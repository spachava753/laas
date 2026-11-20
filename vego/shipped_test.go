package vego

import (
	"bytes"
	"context"
	"errors"
	"fmt"
	"go/importer"
	"go/token"
	"go/types"
	"io"
	"io/fs"
	"log"
	"maps"
	"math"
	"math/big"
	"math/rand"
	"os"
	"path"
	"path/filepath"
	"reflect"
	"slices"
	"sort"
	"strconv"
	"strings"
	"syscall"
	"testing"
	"time"
	"unicode"
	"unicode/utf8"

	"github.com/spachava753/laas/vego/internal/logic"
	"golang.org/x/tools/go/analysis"
)

// sample is one call of a function with a shipped contract: the arguments
// before the call, the same arguments after it, and the results.
type sample struct {
	before  []any
	after   []any
	results []any
	// calls holds, for each function parameter with a contract under calls,
	// the arguments of every call the function made of it, and answers, for
	// one that the contract applies, what it returns for each argument.
	calls   map[string][][]any
	answers map[string]func(int64) int64
	// unwritten holds, where a function the call was handed writes the
	// arguments, what they would be had only that function written them,
	// to the capacity of each slice.
	unwritten []any
}

// table returns a function that answers what a random table says, the
// same for the same argument, and the table as an answer to an
// application. Half the time the table is false and then true, or
// positive, then zero, then negative.
func table[R int | bool](rng *rand.Rand, calls map[string][][]any, name string) (func(int) R, func(int64) int64) {
	values := make([]int64, 12)
	monotone := rng.Intn(2) == 0
	for i := range values {
		values[i] = int64(rng.Intn(3) - 1)
	}
	if monotone {
		slices.Sort(values)
		slices.Reverse(values)
	}
	answer := func(i int64) int64 {
		if i < 0 || i >= int64(len(values)) {
			return 0
		}
		var zero R
		if _, isBool := any(zero).(bool); isBool && monotone {
			// False, then true: true where the sorted value is not positive.
			if values[i] <= 0 {
				return 1
			}
			return 0
		}
		if _, isBool := any(zero).(bool); isBool {
			return values[i] & 1
		}
		return values[i]
	}
	return func(i int) R {
		calls[name] = append(calls[name], []any{i})
		var result R
		switch r := any(&result).(type) {
		case *bool:
			*r = answer(int64(i)) != 0
		case *int:
			*r = int(answer(int64(i)))
		}
		return result
	}, answer
}

// fixedRunes returns a predicate on code points that answers what a random
// table says, the same for the same code point, as FieldsFunc assumes.
func fixedRunes(rng *rand.Rand, calls map[string][][]any) func(rune) bool {
	seed := rng.Int63()
	return func(r rune) bool {
		calls["f"] = append(calls["f"], []any{r})
		return rand.New(rand.NewSource(seed+int64(r))).Intn(2) == 0
	}
}

// recorder returns a function that answers at random and records the
// arguments of each call in calls under name.
func recorder[A, R any](rng *rand.Rand, calls map[string][][]any, name string, answer func(rng *rand.Rand, a A) R) func(A) R {
	return func(a A) R {
		calls[name] = append(calls[name], []any{a})
		return answer(rng, a)
	}
}

// randomBool answers true or false at random, whatever it is asked.
func randomBool[A any](rng *rand.Rand, _ A) bool { return rng.Intn(2) == 0 }

// runeHarness calls a function of package strings that is handed a
// predicate on code points, with one that answers at random.
func runeHarness[R any](call func(s string, f func(rune) bool) R) func(rng *rand.Rand) sample {
	return func(rng *rand.Rand) sample {
		s, calls := randomText(rng), map[string][][]any{}
		f := recorder(rng, calls, "f", randomBool[rune])
		return sample{before: []any{s, f}, results: []any{call(s, f)}, calls: calls}
	}
}

// bytesHarness calls a function of package bytes that is handed a
// predicate on code points, with one that answers at random and, at times,
// writes the slice the function is reading.
func bytesHarness[R any](call func(s []byte, f func(rune) bool) R) func(rng *rand.Rand) sample {
	return func(rng *rand.Rand) sample {
		s, calls := []byte(randomText(rng)), map[string][][]any{}
		before := snapshot(s)
		// What s would hold had only f written it, to its capacity.
		unwritten := make([]byte, len(s), cap(s))
		copy(unwritten[:cap(s)], s[:cap(s)])
		f := recorder(rng, calls, "f", func(rng *rand.Rand, r rune) bool {
			if len(s) > 0 && rng.Intn(4) == 0 {
				at, b := rng.Intn(len(s)), "a\xff "[rng.Intn(3)]
				s[at], unwritten[at] = b, b
			}
			return rng.Intn(2) == 0
		})
		result := call(s, f)
		return sample{before: []any{before[0], f}, after: []any{s, f}, unwritten: []any{unwritten, f}, results: []any{result}, calls: calls}
	}
}

// randomRune answers with what mapping may return: the code point it is
// given, one of another length, an invalid one, or a negative number.
func randomRune(rng *rand.Rand, r rune) rune {
	return []rune{r, 'é', '世', -1, 0x110000, 0xD800}[rng.Intn(6)]
}

// harnesses call each function that vego ships a contract for on random
// arguments. A shipped contract without a harness fails the test, so a new
// contract cannot be added without being exercised against the real function.
var harnesses = map[string]func(rng *rand.Rand) sample{
	"sort.Ints": func(rng *rand.Rand) sample {
		x := randomInts(rng)
		before := slices.Clone(x)
		sort.Ints(x)
		return sample{before: []any{before}, after: []any{x}}
	},
	"sort.IntsAreSorted": func(rng *rand.Rand) sample {
		x := randomInts(rng)
		if rng.Intn(2) == 0 {
			sort.Ints(x)
		}
		before := snapshot(x)
		return sample{before: before, after: []any{x}, results: []any{sort.IntsAreSorted(x)}}
	},
	"sort.SearchInts": func(rng *rand.Rand) sample {
		a, x := randomInts(rng), rng.Intn(9)-4
		sort.Ints(a)
		before := snapshot(a, x)
		return sample{before: before, after: []any{a, x}, results: []any{sort.SearchInts(a, x)}}
	},
	"math/rand.Intn": func(rng *rand.Rand) sample {
		n := rng.Intn(50) + 1
		return sample{before: []any{n}, results: []any{rand.Intn(n)}}
	},
	"math/rand.Int": func(*rand.Rand) sample {
		return sample{results: []any{rand.Int()}}
	},
	"strings.Contains": func(rng *rand.Rand) sample {
		s, substr := randomText(rng), randomText(rng)
		return sample{before: []any{s, substr}, results: []any{strings.Contains(s, substr)}}
	},
	"strings.HasPrefix": func(rng *rand.Rand) sample {
		s := randomText(rng)
		prefix := []string{randomText(rng), s[:rng.Intn(len(s)+1)]}[rng.Intn(2)]
		return sample{before: []any{s, prefix}, results: []any{strings.HasPrefix(s, prefix)}}
	},
	"strings.HasSuffix": func(rng *rand.Rand) sample {
		s := randomText(rng)
		suffix := []string{randomText(rng), s[rng.Intn(len(s)+1):]}[rng.Intn(2)]
		return sample{before: []any{s, suffix}, results: []any{strings.HasSuffix(s, suffix)}}
	},
	"strings.Index": func(rng *rand.Rand) sample {
		s, substr := randomText(rng), randomText(rng)
		if rng.Intn(2) == 0 && len(s) > 0 {
			start := rng.Intn(len(s))
			substr = s[start : start+rng.Intn(len(s)-start+1)]
		}
		return sample{before: []any{s, substr}, results: []any{strings.Index(s, substr)}}
	},
	"strings.TrimSpace": func(rng *rand.Rand) sample {
		s := randomText(rng)
		return sample{before: []any{s}, results: []any{strings.TrimSpace(s)}}
	},
	"strings.Repeat": func(rng *rand.Rand) sample {
		s, count := randomText(rng), rng.Intn(4)
		return sample{before: []any{s, count}, results: []any{strings.Repeat(s, count)}}
	},
	"strings.ToUpper": func(rng *rand.Rand) sample {
		s := randomText(rng)
		return sample{before: []any{s}, results: []any{strings.ToUpper(s)}}
	},
	"strings.ToLower": func(rng *rand.Rand) sample {
		s := randomText(rng)
		return sample{before: []any{s}, results: []any{strings.ToLower(s)}}
	},
	"strconv.Itoa": func(rng *rand.Rand) sample {
		i := rng.Intn(2001) - 1000
		return sample{before: []any{i}, results: []any{strconv.Itoa(i)}}
	},
	"strconv.Atoi": func(rng *rand.Rand) sample {
		big := strings.Repeat("9", 19+rng.Intn(3))
		s := []string{randomText(rng), strconv.Itoa(rng.Intn(100)), big, "-" + big, "+" + big}[rng.Intn(5)]
		n, err := strconv.Atoi(s)
		return sample{before: []any{s}, results: []any{n, err}}
	},
	"fmt.Sprintf": func(rng *rand.Rand) sample {
		format, a := randomFormat(rng), randomOperands(rng)
		before := snapshot(format, a)
		return sample{before: before, after: []any{format, a}, results: []any{fmt.Sprintf(format, a...)}}
	},
	"fmt.Sprint": func(rng *rand.Rand) sample {
		a := randomOperands(rng)
		before := snapshot(a)
		return sample{before: before, after: []any{a}, results: []any{fmt.Sprint(a...)}}
	},
	"fmt.Sprintln": func(rng *rand.Rand) sample {
		a := randomOperands(rng)
		before := snapshot(a)
		return sample{before: before, after: []any{a}, results: []any{fmt.Sprintln(a...)}}
	},
	"fmt.Printf": func(rng *rand.Rand) sample {
		format, a := randomFormat(rng), randomOperands(rng)
		var n int
		var err error
		toScratch(func() { n, err = fmt.Printf(format, a...) })
		before := snapshot(format, a)
		return sample{before: before, after: []any{format, a}, results: []any{n, err}}
	},
	"fmt.Print": func(rng *rand.Rand) sample {
		a := randomOperands(rng)
		var n int
		var err error
		toScratch(func() { n, err = fmt.Print(a...) })
		before := snapshot(a)
		return sample{before: before, after: []any{a}, results: []any{n, err}}
	},
	"fmt.Println": func(rng *rand.Rand) sample {
		a := randomOperands(rng)
		var n int
		var err error
		toScratch(func() { n, err = fmt.Println(a...) })
		before := snapshot(a)
		return sample{before: before, after: []any{a}, results: []any{n, err}}
	},
	"fmt.Fprintf": func(rng *rand.Rand) sample {
		format, a := randomFormat(rng), randomOperands(rng)
		var n int
		var err error
		w := keptFormatting(rng, func(w io.Writer) { n, err = fmt.Fprintf(w, format, a...) })
		before := snapshot(w, format, a)
		return sample{before: before, after: []any{w, format, a}, results: []any{n, err}}
	},
	"fmt.Fprint": func(rng *rand.Rand) sample {
		a := randomOperands(rng)
		var n int
		var err error
		w := keptFormatting(rng, func(w io.Writer) { n, err = fmt.Fprint(w, a...) })
		before := snapshot(w, a)
		return sample{before: before, after: []any{w, a}, results: []any{n, err}}
	},
	"fmt.Fprintln": func(rng *rand.Rand) sample {
		a := randomOperands(rng)
		var n int
		var err error
		w := keptFormatting(rng, func(w io.Writer) { n, err = fmt.Fprintln(w, a...) })
		before := snapshot(w, a)
		return sample{before: before, after: []any{w, a}, results: []any{n, err}}
	},
	"log.Printf": func(rng *rand.Rand) sample {
		format, v := randomFormat(rng), randomOperands(rng)
		toLogBuffer(func() { log.Printf(format, v...) })
		before := snapshot(format, v)
		return sample{before: before, after: []any{format, v}}
	},
	"log.Print": func(rng *rand.Rand) sample {
		v := randomOperands(rng)
		toLogBuffer(func() { log.Print(v...) })
		before := snapshot(v)
		return sample{before: before, after: []any{v}}
	},
	"log.Println": func(rng *rand.Rand) sample {
		v := randomOperands(rng)
		toLogBuffer(func() { log.Println(v...) })
		before := snapshot(v)
		return sample{before: before, after: []any{v}}
	},
	"path.Join": func(rng *rand.Rand) sample {
		elem := randomElements(rng)
		before := snapshot(elem)
		return sample{before: before, after: []any{elem}, results: []any{path.Join(elem...)}}
	},
	"path/filepath.Join": func(rng *rand.Rand) sample {
		elem := randomElements(rng)
		before := snapshot(elem)
		return sample{before: before, after: []any{elem}, results: []any{filepath.Join(elem...)}}
	},
	"os.IsExist":      osPredicate(os.IsExist, false),
	"os.IsNotExist":   osPredicate(os.IsNotExist, false),
	"os.IsPermission": osPredicate(os.IsPermission, false),
	"os.IsTimeout":    osPredicate(os.IsTimeout, true),
	"os.Remove": func(rng *rand.Rand) sample {
		// Only inside a directory of its own, made for each call: a file,
		// a missing name, a directory that is not empty, a path through a
		// file, and a name with a NUL byte in it.
		dir, err := os.MkdirTemp(scratch, "remove")
		if err != nil {
			panic(err)
		}
		file := filepath.Join(dir, "file")
		if err := os.WriteFile(file, nil, 0o600); err != nil {
			panic(err)
		}
		full := filepath.Join(dir, "full")
		if err := os.Mkdir(full, 0o700); err != nil {
			panic(err)
		}
		if err := os.WriteFile(filepath.Join(full, "inside"), nil, 0o600); err != nil {
			panic(err)
		}
		name := []string{file, filepath.Join(dir, "missing"), full, filepath.Join(file, "below"), filepath.Join(dir, "a\x00b")}[rng.Intn(5)]
		return sample{before: []any{name}, results: []any{os.Remove(name)}}
	},
	"sort.Search": func(rng *rand.Rand) sample {
		n, calls := rng.Intn(14)-2, map[string][][]any{}
		f, answers := table[bool](rng, calls, "f")
		return sample{before: []any{n, f}, results: []any{sort.Search(n, f)}, calls: calls, answers: map[string]func(int64) int64{"f": answers}}
	},
	"sort.Find": func(rng *rand.Rand) sample {
		n, calls := rng.Intn(14)-2, map[string][][]any{}
		cmp, answers := table[int](rng, calls, "cmp")
		i, found := sort.Find(n, cmp)
		return sample{before: []any{n, cmp}, results: []any{i, found}, calls: calls, answers: map[string]func(int64) int64{"cmp": answers}}
	},
	"strings.FieldsFunc": func(rng *rand.Rand) sample {
		s, calls := randomText(rng), map[string][][]any{}
		f := fixedRunes(rng, calls)
		return sample{before: []any{s, f}, results: []any{strings.FieldsFunc(s, f)}, calls: calls}
	},
	"bytes.FieldsFunc": func(rng *rand.Rand) sample {
		s, calls := []byte(randomText(rng)), map[string][][]any{}
		f := fixedRunes(rng, calls)
		before := snapshot(s, f)
		return sample{before: before, after: []any{s, f}, results: []any{bytes.FieldsFunc(s, f)}, calls: calls}
	},
	"strings.IndexFunc":     runeHarness(strings.IndexFunc),
	"strings.LastIndexFunc": runeHarness(strings.LastIndexFunc),
	"strings.ContainsFunc":  runeHarness(strings.ContainsFunc),
	"strings.TrimFunc":      runeHarness(strings.TrimFunc),
	"strings.TrimLeftFunc":  runeHarness(strings.TrimLeftFunc),
	"strings.TrimRightFunc": runeHarness(strings.TrimRightFunc),
	"strings.Map": func(rng *rand.Rand) sample {
		s, calls := randomText(rng), map[string][][]any{}
		mapping := recorder(rng, calls, "mapping", randomRune)
		return sample{before: []any{mapping, s}, results: []any{strings.Map(mapping, s)}, calls: calls}
	},
	"bytes.IndexFunc":     bytesHarness(bytes.IndexFunc),
	"bytes.LastIndexFunc": bytesHarness(bytes.LastIndexFunc),
	"bytes.ContainsFunc":  bytesHarness(bytes.ContainsFunc),
	"bytes.TrimFunc":      bytesHarness(bytes.TrimFunc),
	"bytes.TrimLeftFunc":  bytesHarness(bytes.TrimLeftFunc),
	"bytes.TrimRightFunc": bytesHarness(bytes.TrimRightFunc),
	"bytes.Map": func(rng *rand.Rand) sample {
		s, calls := []byte(randomText(rng)), map[string][][]any{}
		mapping := recorder(rng, calls, "mapping", randomRune)
		before := snapshot(mapping, s)
		return sample{before: before, after: []any{mapping, s}, results: []any{bytes.Map(mapping, s)}, calls: calls}
	},
	"strings.IndexByte": func(rng *rand.Rand) sample {
		s, c := randomText(rng), randomByte(rng)
		return sample{before: []any{s, c}, results: []any{strings.IndexByte(s, c)}}
	},
	"strings.LastIndexByte": func(rng *rand.Rand) sample {
		s, c := randomText(rng), randomByte(rng)
		return sample{before: []any{s, c}, results: []any{strings.LastIndexByte(s, c)}}
	},
	"strings.LastIndex":  textHarness(func(s, t string) []any { return []any{strings.LastIndex(s, t)} }),
	"strings.Cut":        textHarness(func(s, t string) []any { before, after, found := strings.Cut(s, t); return []any{before, after, found} }),
	"strings.TrimPrefix": textHarness(func(s, t string) []any { return []any{strings.TrimPrefix(s, t)} }),
	"strings.TrimSuffix": textHarness(func(s, t string) []any { return []any{strings.TrimSuffix(s, t)} }),
	"strings.Split":      textHarness(func(s, t string) []any { return []any{strings.Split(s, t)} }),
	"strings.EqualFold": func(rng *rand.Rand) sample {
		s, t := foldPair(rng)
		return sample{before: []any{s, t}, results: []any{strings.EqualFold(s, t)}}
	},
	"strings.Count": textHarness(func(s, t string) []any { return []any{strings.Count(s, t)} }),
	"strings.Fields": func(rng *rand.Rand) sample {
		s := randomText(rng)
		return sample{before: []any{s}, results: []any{strings.Fields(s)}}
	},
	"strings.Join": func(rng *rand.Rand) sample {
		elems, sep := randomElements(rng), []string{"", ",", ", ", randomText(rng)}[rng.Intn(4)]
		before := snapshot(elems, sep)
		return sample{before: before, after: []any{elems, sep}, results: []any{strings.Join(elems, sep)}}
	},
	"strings.Replace": func(rng *rand.Rand) sample {
		s, old := randomPair(rng)
		replacement, n := randomReplacement(rng, old), rng.Intn(5)-2
		return sample{before: []any{s, old, replacement, n}, results: []any{strings.Replace(s, old, replacement, n)}}
	},
	"strings.ReplaceAll": func(rng *rand.Rand) sample {
		s, old := randomPair(rng)
		replacement := randomReplacement(rng, old)
		return sample{before: []any{s, old, replacement}, results: []any{strings.ReplaceAll(s, old, replacement)}}
	},
	"bytes.IndexByte": func(rng *rand.Rand) sample {
		b, c := []byte(randomText(rng)), randomByte(rng)
		before := snapshot(b, c)
		return sample{before: before, after: []any{b, c}, results: []any{bytes.IndexByte(b, c)}}
	},
	"bytes.LastIndexByte": func(rng *rand.Rand) sample {
		b, c := []byte(randomText(rng)), randomByte(rng)
		before := snapshot(b, c)
		return sample{before: before, after: []any{b, c}, results: []any{bytes.LastIndexByte(b, c)}}
	},
	"bytes.Index":     bytesPairHarness(func(s, t []byte) []any { return []any{bytes.Index(s, t)} }),
	"bytes.LastIndex": bytesPairHarness(func(s, t []byte) []any { return []any{bytes.LastIndex(s, t)} }),
	"bytes.Contains":  bytesPairHarness(func(s, t []byte) []any { return []any{bytes.Contains(s, t)} }),
	"bytes.HasPrefix": bytesPairHarness(func(s, t []byte) []any { return []any{bytes.HasPrefix(s, t)} }),
	"bytes.HasSuffix": bytesPairHarness(func(s, t []byte) []any { return []any{bytes.HasSuffix(s, t)} }),
	"bytes.Equal":     bytesPairHarness(func(s, t []byte) []any { return []any{bytes.Equal(s, t)} }),
	"bytes.Count":     bytesPairHarness(func(s, t []byte) []any { return []any{bytes.Count(s, t)} }),
	"bytes.EqualFold": func(rng *rand.Rand) sample {
		text, other := foldPair(rng)
		s, t := []byte(text), []byte(other)
		before := snapshot(s, t)
		return sample{before: before, after: []any{s, t}, results: []any{bytes.EqualFold(s, t)}}
	},
	"bytes.Cut": bytesPairHarness(func(s, t []byte) []any {
		before, after, found := bytes.Cut(s, t)
		return []any{before, after, found}
	}),
	"bytes.TrimPrefix": bytesPairHarness(func(s, t []byte) []any { return []any{bytes.TrimPrefix(s, t)} }),
	"bytes.TrimSuffix": bytesPairHarness(func(s, t []byte) []any { return []any{bytes.TrimSuffix(s, t)} }),
	"bytes.TrimSpace": func(rng *rand.Rand) sample {
		s := []byte(randomText(rng))
		before := snapshot(s)
		return sample{before: before, after: []any{s}, results: []any{bytes.TrimSpace(s)}}
	},
	"bytes.Repeat": func(rng *rand.Rand) sample {
		b, count := []byte(randomText(rng)), rng.Intn(4)
		before := snapshot(b, count)
		return sample{before: before, after: []any{b, count}, results: []any{bytes.Repeat(b, count)}}
	},
	"bytes.Join": func(rng *rand.Rand) sample {
		var s [][]byte
		for _, elem := range randomElements(rng) {
			s = append(s, []byte(elem))
		}
		sep := []byte([]string{"", ",", ", ", randomText(rng)}[rng.Intn(4)])
		before := snapshot(s, sep)
		return sample{before: before, after: []any{s, sep}, results: []any{bytes.Join(s, sep)}}
	},
	"bytes.Replace": func(rng *rand.Rand) sample {
		text, oldText := randomPair(rng)
		s, old, replacement, n := []byte(text), []byte(oldText), []byte(randomReplacement(rng, oldText)), rng.Intn(5)-2
		before := snapshot(s, old, replacement, n)
		return sample{before: before, after: []any{s, old, replacement, n}, results: []any{bytes.Replace(s, old, replacement, n)}}
	},
	"bytes.ReplaceAll": func(rng *rand.Rand) sample {
		text, oldText := randomPair(rng)
		s, old, replacement := []byte(text), []byte(oldText), []byte(randomReplacement(rng, oldText))
		before := snapshot(s, old, replacement)
		return sample{before: before, after: []any{s, old, replacement}, results: []any{bytes.ReplaceAll(s, old, replacement)}}
	},
	"unicode/utf8.DecodeRuneInString": func(rng *rand.Rand) sample {
		s := utf8Text(rng)
		r, size := utf8.DecodeRuneInString(s)
		return sample{before: []any{s}, results: []any{r, size}}
	},
	"unicode/utf8.DecodeRune": func(rng *rand.Rand) sample {
		p := []byte(utf8Text(rng))
		before := snapshot(p)
		r, size := utf8.DecodeRune(p)
		return sample{before: before, after: []any{p}, results: []any{r, size}}
	},
	"unicode/utf8.AppendRune": func(rng *rand.Rand) sample {
		p, r := roomyBytes(rng), randomCodePoint(rng)
		before := snapshot(p, r)
		return sample{before: before, after: []any{p, r}, results: []any{utf8.AppendRune(p, r)}}
	},
	"unicode/utf8.RuneLen": func(rng *rand.Rand) sample {
		r := randomCodePoint(rng)
		return sample{before: []any{r}, results: []any{utf8.RuneLen(r)}}
	},
	"unicode/utf8.ValidString": func(rng *rand.Rand) sample {
		s := utf8Text(rng)
		return sample{before: []any{s}, results: []any{utf8.ValidString(s)}}
	},
	"unicode.IsSpace":  runePredicate(unicode.IsSpace),
	"unicode.IsDigit":  runePredicate(unicode.IsDigit),
	"unicode.IsLetter": runePredicate(unicode.IsLetter),
	"unicode.IsUpper":  runePredicate(unicode.IsUpper),
	"unicode.IsLower":  runePredicate(unicode.IsLower),
	"strconv.Quote": func(rng *rand.Rand) sample {
		s := utf8Text(rng) + []string{"", "\x01", "\n", "\"", "\\", "\u0085", "\U0001F600", "\u00ff"}[rng.Intn(8)]
		return sample{before: []any{s}, results: []any{strconv.Quote(s)}}
	},
	"strconv.Unquote": func(rng *rand.Rand) sample {
		s := randomLiteral(rng)
		value, err := strconv.Unquote(s)
		return sample{before: []any{s}, results: []any{value, err}}
	},
	"strconv.ParseInt": numeralHarness(func(s string, base, bitSize int) []any {
		i, err := strconv.ParseInt(s, base, bitSize)
		return []any{i, err}
	}),
	"strconv.ParseUint": numeralHarness(func(s string, base, bitSize int) []any {
		u, err := strconv.ParseUint(s, base, bitSize)
		return []any{u, err}
	}),
	"strconv.ParseBool": func(rng *rand.Rand) sample {
		str := []string{"1", "t", "T", "TRUE", "true", "True", "0", "f", "F", "FALSE", "false", "False", "", "yes", "tRUE", "2", " true", randomText(rng)}[rng.Intn(18)]
		value, err := strconv.ParseBool(str)
		return sample{before: []any{str}, results: []any{value, err}}
	},
	"strconv.FormatInt": func(rng *rand.Rand) sample {
		i, base := randomInt64(rng), []int{2, 10, 10, 16, 36, rng.Intn(40)}[rng.Intn(6)]
		if base < 2 || base > 36 {
			return sample{before: []any{i, base}}
		}
		return sample{before: []any{i, base}, results: []any{strconv.FormatInt(i, base)}}
	},
	"strconv.AppendInt": func(rng *rand.Rand) sample {
		dst, i, base := roomyBytes(rng), randomInt64(rng), []int{2, 10, 10, 16, 36, rng.Intn(40)}[rng.Intn(6)]
		before := snapshot(dst, i, base)
		if base < 2 || base > 36 {
			return sample{before: before, after: []any{dst, i, base}}
		}
		return sample{before: before, after: []any{dst, i, base}, results: []any{strconv.AppendInt(dst, i, base)}}
	},
	"sort.Strings": func(rng *rand.Rand) sample {
		x := randomElements(rng)
		before := snapshot(x)
		sort.Strings(x)
		return sample{before: before, after: []any{x}}
	},
	"math.Sqrt":  floatHarness(math.Sqrt),
	"math.Abs":   floatHarness(math.Abs),
	"math.Floor": floatHarness(math.Floor),
	"math.Ceil":  floatHarness(math.Ceil),
	"math.Trunc": floatHarness(math.Trunc),
	"math.Round": floatHarness(math.Round),
	"math.Log":   floatHarness(math.Log),
	"math.Exp":   floatHarness(math.Exp),
	"math.Min":   floatPairHarness(math.Min),
	"math.Max":   floatPairHarness(math.Max),
	"math.Pow":   floatPairHarness(math.Pow),
	"math.Mod":   floatPairHarness(math.Mod),
	"math.Inf": func(rng *rand.Rand) sample {
		sign := rng.Intn(5) - 2
		return sample{before: []any{sign}, results: []any{math.Inf(sign)}}
	},
	"math.NaN": func(*rand.Rand) sample {
		return sample{results: []any{math.NaN()}}
	},
	"math.IsNaN": func(rng *rand.Rand) sample {
		f := randomFloat(rng)
		return sample{before: []any{f}, results: []any{math.IsNaN(f)}}
	},
	"math.IsInf": func(rng *rand.Rand) sample {
		f, sign := randomFloat(rng), rng.Intn(5)-2
		return sample{before: []any{f, sign}, results: []any{math.IsInf(f, sign)}}
	},
	"(time.Time).Date": func(rng *rand.Rand) sample {
		t := randomTime(rng)
		before := snapshot(t)
		year, month, day := t.Date()
		return sample{before: before, after: []any{t}, results: []any{year, month, day}}
	},
	"(time.Time).Year":             timeHarness(time.Time.Year),
	"(time.Time).Month":            timeHarness(time.Time.Month),
	"(time.Time).Day":              timeHarness(time.Time.Day),
	"(time.Time).Hour":             timeHarness(time.Time.Hour),
	"(time.Time).Minute":           timeHarness(time.Time.Minute),
	"(time.Time).Second":           timeHarness(time.Time.Second),
	"(time.Time).Nanosecond":       timeHarness(time.Time.Nanosecond),
	"(time.Time).Weekday":          timeHarness(time.Time.Weekday),
	"(time.Time).YearDay":          timeHarness(time.Time.YearDay),
	"(time.Time).Unix":             timeHarness(time.Time.Unix),
	"(time.Time).UnixMilli":        timeHarness(time.Time.UnixMilli),
	"(time.Time).IsZero":           timeHarness(time.Time.IsZero),
	"(time.Time).Sub":              timePairHarness(time.Time.Sub),
	"(time.Time).Before":           timePairHarness(time.Time.Before),
	"(time.Time).After":            timePairHarness(time.Time.After),
	"(time.Time).Equal":            timePairHarness(time.Time.Equal),
	"time.Since":                   timeHarness(time.Since),
	"time.Until":                   timeHarness(time.Until),
	"time.Now":                     func(*rand.Rand) sample { return sample{results: []any{time.Now()}} },
	"(time.Duration).Seconds":      durationHarness(time.Duration.Seconds),
	"(time.Duration).Milliseconds": durationHarness(time.Duration.Milliseconds),
	"(time.Duration).Nanoseconds":  durationHarness(time.Duration.Nanoseconds),
	"(time.Time).Add": func(rng *rand.Rand) sample {
		t, d := randomTime(rng), randomDuration(rng)
		before := snapshot(t, d)
		return sample{before: before, after: []any{t, d}, results: []any{t.Add(d)}}
	},
	"(time.Time).AddDate": func(rng *rand.Rand) sample {
		t, years, months, days := randomTime(rng), randomCalendarInt(rng), randomCalendarInt(rng), randomCalendarInt(rng)
		before := snapshot(t, years, months, days)
		return sample{before: before, after: []any{t, years, months, days}, results: []any{t.AddDate(years, months, days)}}
	},
	"time.Unix": func(rng *rand.Rand) sample {
		sec, nsec := randomInt64(rng), randomInt64(rng)
		return sample{before: []any{sec, nsec}, results: []any{time.Unix(sec, nsec)}}
	},
	"time.Date": func(rng *rand.Rand) sample {
		year, month, day := randomCalendarInt(rng), time.Month(randomCalendarInt(rng)), randomCalendarInt(rng)
		hour, minute, sec, nsec := randomCalendarInt(rng), randomCalendarInt(rng), randomCalendarInt(rng), randomCalendarInt(rng)
		loc := randomLocation(rng)
		if rng.Intn(8) == 0 {
			return sample{before: []any{year, month, day, hour, minute, sec, nsec, (*time.Location)(nil)}}
		}
		before := snapshot(year, month, day, hour, minute, sec, nsec, loc)
		return sample{before: before, after: []any{year, month, day, hour, minute, sec, nsec, loc}, results: []any{time.Date(year, month, day, hour, minute, sec, nsec, loc)}}
	},
	"unicode/utf8.RuneCountInString": func(rng *rand.Rand) sample {
		s := randomText(rng)
		return sample{before: []any{s}, results: []any{utf8.RuneCountInString(s)}}
	},
}

// utf8Text returns text whose bytes are each kind UTF-8 has: ASCII, valid
// encodings of two, three, and four bytes, U+FFFD itself, and invalid
// ones: a lone continuation byte, an overlong encoding, an encoded
// surrogate, one past MaxRune, a truncated encoding, and 0xC0, 0xC1, and
// 0xF5 to 0xFF.
func utf8Text(rng *rand.Rand) string {
	pieces := []string{"a", " ", "\x7f", "é", "世", "\U0001F600", "\U0010FFFF", "\uFFFD", "\x80", "\xc0\x80", "\xc1\xbf",
		"\xed\xa0\x80", "\xf4\x90\x80\x80", "\xe4\xb8", "\xf5", "\xff", "\u0085", "\u00a0"}
	var text strings.Builder
	for range rng.Intn(5) {
		text.WriteString(pieces[rng.Intn(len(pieces))])
	}
	return text.String()
}

// roomyBytes returns random text as a slice that has spare capacity half
// the time, so that an append writes in place or into new memory.
func roomyBytes(rng *rand.Rand) []byte {
	text := randomText(rng)
	p := make([]byte, len(text), len(text)+rng.Intn(2)*rng.Intn(70))
	copy(p, text)
	return p
}

// randomCodePoint returns a value of a rune at the edges of what UTF-8
// encodes, or at random.
func randomCodePoint(rng *rand.Rand) rune {
	edges := []rune{-1 << 31, -2, -1, 0, 0x7f, 0x80, 0x7ff, 0x800, 0xd7ff, 0xd800, 0xdfff, 0xe000, 0xfffd, 0xffff, 0x10000, 0x10ffff, 0x110000, 1<<31 - 1}
	if rng.Intn(2) == 0 {
		return edges[rng.Intn(len(edges))]
	}
	return rune(rng.Intn(0x110010)) - 8
}

// runePredicate returns a harness that calls a predicate of package unicode
// on every value from -2 to 300 in turn, and then on random code points.
func runePredicate(predicate func(rune) bool) func(rng *rand.Rand) sample {
	next := rune(-2)
	return func(rng *rand.Rand) sample {
		r := next
		if next <= 300 {
			next++
		} else {
			r = randomCodePoint(rng)
		}
		return sample{before: []any{r}, results: []any{predicate(r)}}
	}
}

// randomLiteral returns a quoted literal of each form, with escapes,
// invalid bytes, and carriage returns, or text that is no literal.
func randomLiteral(rng *rand.Rand) string {
	body := utf8Text(rng) + []string{"", "\\n", "\\x41", "\\u00e9", "\\U0001F600", "\\'", "\\q", "\r"}[rng.Intn(8)]
	switch rng.Intn(6) {
	case 0:
		return "`" + body + "`"
	case 1:
		return "'" + body + "'"
	case 2:
		return []string{"", "\"", "'", "`", "\"\"x", "'ab'", "''"}[rng.Intn(7)]
	case 3:
		return strconv.Quote(body)
	}
	return "\"" + body + "\""
}

// numeralEdges are the edges of each bit size, signed and unsigned, and a
// number past each by one.
var numeralEdges = []string{"-128", "127", "-129", "128", "255", "256", "-32768", "32767", "-32769", "32768", "65535", "65536",
	"-2147483648", "2147483647", "-2147483649", "2147483648", "4294967295", "4294967296",
	"-9223372036854775808", "9223372036854775807", "-9223372036854775809", "9223372036854775808",
	"18446744073709551615", "18446744073709551616"}

// numeralHarness returns a harness for ParseInt or ParseUint that parses
// each edge in base 10 at each bit size the documentation names in turn,
// and then random numerals in random bases and bit sizes.
func numeralHarness(parse func(s string, base, bitSize int) []any) func(rng *rand.Rand) sample {
	next := 0
	return func(rng *rand.Rand) sample {
		// Digits of each base, with signs, prefixes, and underscores,
		// numbers past every bit size, and text that is no number, in a
		// base that ParseInt accepts, mostly 10, or one it does not, and a
		// bit size it names, mostly, or another.
		sign := []string{"", "", "-", "+"}[rng.Intn(4)]
		digits := []string{"0", "7", "127", "128", "255", "256", "32767", "32768", "65535", "65536", "2147483647", "2147483648",
			"4294967295", "4294967296", "9223372036854775807", "9223372036854775808", "18446744073709551615", "18446744073709551616",
			"99999999999999999999999", "0x7f", "0b101", "0o17", "017", "1_000", "z", "ff", ""}[rng.Intn(27)]
		s, base, bitSize := sign+digits, []int{10, 10, 10, 0, 0, 2, 8, 16, 36, 1, 37, -1}[rng.Intn(12)], []int{0, 8, 16, 32, 64, 0, 8, 16, 32, 64, 7, -1, 65}[rng.Intn(13)]
		if next < 5*len(numeralEdges) {
			s, base, bitSize = numeralEdges[next/5], 10, []int{0, 8, 16, 32, 64}[next%5]
			next++
		}
		return sample{before: []any{s, base, bitSize}, results: parse(s, base, bitSize)}
	}
}

// randomInt64 returns an int64 at an edge or at random.
func randomInt64(rng *rand.Rand) int64 {
	edges := []int64{math.MinInt64, math.MinInt64 + 1, -1, 0, 1, 9, 10, 35, 36, math.MaxInt64}
	if rng.Intn(2) == 0 {
		return edges[rng.Intn(len(edges))]
	}
	return int64(rng.Uint64())
}

// randomFloat returns a float at an edge or at random.
func randomFloat(rng *rand.Rand) float64 {
	edges := []float64{0, math.Copysign(0, -1), 1, -1, 0.5, -2.5, math.Inf(1), math.Inf(-1), math.NaN(), math.MaxFloat64, math.SmallestNonzeroFloat64}
	if rng.Intn(2) == 0 {
		return edges[rng.Intn(len(edges))]
	}
	return math.Float64frombits(rng.Uint64())
}

// floatHarness calls a function of package math of one float.
func floatHarness(f func(float64) float64) func(rng *rand.Rand) sample {
	return func(rng *rand.Rand) sample {
		x := randomFloat(rng)
		return sample{before: []any{x}, results: []any{f(x)}}
	}
}

// floatPairHarness calls a function of package math of two floats.
func floatPairHarness(f func(float64, float64) float64) func(rng *rand.Rand) sample {
	return func(rng *rand.Rand) sample {
		x, y := randomFloat(rng), randomFloat(rng)
		return sample{before: []any{x, y}, results: []any{f(x, y)}}
	}
}

// randomLocation returns UTC, Local, a zone loaded from the system's
// database, or a fixed zone at an edge of its offset.
func randomLocation(rng *rand.Rand) *time.Location {
	switch rng.Intn(5) {
	case 0:
		return time.UTC
	case 1:
		return time.Local
	case 2:
		if loc, err := time.LoadLocation("America/New_York"); err == nil {
			return loc
		}
		return time.UTC
	}
	return time.FixedZone("edge", []int{math.MinInt32, math.MaxInt32, -1, 0, 3600 * 14}[rng.Intn(5)])
}

// randomCalendarInt returns a field of a date at an edge, outside its
// usual range, or at random.
func randomCalendarInt(rng *rand.Rand) int {
	edges := []int{math.MinInt, math.MinInt / 2, -1 << 40, -400, -1, 0, 1, 12, 13, 28, 31, 32, 59, 60, 366, 1e9, 1 << 40, math.MaxInt / 2, math.MaxInt}
	if rng.Intn(2) == 0 {
		return edges[rng.Intn(len(edges))]
	}
	return rng.Intn(4000) - 2000
}

// randomDuration returns a duration at an edge or at random.
func randomDuration(rng *rand.Rand) time.Duration {
	return time.Duration(randomInt64(rng))
}

// randomTime returns the zero Time, the time now, a time from time.Unix
// over all of int64 or from time.Date with fields outside their ranges,
// in a random location.
func randomTime(rng *rand.Rand) time.Time {
	loc := randomLocation(rng)
	switch rng.Intn(6) {
	case 0:
		return time.Time{}
	case 5:
		// The last instant of a year, leap or not, and of a month of 31
		// days, in a zone that may move it to another day.
		year := []int{2024, 2023, 2000, 1900, 1, 0, -4}[rng.Intn(7)]
		return time.Date(year, time.Month([]int{12, 1, 2, 3}[rng.Intn(4)]), []int{31, 29, 28, 1}[rng.Intn(4)], 23, 59, 59, 999999999, loc)
	case 1:
		return time.Now().In(loc)
	case 2:
		return time.Date(randomCalendarInt(rng), time.Month(randomCalendarInt(rng)), randomCalendarInt(rng),
			randomCalendarInt(rng), randomCalendarInt(rng), randomCalendarInt(rng), randomCalendarInt(rng), loc)
	}
	return time.Unix(randomInt64(rng), randomInt64(rng)).In(loc)
}

// timeHarness calls a method of time.Time that takes nothing.
func timeHarness[R any](method func(time.Time) R) func(rng *rand.Rand) sample {
	return func(rng *rand.Rand) sample {
		t := randomTime(rng)
		before := snapshot(t)
		return sample{before: before, after: []any{t}, results: []any{method(t)}}
	}
}

// timePairHarness calls a method of time.Time that takes another time.
func timePairHarness[R any](method func(time.Time, time.Time) R) func(rng *rand.Rand) sample {
	return func(rng *rand.Rand) sample {
		t, u := randomTime(rng), randomTime(rng)
		if rng.Intn(4) == 0 {
			u = t
		}
		before := snapshot(t, u)
		return sample{before: before, after: []any{t, u}, results: []any{method(t, u)}}
	}
}

// durationHarness calls a method of time.Duration.
func durationHarness[R any](method func(time.Duration) R) func(rng *rand.Rand) sample {
	return func(rng *rand.Rand) sample {
		d := randomDuration(rng)
		return sample{before: []any{d}, results: []any{method(d)}}
	}
}

// randomByte returns a byte that random text holds at times: a letter, a
// space, the lead byte of a multi-byte character, or an invalid one.
func randomByte(rng *rand.Rand) byte {
	return "aB \t\xc3\xe4\xff,"[rng.Intn(8)]
}

// randomPair returns a text and a second one that is, at random, a piece,
// a prefix, or a suffix of it, the text itself, empty, other text, or
// longer than it.
func randomPair(rng *rand.Rand) (string, string) {
	s := randomText(rng)
	i := rng.Intn(len(s) + 1)
	j := i + rng.Intn(len(s)-i+1)
	return s, []string{s[i:j], s[:j], s[i:], s, "", randomText(rng), s + "a"}[rng.Intn(7)]
}

// randomReplacement returns what a replacement puts in place of old: old
// itself, nothing, or other text.
func randomReplacement(rng *rand.Rand, old string) string {
	return []string{old, "", "x", randomText(rng)}[rng.Intn(4)]
}

// foldPair returns a text and one that is, at random, the same, the same
// in another case, with the Kelvin sign that folds to k, or another pair.
func foldPair(rng *rand.Rand) (string, string) {
	s, t := randomPair(rng)
	switch rng.Intn(4) {
	case 0:
		t = strings.ToUpper(s)
	case 1:
		t = strings.ToLower(s)
	case 2:
		s, t = s+"k", s+"\u212a"
	}
	return s, t
}

// textHarness calls a function of package strings on a pair of texts.
func textHarness(call func(s, t string) []any) func(rng *rand.Rand) sample {
	return func(rng *rand.Rand) sample {
		s, t := randomPair(rng)
		return sample{before: []any{s, t}, results: call(s, t)}
	}
}

// bytesPairHarness calls a function of package bytes on a pair of slices
// that share no memory, as verified code passes them.
func bytesPairHarness(call func(s, t []byte) []any) func(rng *rand.Rand) sample {
	return func(rng *rand.Rand) sample {
		text, other := randomPair(rng)
		s, t := []byte(text), []byte(other)
		before := snapshot(s, t)
		return sample{before: before, after: []any{s, t}, results: call(s, t)}
	}
}

// snapped is an argument as a harness saw it before a call: a copy that
// the formulas read, and a print of all the memory it reaches, which the
// check of what an entry's modifies leaves out compares with the print of
// the argument after the call.
type snapped struct {
	value any
	print string
	// codePrint is the print with every interface value and function
	// value inside left opaque, which is what a parameter under runs is
	// compared by: what its code writes is that code's own.
	codePrint string
}

// snapshot returns the arguments of a call as they are before it: each a
// copy, of the elements of a slice up to its length and of the entries of
// a map, with a print of everything it reaches.
func snapshot(args ...any) []any {
	before := make([]any, len(args))
	for i, arg := range args {
		value := arg
		switch v := reflect.ValueOf(arg); {
		case v.Kind() == reflect.Slice && !v.IsNil():
			copied := reflect.MakeSlice(v.Type(), v.Len(), v.Len())
			reflect.Copy(copied, v)
			value = copied.Interface()
		case v.Kind() == reflect.Map && !v.IsNil():
			copied := reflect.MakeMapWithSize(v.Type(), v.Len())
			for iter := v.MapRange(); iter.Next(); {
				copied.SetMapIndex(iter.Key(), iter.Value())
			}
			value = copied.Interface()
		}
		before[i] = snapped{value: value, print: fingerprint(arg), codePrint: printOf(arg, true, true)}
	}
	return before
}

// fingerprint prints a value and all the memory it reaches: the elements
// of a slice up to its capacity, the entries of a map, what a pointer or an
// interface value refers to, and the fields of a struct, exported or not,
// with the address of each array and object, so that a write anywhere in
// it, or a pointer that now refers elsewhere, changes the print.
func fingerprint(arg any) string { return printOf(arg, true, false) }

// printOf is fingerprint, with the addresses of arrays and objects left out
// unless addresses is set, so that two copies of a value print the same,
// and with each interface value and function value inside printed as its
// dynamic type and address alone when opaqueCode is set.
func printOf(arg any, addresses, opaqueCode bool) string {
	var b strings.Builder
	address := func(format string, p uintptr) {
		if addresses {
			fmt.Fprintf(&b, format, p)
		}
	}
	// An object is known by its address and its type: a struct and its
	// first field share an address.
	type object struct {
		at  uintptr
		typ reflect.Type
	}
	seen := map[object]bool{}
	var walk func(v reflect.Value, depth int)
	walk = func(v reflect.Value, depth int) {
		if depth > 20 {
			panic(fmt.Sprintf("%T reaches memory deeper than a print follows", arg))
		}
		switch v.Kind() {
		case reflect.Invalid:
			b.WriteString("nil ")
		case reflect.Bool:
			fmt.Fprintf(&b, "%v ", v.Bool())
		case reflect.Int, reflect.Int8, reflect.Int16, reflect.Int32, reflect.Int64:
			fmt.Fprintf(&b, "%d ", v.Int())
		case reflect.Uint, reflect.Uint8, reflect.Uint16, reflect.Uint32, reflect.Uint64, reflect.Uintptr:
			fmt.Fprintf(&b, "%d ", v.Uint())
		case reflect.Float32, reflect.Float64:
			fmt.Fprintf(&b, "%x ", math.Float64bits(v.Float()))
		case reflect.Complex64, reflect.Complex128:
			fmt.Fprintf(&b, "%v ", v.Complex())
		case reflect.String:
			fmt.Fprintf(&b, "%q ", v.String())
		case reflect.Pointer:
			if v.IsNil() {
				b.WriteString("nil ")
				return
			}
			address("*%x ", v.Pointer())
			if at := (object{v.Pointer(), v.Type()}); !seen[at] {
				seen[at] = true
				walk(v.Elem(), depth+1)
			}
		case reflect.UnsafePointer, reflect.Func, reflect.Chan:
			b.WriteString(v.Kind().String())
			address(" %x ", v.Pointer())
		case reflect.Slice:
			if v.IsNil() {
				b.WriteString("nil[] ")
				return
			}
			address("[%x ", v.Pointer())
			fmt.Fprintf(&b, "[%d %d: ", v.Len(), v.Cap())
			whole := v.Slice3(0, v.Cap(), v.Cap())
			for k := range whole.Len() {
				walk(whole.Index(k), depth+1)
			}
			b.WriteString("] ")
		case reflect.Array:
			for k := range v.Len() {
				walk(v.Index(k), depth+1)
			}
		case reflect.Map:
			if v.IsNil() {
				b.WriteString("nil{} ")
				return
			}
			address("{%x ", v.Pointer())
			b.WriteString("{ ")
			keys := v.MapKeys()
			slices.SortFunc(keys, func(x, y reflect.Value) int { return strings.Compare(fmt.Sprint(x), fmt.Sprint(y)) })
			for _, key := range keys {
				walk(key, depth+1)
				walk(v.MapIndex(key), depth+1)
			}
			b.WriteString("} ")
		case reflect.Struct:
			for k := range v.NumField() {
				walk(v.Field(k), depth+1)
			}
		case reflect.Interface:
			if opaqueCode && depth > 0 {
				// The code an interface value holds is its dynamic type
				// and, for a pointer, the address; a value of another
				// kind is printed with the code inside it opaque.
				if v.IsNil() {
					b.WriteString("nil ")
					return
				}
				fmt.Fprintf(&b, "%v ", v.Elem().Type())
				if v.Elem().Kind() == reflect.Pointer {
					address("%x ", v.Elem().Pointer())
					return
				}
			}
			walk(v.Elem(), depth+1)
		}
	}
	walk(reflect.ValueOf(arg), 0)
	return b.String()
}

// reach returns where the memory that values reach lies, as extents from
// start up to end: the array of every slice up to its capacity and every
// object a pointer refers to, at any depth. A slice of capacity zero
// reaches no memory.
func reach(values ...any) [][2]uintptr {
	var extents [][2]uintptr
	seen := map[[2]uintptr]bool{}
	var walk func(v reflect.Value, depth int)
	walk = func(v reflect.Value, depth int) {
		if depth > 20 {
			panic("a value reaches memory deeper than reach follows")
		}
		switch v.Kind() {
		case reflect.Pointer:
			if v.IsNil() {
				return
			}
			extent := [2]uintptr{v.Pointer(), v.Pointer() + max(v.Type().Elem().Size(), 1)}
			if !seen[extent] {
				seen[extent] = true
				extents = append(extents, extent)
				walk(v.Elem(), depth+1)
			}
		case reflect.Slice:
			if v.Cap() == 0 {
				return
			}
			extent := [2]uintptr{v.Pointer(), v.Pointer() + uintptr(v.Cap())*v.Type().Elem().Size()}
			if !seen[extent] {
				seen[extent] = true
				extents = append(extents, extent)
				whole := v.Slice3(0, v.Cap(), v.Cap())
				for k := range whole.Len() {
					walk(whole.Index(k), depth+1)
				}
			}
		case reflect.Array:
			for k := range v.Len() {
				walk(v.Index(k), depth+1)
			}
		case reflect.Map:
			for iter := v.MapRange(); iter.Next(); {
				walk(iter.Key(), depth+1)
				walk(iter.Value(), depth+1)
			}
		case reflect.Struct:
			for k := range v.NumField() {
				walk(v.Field(k), depth+1)
			}
		case reflect.Interface:
			walk(v.Elem(), depth+1)
		}
	}
	for _, value := range values {
		walk(reflect.ValueOf(value), 0)
	}
	return extents
}

func randomInts(rng *rand.Rand) []int {
	values := make([]int, rng.Intn(6))
	for i := range values {
		values[i] = rng.Intn(9) - 4
	}
	return values
}

// randomText returns a short string that may contain spaces, upper and lower
// case letters, multi-byte characters, and invalid UTF-8.
func randomText(rng *rand.Rand) string {
	pieces := []string{"a", "B", " ", "ab", "é", "ß", "\xff", "\t", "世"}
	var text strings.Builder
	for range rng.Intn(5) {
		text.WriteString(pieces[rng.Intn(len(pieces))])
	}
	return text.String()
}

// randomFormat returns a format of the kinds code passes to Printf: verbs
// with flags, widths, precisions, and indices, too few or too many for the
// operands, and bad verbs.
func randomFormat(rng *rand.Rand) string {
	parts := []string{"x", " ", "%v", "%+v", "%#v", "%s", "%q", "%x", "% #x", "%d", "%5.2f", "%T", "%p", "%[1]v", "%[2]d", "%*d", "%-8q", "%z", "%w", "%%", "%!"}
	var b strings.Builder
	for range rng.Intn(6) {
		b.WriteString(parts[rng.Intn(len(parts))])
	}
	return b.String()
}

// randomOperands returns values that vego lets code format: numbers,
// booleans, strings, slices of them, plain structs, nil, and errors of
// known origin.
func randomOperands(rng *rand.Rand) []any {
	type pair struct {
		A int
		b string
	}
	values := []any{0, -1, 1 << 62, uint8(200), true, "", "text", "\xff\x00", 2.5, []int{1, 2}, []string{"a", ""}, []byte("hi"),
		pair{3, "x"}, []pair{{1, "y"}}, nil, errors.New("made"), fmt.Errorf("wrapped: %w", io.EOF)}
	operands := make([]any, rng.Intn(5))
	for i := range operands {
		operands[i] = values[rng.Intn(len(values))]
	}
	return operands
}

// randomWriter returns a writer from the standard library: a buffer, a
// writer that discards, or a file in scratch.
func randomWriter(rng *rand.Rand) io.Writer {
	switch rng.Intn(3) {
	case 0:
		return &bytes.Buffer{}
	case 1:
		return io.Discard
	}
	file, err := os.CreateTemp(scratch, "out")
	if err != nil {
		panic(err)
	}
	return file
}

// toScratch runs a call that writes to standard output with standard
// output set to a file in scratch.
func toScratch(call func()) {
	file, err := os.CreateTemp(scratch, "stdout")
	if err != nil {
		panic(err)
	}
	defer func() { _ = file.Close() }()
	saved := os.Stdout
	os.Stdout = file
	defer func() { os.Stdout = saved }()
	call()
}

// toLogBuffer runs a call that writes to the standard logger with its
// output set to a buffer.
func toLogBuffer(call func()) {
	saved := log.Writer()
	log.SetOutput(&bytes.Buffer{})
	defer log.SetOutput(saved)
	call()
}

// randomElements returns elements of a path, all empty about a fifth of
// the time.
func randomElements(rng *rand.Rand) []string {
	parts := []string{"", "a", "b/c", "..", "/", "./d"}
	elem := make([]string, rng.Intn(4))
	for i := range elem {
		elem[i] = parts[rng.Intn(len(parts))]
		if rng.Intn(5) == 0 {
			elem[i] = ""
		}
	}
	return elem
}

// scratch is the directory the harnesses that touch files work in, made
// afresh for each run of the test.
var scratch string

// shippedVariables are the error variables the shipped contracts may name,
// by key, with their values. A contract that names another fails the test
// until it is added here.
var shippedVariables = map[string]error{
	"strconv.ErrSyntax":        strconv.ErrSyntax,
	"strconv.ErrRange":         strconv.ErrRange,
	"io/fs.ErrNotExist":        fs.ErrNotExist,
	"context.Canceled":         context.Canceled,
	"context.DeadlineExceeded": context.DeadlineExceeded,
}

// reviewedErrorTypes are the dynamic types that may occur in the tree of an
// error a shipped contract vouches for. Each was read against what vouches
// claims: its methods return, write nothing a caller can see, and call no
// method of their arguments; == on it is identity; and what errors.Is
// reports for it does not change. A type not listed fails the test until
// someone has read its methods and added it.
var reviewedErrorTypes = map[string]bool{
	"*strconv.NumError":   true,
	"*errors.errorString": true,
	"*fs.PathError":       true,
	"syscall.Errno":       true,
	// The type of context.DeadlineExceeded, an empty struct whose methods
	// Error, Timeout, and Temporary return constants.
	"context.deadlineExceededError": true,
}

// grounder converts Go values to the terms that denote them. Each error that
// is not nil gets a constant of its own, which stands for that value.
type grounder struct {
	errs []error
}

// errorName begins the names of the constants that stand for errors.
const errorName = "error #"

func (g *grounder) error(t *logic.Term) error {
	switch {
	case t == logic.NilErr():
		return nil
	case strings.HasPrefix(t.Name, errorName):
		i, _ := strconv.Atoi(strings.TrimPrefix(t.Name, errorName))
		return g.errs[i]
	case strings.HasPrefix(t.Name, sentinelName):
		if value, ok := shippedVariables[strings.TrimPrefix(t.Name, sentinelName)]; ok {
			return value
		}
	}
	panic("no Go error for " + t.String() + "; add the variable to shippedVariables")
}

// groundTerm converts a Go value to the term that denotes it.
func (g *grounder) groundTerm(value any) *logic.Term {
	switch value := value.(type) {
	case int:
		return logic.IntLit(int64(value))
	case bool:
		return logic.BoolLit(value)
	case string:
		return logic.Bytes(value)
	case int32:
		return logic.IntLit(int64(value))
	case []int:
		seq := logic.Fill(logic.IntLit(0), logic.IntLit(0))
		for _, element := range value {
			seq = logic.Push(seq, logic.IntLit(int64(element)))
		}
		return seq
	case []byte:
		seq := logic.Fill(logic.IntLit(0), logic.IntLit(0))
		for _, element := range value {
			seq = logic.Push(seq, logic.IntLit(int64(element)))
		}
		return seq
	case []string:
		seq := logic.Fill(logic.IntLit(0), logic.Bytes(""))
		for _, element := range value {
			seq = logic.Push(seq, logic.Bytes(element))
		}
		return seq
	case uint8:
		return logic.IntLit(int64(value))
	case int64:
		return logic.IntLit(value)
	case uint64:
		return logic.BigLit(new(big.Int).SetUint64(value))
	case [][]byte:
		seq := logic.Fill(logic.IntLit(0), logic.Fill(logic.IntLit(0), logic.IntLit(0)))
		for _, element := range value {
			seq = logic.Push(seq, g.groundTerm(element))
		}
		return seq
	case []any:
		// No shipped contract reads the values a function formats; a
		// formula that did would fail on this constant, which the
		// evaluator cannot read.
		return logic.Const("unreadable", logic.IntSeq)
	case io.Writer, *log.Logger:
		// A writer or a logger is one reference, which no formula of an
		// entry reads but to compare it with nil, which a nil pointer in
		// the interface is.
		if v := reflect.ValueOf(value); v.Kind() == reflect.Pointer && v.IsNil() {
			return logic.RefLit(0)
		}
		return logic.RefLit(1)
	case error:
		if value != nil {
			g.errs = append(g.errs, value)
			return logic.Const(fmt.Sprintf("%s%d", errorName, len(g.errs)-1), logic.Err)
		}
	case nil:
	default:
		// Integers of named types, as time.Month, are numbers; floats and
		// values of which no formula of an entry reads anything, a
		// time.Time or a *time.Location, are constants the evaluator
		// cannot read, so a formula that read one would fail.
		v := reflect.ValueOf(value)
		switch {
		case v.CanInt():
			return logic.IntLit(v.Int())
		case v.CanUint():
			return logic.BigLit(new(big.Int).SetUint64(v.Uint()))
		case v.CanFloat():
			return logic.Const("unreadable float", logic.Float)
		case v.Kind() == reflect.Pointer && v.IsNil():
			return logic.RefLit(0)
		case v.Kind() == reflect.Pointer:
			// A pointer is a reference, which no formula of an entry
			// reads but to compare it with nil; fresh and within are
			// told from the real memory.
			return logic.RefLit(1)
		case v.Kind() == reflect.Struct:
			return logic.Const("unreadable", logic.IntSeq)
		}
		panic(fmt.Sprintf("no term for %T", value))
	}
	return logic.NilErr()
}

// TestShippedContracts runs every contract shipped with vego against the
// function it describes. For each random call whose arguments satisfy the
// contract's requires, every ensures must be true of what the function did.
// This does not prove a contract, but a wrong one is caught before it ships.
func TestShippedContracts(t *testing.T) {
	scratch = t.TempDir()
	pv := &pkgVerifier{
		pass: &analysis.Pass{
			Fset:       token.NewFileSet(),
			Pkg:        types.NewPackage("shipped", "shipped"),
			TypesSizes: types.SizesFor("gc", "amd64"),
			// The error variables the contracts name hold their values in
			// the evaluation below, whatever kind of stable variable they
			// are; nothing in the build writes them.
			ImportPackageFact: func(pkg *types.Package, fact analysis.Fact) bool {
				published, ok := fact.(*sentinelsFact)
				if !ok {
					return false
				}
				published.Vars = map[string]sentinelInfo{}
				for key := range shippedVariables {
					if path, name := key[:strings.LastIndex(key, ".")], key[strings.LastIndex(key, ".")+1:]; path == pkg.Path() {
						published.Vars[name] = sentinelInfo{Kind: stableMade}
					}
				}
				return true
			},
			AllPackageFacts: func() []analysis.PackageFact { return nil },
			// No type of a shipped contract has an invariant.
			ImportObjectFact: func(types.Object, analysis.Fact) bool { return false },
		},
		res:          logic.NewResolver(),
		trusted:      map[*types.Func]*funcInfo{},
		trustSources: map[*trustFile]*token.File{},
		reported:     map[string]bool{},
		usage:        &Usage{},
		reliedKeys:   map[string]bool{},
		typeEntries:  map[string]*funcInfo{},
		// What the entries under formats run is looked up by method.
		importedMethods: map[*types.Func]*funcInfo{},
		ifaceMethods:    map[*types.Func]*funcInfo{},
		importedTypes:   map[*types.TypeName]*funcInfo{},
		funcTypes:       map[*types.TypeName]*funcInfo{},
		unentered:       map[string]bool{},
		ownStates:       map[*types.TypeName][]ifaceState{},
		foreignBroken:   map[*types.Package]bool{},
		imported:        map[*types.Func]*funcInfo{},
		foreign:         map[*types.Package]*logic.Resolver{},
		// The types of the methods of sync are structs, whose invariants
		// are looked up.
		invariants: map[*types.TypeName]*invariantSet{},
	}
	imports := importer.ForCompiler(pv.pass.Fset, "source", nil)
	// A contract names the variables of a package by its path, which must
	// be in the build.
	var built []*types.Package
	for key := range shippedVariables {
		pkg, err := imports.Import(key[:strings.LastIndex(key, ".")])
		if err != nil {
			t.Fatalf("import %s: %v", key, err)
		}
		built = append(built, pkg)
	}
	pv.pass.Pkg.SetImports(built)
	for _, file := range shippedContracts() {
		for _, problem := range file.problems {
			t.Errorf("%s:%d: %s", file.path, problem.line, problem.msg)
		}
		for key := range file.entries {
			t.Run(key, func(t *testing.T) {
				path, name, _ := splitFuncName(key)
				pkg, err := imports.Import(path)
				if err != nil {
					t.Fatalf("import %s: %v", path, err)
				}
				// A claim under asserts must be one that can be read, and
				// every entry that makes one runs through a harness whose
				// kept values have the methods of the optional interfaces
				// and return errors that record their calls; see
				// wrappers_test.go.
				if entry := file.entries[key]; len(entry.asserts) > 0 {
					callee, ok := pkg.Scope().Lookup(name).(*types.Func)
					if receiver, method, isMethod := strings.Cut(strings.TrimPrefix(strings.TrimPrefix(name, "("), "*"), ")."); isMethod {
						typeName := pkg.Scope().Lookup(receiver).(*types.TypeName)
						found, _, _ := types.LookupFieldOrMethod(types.NewPointer(typeName.Type()), true, pkg, method)
						callee, ok = found.(*types.Func)
					}
					if !ok {
						t.Fatalf("package %s has no function %s", path, name)
					}
					if _, problem := pv.assertsClaim(entry, callee.Type().(*types.Signature), callee.Pkg()); problem != "" {
						t.Errorf("the claim under asserts cannot be read: %s", problem)
					}
				}
				if fn := shippedTypeContract(pv, pkg, name); fn != nil && key == "(io.Closer).Close" {
					checkCloseEntry(t, pv, fn)
					return
				}
				if fn := shippedTypeContract(pv, pkg, name); fn != nil {
					checkTypeContract(t, pv, key, fn)
					return
				}
				if key == "(*sync.Once).Do" {
					checkOnceEntry(t, pv, pkg, key)
					return
				}
				if strings.HasPrefix(key, "(*sync.") {
					checkLockEntry(t, pv, pkg, key)
					return
				}
				if key == "log.New" || strings.HasPrefix(key, "(*log.Logger).") {
					checkLoggerEntries(t, pv, pkg, key)
					return
				}
				switch {
				case key == "bufio.NewScanner" || strings.HasPrefix(key, "(*bufio.Scanner)."):
					checkScannerEntries(t, pv, pkg, key)
					return
				case key == "bufio.NewReader" || strings.HasPrefix(key, "(*bufio.Reader)."):
					checkReaderEntries(t, pv, pkg, key)
					return
				case key == "bufio.NewWriter" || strings.HasPrefix(key, "(*bufio.Writer)."):
					checkWriterEntries(t, pv, pkg, key)
					return
				case slices.Contains([]string{"io.NopCloser", "io.LimitReader", "io.TeeReader", "io.MultiReader", "io.MultiWriter"}, key):
					checkIOEntries(t, pv, pkg, key)
					return
				}
				callee, ok := pkg.Scope().Lookup(name).(*types.Func)
				if receiver, method, isMethod := strings.Cut(strings.TrimPrefix(strings.TrimPrefix(name, "("), "*"), ")."); isMethod {
					typeName := pkg.Scope().Lookup(receiver).(*types.TypeName)
					found, _, _ := types.LookupFieldOrMethod(types.NewPointer(typeName.Type()), true, pkg, method)
					callee, ok = found.(*types.Func)
				}
				if !ok {
					t.Fatalf("package %s has no function %s", path, name)
				}
				harness, ok := harnesses[key]
				if !ok {
					t.Fatalf("no harness calls %s; add one to harnesses", key)
				}
				fn := pv.trustedContract(callee)
				for _, defect := range fn.defects {
					t.Errorf("contract cannot be used: %s", defect)
				}
				met := coverage{}
				checkContract(t, pv, key, fn, harness, met)
				met.require(t, fn)
			})
		}
	}
}

// coverage counts, by clause of an ensures and condition of it, the calls
// whose condition held.
type coverage map[*clause][]int

// require fails the test for each condition of an ensures that no call met.
func (met coverage) require(t *testing.T, fn *funcInfo) {
	t.Helper()
	for _, c := range fn.ensures {
		for j, count := range met[c] {
			if count == 0 {
				t.Errorf("no call met condition %d of ensures %q, so the samples do not check it; give the harness inputs that meet it", j+1, c.text)
			}
		}
	}
}

// checkContract runs a harness 400 times and checks every call whose
// arguments satisfy the requires of the contract fn: what the function
// called through calls was given, the vouched errors, that the parameters
// its modifies does not list are as they were before the call, what fresh
// and within say of the results, and every ensures. A clause of an ensures
// whose condition no call met is not checked by the samples; checkContract
// counts in met the calls that meet each condition, which met.require then
// demands: each condition of an implication, of a conjunction of them, or
// both sides of an iff, must hold in some call.
func checkContract(t *testing.T, pv *pkgVerifier, key string, fn *funcInfo, harness func(*rand.Rand) sample, met coverage) {
	t.Helper()
	rng := rand.New(rand.NewSource(1))
	checked := 0
	// earlier holds every result so far, which fresh is checked against;
	// keeping them keeps their memory from being used again.
	var earlier []any
	for range 400 {
		call := harness(rng)
		// What the formulas read of an argument before the call, and the
		// print of what it reached then, where the harness took one.
		before, prints := make([]any, len(call.before)), make([]string, len(call.before))
		for i, value := range call.before {
			before[i] = value
			if snap, ok := value.(snapped); ok {
				before[i], prints[i] = snap.value, snap.print
			}
		}
		if call.after == nil {
			for i, value := range call.before {
				if _, ok := value.(snapped); ok || len(reach(value)) > 0 {
					t.Fatalf("the harness of %s gives no after for %s, a %T that reaches memory, so a change to it would not be seen", key, fn.params[i].Name(), before[i])
				}
			}
			call.after = before
		}
		env := &specEnv{
			v: &fnVerifier{pkgVerifier: pv, fn: fn}, fn: fn,
			given: map[*types.Var]*logic.Term{}, givenPost: map[*types.Var]*logic.Term{},
		}
		g := &grounder{}
		eval := &evaluator{bindings: map[string]*big.Int{}, errors: g, callbacks: map[string]func(int64) int64{}}
		// What a function the contract applies returns is what
		// the harness answers.
		env.applied = map[*types.Var]*logic.Term{}
		for _, param := range fn.params {
			if cb := fn.calls[param]; cb != nil && cb.applied {
				sort, _ := sortOf(cb.sig.Results().At(0).Type())
				name := "callback " + param.Name()
				env.applied[param] = logic.Const(name, logic.SeqOf(sort))
				eval.callbacks[name] = call.answers[param.Name()]
			}
		}
		for i, param := range fn.params {
			// A function is one reference, which no formula of an
			// entry reads.
			if _, isFunc := param.Type().Underlying().(*types.Signature); isFunc {
				env.given[param], env.givenPost[param] = logic.RefLit(1), logic.RefLit(1)
				continue
			}
			env.given[param], env.givenPost[param] = g.groundTerm(before[i]), g.groundTerm(call.after[i])
		}
		env.givenRelation = func(name string, paths []logic.Path) (*logic.Term, error) {
			return logic.BoolLit(relation(t, fn, call, earlier, name, paths)), nil
		}
		satisfied := true
		for _, c := range fn.requires {
			formula, err := pv.res.Formula(c.node, env)
			if err != nil {
				t.Fatalf("requires %q: %v", c.text, err)
			}
			satisfied = satisfied && eval.judge(t, fmt.Sprintf("requires %q", c.text), formula)
		}
		if !satisfied {
			continue
		}
		checked++
		for i, param := range fn.params {
			if _, isFunc := param.Type().Underlying().(*types.Signature); isFunc {
				continue
			}
			// What code that a parameter under runs holds writes is that
			// code's own write, as is what a function the call was
			// handed writes.
			listed := slices.ContainsFunc(fn.modifies, func(m *modTarget) bool { return m.name == param.Name() })
			_, isInterface := param.Type().Underlying().(*types.Interface)
			snap, snapshotted := call.before[i].(snapped)
			switch {
			case listed:
			case fn.runs[param] && isInterface:
				// An interface value under runs is code, and what it
				// reaches is its code's own memory.
			case fn.runs[param] && snapshotted:
				if snap.codePrint != printOf(call.after[i], true, true) {
					t.Fatalf("%s changed %s, or memory it reaches outside the code it holds, which its modifies does not list", key, param.Name())
				}
			case fn.runs[param]:
				t.Fatalf("the harness of %s does not snapshot %s, which is under runs and reaches memory outside the code it holds", key, param.Name())
			case call.unwritten != nil:
				if printOf(call.unwritten[i], false, false) != printOf(call.after[i], false, false) {
					t.Fatalf("%s changed %s, which its modifies does not list: %v became %v", key, param.Name(), call.unwritten[i], call.after[i])
				}
			case prints[i] != "":
				if prints[i] != fingerprint(call.after[i]) {
					t.Fatalf("%s changed %s, or memory it reaches, which its modifies does not list: before it, the print of %s was\n%s\nand after it\n%s",
						key, param.Name(), param.Name(), prints[i], fingerprint(call.after[i]))
				}
			case len(reach(before[i])) > 0:
				t.Fatalf("the harness of %s does not snapshot %s, a %T that reaches memory, so a change to it would not be seen", key, param.Name(), before[i])
			case !unchanged(before[i], call.after[i]):
				t.Fatalf("%s changed %s, which its modifies does not list: %v became %v", key, param.Name(), before[i], call.after[i])
			}
		}
		// The function called what it was handed only with
		// arguments that the requires of calls allow.
		for _, param := range fn.params {
			cb := fn.calls[param]
			if cb == nil {
				continue
			}
			for _, args := range call.calls[param.Name()] {
				given := maps.Clone(env.given)
				for i, p := range cb.params {
					given[p] = g.groundTerm(args[i])
				}
				inner := &specEnv{v: env.v, fn: cb.fn, given: given, givenPost: map[*types.Var]*logic.Term{}}
				for _, c := range cb.requires {
					formula, err := pv.res.Formula(c.node, inner)
					if err != nil {
						t.Fatalf("calls requires %q: %v", c.text, err)
					}
					if !eval.judge(t, fmt.Sprintf("calls requires %q", c.text), formula) {
						t.Fatalf("%s called %s with %v, for which the calls requires %q is false, in the call with arguments %v",
							key, param.Name(), args, c.text, before)
					}
				}
			}
		}
		for i, result := range call.results {
			if fn.vouches[i] {
				checkVouched(t, result)
			}
			env.givenResults = append(env.givenResults, g.groundTerm(result))
		}
		for _, c := range fn.ensures {
			formula, err := pv.res.Formula(c.node, env)
			if err != nil {
				t.Fatalf("ensures %q: %v", c.text, err)
			}
			if !eval.judge(t, fmt.Sprintf("ensures %q", c.text), formula) {
				t.Fatalf("ensures %q is false for the call with arguments %v, which left them as %v and returned %v",
					c.text, before, call.after, call.results)
			}
			conds := conditions(formula)
			if met[c] == nil {
				met[c] = make([]int, len(conds))
			}
			for j, cond := range conds {
				if eval.judge(t, fmt.Sprintf("condition %d of ensures %q", j+1, c.text), cond) {
					met[c][j]++
				}
			}
		}
		earlier = append(earlier, call.results...)
	}
	if checked < 100 {
		t.Fatalf("only %d of 400 random calls satisfied the requires; the harness does not exercise the contract", checked)
	}
}

// unchanged reports whether an argument is as it was: deeply equal, with a
// float equal to itself also when it is a NaN.
func unchanged(before, after any) bool {
	if x, isFloat := before.(float64); isFloat {
		y, isFloat := after.(float64)
		return isFloat && math.Float64bits(x) == math.Float64bits(y)
	}
	return reflect.DeepEqual(before, after)
}

// conditions returns what must hold in some sample for a clause to be
// checked: the condition of an implication, those of each implication of
// a conjunction, and both sides of an iff.
func conditions(t *logic.Term) []*logic.Term {
	switch t.Op {
	case logic.OpImplies:
		return []*logic.Term{t.Args[0]}
	case logic.OpIff:
		return []*logic.Term{t.Args[0], logic.Not(t.Args[0])}
	case logic.OpAnd:
		var all []*logic.Term
		for _, arg := range t.Args {
			all = append(all, conditions(arg)...)
		}
		return all
	}
	return nil
}

// extent returns where the memory a slice or a pointer refers to lies, as
// addresses from start up to end, and false when it refers to none: a nil
// pointer, or a slice of capacity zero, which shares runtime.zerobase with
// every other.
func extent(value any) (start, end uintptr, ok bool) {
	v := reflect.ValueOf(value)
	switch v.Kind() {
	case reflect.Slice:
		if v.Cap() == 0 {
			return 0, 0, false
		}
		start = v.Pointer()
		return start, start + uintptr(v.Cap())*v.Type().Elem().Size(), true
	case reflect.Pointer:
		if v.IsNil() {
			return 0, 0, false
		}
		start = v.Pointer()
		return start, start + max(v.Type().Elem().Size(), 1), true
	}
	return 0, 0, false
}

// relation decides fresh(x) and within(a, b) of a call from the real
// memory: a result is fresh when it refers to no memory, or to memory that
// no argument and no earlier result reaches directly; within(a, b) holds
// when a refers to no memory, or lies inside b's. Only results can be
// fresh, and only a result can lie within a parameter, which is all that
// the shipped entries say.
func relation(t *testing.T, fn *funcInfo, call sample, earlier []any, name string, paths []logic.Path) bool {
	t.Helper()
	valueOf := func(p logic.Path) any {
		if len(p.Steps) > 0 {
			t.Fatalf("the harness can tell %s only of a parameter or a result, not of a path", name)
		}
		if i, isResult := fn.resultNames[p.Root]; isResult {
			return call.results[i]
		}
		for i, param := range fn.params {
			if param.Name() == p.Root {
				return call.after[i]
			}
		}
		t.Fatalf("%s(%s): no parameter or result is called %s", name, p.Root, p.Root)
		return nil
	}
	if _, isResult := fn.resultNames[paths[0].Root]; !isResult {
		t.Fatalf("the harness can tell %s only of a result, not of %s", name, paths[0].Root)
	}
	value := valueOf(paths[0])
	switch v := reflect.ValueOf(value); {
	case v.Kind() == reflect.Pointer && v.IsNil():
		// A nil pointer is not fresh, and lies within nothing.
		return false
	case v.Kind() != reflect.Slice && v.Kind() != reflect.Pointer:
		t.Fatalf("the harness cannot tell %s of %s, a %T; it tells it of slices and pointers", name, paths[0].Root, value)
	}
	start, end, refers := extent(value)
	if !refers {
		// A slice of capacity zero has no memory.
		return true
	}
	overlaps := func(extents [][2]uintptr) bool {
		return slices.ContainsFunc(extents, func(e [2]uintptr) bool { return start < e[1] && e[0] < end })
	}
	switch name {
	case "fresh":
		// Fresh memory is none that an argument, another result of the
		// call, or an earlier result reaches, at any depth.
		var others []any
		for i, other := range call.results {
			if i != fn.resultNames[paths[0].Root] {
				others = append(others, other)
			}
		}
		return !overlaps(reach(call.after...)) && !overlaps(reach(others...)) && !overlaps(reach(earlier...))
	case "within":
		s, e, ok := extent(valueOf(paths[1]))
		return ok && s <= start && end <= e
	}
	t.Fatalf("the harness cannot tell %s", name)
	return false
}

// checkVouched checks an error that a shipped contract vouches for: every
// error in its tree has a dynamic type someone has read, and == on it is
// identity.
func checkVouched(t *testing.T, result any) {
	t.Helper()
	for err, _ := result.(error); err != nil; err = errors.Unwrap(err) {
		if _, several := err.(interface{ Unwrap() []error }); several {
			t.Fatalf("%v wraps several errors, which vouches does not cover", err)
		}
		name := reflect.TypeOf(err).String()
		if !reviewedErrorTypes[name] {
			t.Fatalf("the tree of %q holds a %s, which is not among the reviewed error types; read its methods against what vouches claims and add it", result, name)
		}
		if err != err { //nolint:staticcheck // == on the error must be identity
			t.Fatalf("%q is not equal to itself", err)
		}
	}
}

// TestRemoveOutcomes checks that the harness of os.Remove produces each
// outcome it is meant to, so that the errors checkVouched sees include
// every kind os.Remove returns here.
func TestRemoveOutcomes(t *testing.T) {
	scratch = t.TempDir()
	seen := map[string]bool{}
	rng := rand.New(rand.NewSource(1))
	for range 400 {
		err, _ := harnesses["os.Remove"](rng).results[0].(error)
		var errno syscall.Errno
		switch {
		case err == nil:
			seen["success"] = true
		case errors.As(err, &errno):
			seen[errno.Error()] = true
		}
	}
	for _, want := range []string{"success", syscall.ENOENT.Error(), syscall.ENOTEMPTY.Error(), syscall.ENOTDIR.Error(), syscall.EINVAL.Error()} {
		if !seen[want] {
			t.Errorf("no call of os.Remove ended with %s; got %v", want, seen)
		}
	}
}

// recordingError is an error whose methods fail the test when called while
// the call it is handed to is active: the entries of the os predicates
// claim under asserts that they call no method of what err holds, but for
// IsTimeout its Timeout. It also has Unwrap, Is, and the methods of fmt,
// which an assertion could find.
type recordingError struct {
	log      *keptLog
	timeout  bool
	allowed  bool
	wrapping error
}

func (e recordingError) Error() string {
	e.log.called("Error of the error handed to an os predicate")
	return "recorded"
}

func (e recordingError) Unwrap() error {
	e.log.called("Unwrap of the error handed to an os predicate")
	return e.wrapping
}

func (e recordingError) Is(error) bool {
	e.log.called("Is of the error handed to an os predicate")
	return true
}

func (e recordingError) String() string {
	e.log.called("String of the error handed to an os predicate")
	return ""
}

func (e recordingError) Timeout() bool {
	if !e.allowed {
		e.log.called("Timeout of the error handed to an os predicate")
	}
	return e.timeout
}

// osPredicate returns a harness for an os predicate on errors: nil, the
// errors of package fs and syscall it looks for, those wrapped in a
// *PathError, a *LinkError, or a *SyscallError, and a recording error,
// bare or wrapped. Each call runs as one that is handed what it is given,
// so a method of the recording error called during it fails the test.
func osPredicate(predicate func(error) bool, timeout bool) func(rng *rand.Rand) sample {
	return func(rng *rand.Rand) sample {
		k := &keptLog{}
		recorded := recordingError{log: k, timeout: rng.Intn(2) == 0, allowed: timeout, wrapping: fs.ErrNotExist}
		inner := []error{nil, fs.ErrNotExist, fs.ErrExist, fs.ErrPermission, syscall.ENOENT, syscall.EEXIST, syscall.EACCES,
			syscall.ETIMEDOUT, recorded}[rng.Intn(9)]
		err := inner
		if inner != nil {
			switch rng.Intn(4) {
			case 1:
				err = &os.PathError{Op: "open", Path: "x", Err: inner}
			case 2:
				err = &os.LinkError{Op: "link", Old: "x", New: "y", Err: inner}
			case 3:
				err = os.NewSyscallError("read", inner)
			}
		}
		before := snapshot(err)
		done := k.enter()
		result := predicate(err)
		done()
		k.check()
		return sample{before: before, after: []any{err}, results: []any{result}}
	}
}
