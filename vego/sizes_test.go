package vego

import (
	"testing"

	"github.com/spachava753/laas/vego/internal/logic"
)

// TestRewriteMarked checks where a marked bound is replaced: an atom
// Le(t, mark) under And, Or, the consequent of Implies, and a quantifier's
// body, where a smaller bound gives a stronger hypothesis and dropping it a
// weaker one; and nowhere else, where either would change what the
// hypothesis says in the other direction (F2 of the design review of F38).
func TestRewriteMarked(t *testing.T) {
	parallel(t)
	mark := logic.IntLit(1 << 48)
	marks := map[*logic.Term]bool{mark: true}
	x, y := logic.Const("x", logic.Int), logic.Const("y", logic.Int)
	smaller := logic.IntLit(1000)
	with := func(atom *logic.Term) *logic.Term { return logic.Le(atom.Args[0], smaller) }
	k := logic.Bound("k", logic.Int)
	positive := []*logic.Term{
		logic.Le(x, mark),
		logic.And(logic.Le(x, mark), logic.Le(y, logic.IntLit(3))),
		logic.Or(logic.Eq(x, logic.IntLit(0)), logic.Le(x, mark)),
		logic.Implies(logic.Le(y, logic.IntLit(3)), logic.Le(x, mark)),
		logic.Forall(k, logic.Implies(logic.Le(logic.IntLit(0), k), logic.Le(logic.Add(x, k), mark))),
	}
	for _, hyp := range positive {
		got, ok := rewriteMarked(hyp, marks, with)
		if !ok || holdsMark(got, marks) || !containsTerm(got, smaller) {
			t.Errorf("rewriteMarked(%s) = %s, %v; want the mark replaced", hyp, got, ok)
		}
	}
	elsewhere := []*logic.Term{
		logic.Not(logic.Le(x, mark)),
		logic.Implies(logic.Le(x, mark), logic.Le(y, logic.IntLit(3))),
		logic.Eq(x, mark),
		logic.Le(mark, x),
		logic.Le(logic.Add(x, mark), y),
		logic.Iff(logic.Le(x, mark), logic.Le(y, logic.IntLit(3))),
		logic.And(logic.Le(x, mark), logic.Not(logic.Le(y, mark))),
	}
	for _, hyp := range elsewhere {
		if got, ok := rewriteMarked(hyp, marks, with); ok {
			t.Errorf("rewriteMarked(%s) = %s; a mark that does not stand only as an upper bound in a weakening position must leave the hypothesis alone", hyp, got)
		}
	}
	unmarked := logic.Le(x, logic.IntLit(1<<48))
	if got, ok := rewriteMarked(unmarked, marks, with); !ok || got != unmarked {
		t.Errorf("rewriteMarked(%s) = %s, %v; a bound by the same number that is not the mark must stay", unmarked, got, ok)
	}
}

// containsTerm reports whether t holds sub, by pointer.
func containsTerm(t, sub *logic.Term) bool {
	if t == sub {
		return true
	}
	for _, arg := range t.Args {
		if containsTerm(arg, sub) {
			return true
		}
	}
	return false
}

// shippedClasses is the class of every shipped entry in the bound on every
// value under a declared memory (sizes.go, and the ROADMAP's Sizes under a
// declared memory), each read from the source of Go 1.26.6 and 1.27.3:
// what it exposes of new memory is written (W), it reserves at most the
// array of an operand, which keeps the bound by the operand's (O), it
// reserves by a number and its entry declares what keeps the bound (N), it
// reserves a constant (C), or it exposes no memory it made (none: a part
// of what it is handed, a number, a boolean, or nothing). The parsers of
// strconv are W: on an error they return a *NumError that holds a copy of
// their input (F23 of the review of step 2c).
var shippedClasses = map[string][]string{
	"N": {
		"(*bytes.Buffer).Grow", "(*strings.Builder).Grow", "slices.Grow",
	},
	"C": {
		"(*bufio.Scanner).Scan", "(*regexp.Regexp).Match", "(*regexp.Regexp).MatchString", "bufio.NewReader", "bufio.NewScanner",
		"bufio.NewWriter", "crypto/md5.Sum", "crypto/sha256.Sum256", "io.LimitReader", "io.MultiWriter", "io.NopCloser", "io.TeeReader",
		"log.New", "net/http.NewServeMux", "os.Create", "os.Open",
	},
	"O": {
		"bytes.Map",
	},
	"W": {
		"strconv.Atoi", "strconv.ParseBool", "strconv.ParseInt", "strconv.ParseUint",
		"(*bufio.Scanner).Text", "(*bytes.Buffer).String", "(*bytes.Buffer).Write", "(*bytes.Buffer).WriteByte", "(*bytes.Buffer).WriteRune",
		"(*bytes.Buffer).WriteString", "(*encoding/json.Decoder).Decode", "(*encoding/json.Encoder).Encode", "(*log.Logger).Print",
		"(*log.Logger).Printf", "(*log.Logger).Println", "(*net/url.URL).Query", "(*regexp.Regexp).FindStringSubmatch",
		"(*strings.Builder).Write", "(*strings.Builder).WriteByte", "(*strings.Builder).WriteRune", "(*strings.Builder).WriteString",
		"(net/http.Header).Set", "bytes.FieldsFunc", "bytes.Join", "bytes.Repeat", "bytes.Replace", "bytes.ReplaceAll",
		"encoding/hex.EncodeToString", "encoding/json.Marshal", "encoding/json.MarshalIndent", "encoding/json.Unmarshal", "fmt.Fprint",
		"fmt.Fprintf", "fmt.Fprintln", "fmt.Print", "fmt.Printf", "fmt.Println", "fmt.Sprint", "fmt.Sprintf", "fmt.Sprintln", "io.MultiReader",
		"io.WriteString", "log.Fatal", "log.Fatalf", "log.Fatalln", "log.Print", "log.Printf", "log.Println", "maps.Clone", "maps.Copy",
		"mime.ParseMediaType", "net/http.Error", "net/http.NotFound", "os.Getenv", "os.Getwd", "os.LookupEnv", "os.MkdirAll", "os.Remove",
		"os.WriteFile", "path.Clean", "path.Dir", "path.Join", "path/filepath.Clean", "path/filepath.Dir", "path/filepath.Join",
		"path/filepath.Rel", "regexp.Compile", "regexp.MustCompile", "regexp.MustCompilePOSIX", "slices.Clone", "slices.Insert",
		"strconv.AppendInt", "strconv.FormatInt", "strconv.Itoa", "strconv.Quote", "strconv.Unquote", "strings.Fields", "strings.FieldsFunc",
		"strings.Join", "strings.Map", "strings.Repeat", "strings.Replace", "strings.ReplaceAll", "strings.Split", "strings.SplitAfter",
		"strings.ToLower", "strings.ToUpper", "unicode/utf8.AppendRune",
	},
	"none": {
		"(*bytes.Buffer).Read",
		"(*bufio.Reader).ReadByte", "(*bufio.Scanner).Err", "(*bufio.Writer).Flush", "(*bufio.Writer).Write", "(*bufio.Writer).WriteByte",
		"(*bufio.Writer).WriteString", "(*bytes.Buffer).Bytes", "(*bytes.Buffer).Len", "(*bytes.Buffer).Reset", "(*bytes.Buffer).Truncate",
		"(*net/http.Request).PathValue", "(*os.File).Close", "(*os.File).Read", "(*os.File).Write", "(*os.File).WriteString",
		"(*regexp.Regexp).FindString", "(*strings.Builder).Len", "(*strings.Builder).Reset", "(*strings.Builder).String", "(*sync.Mutex).Lock",
		"(*sync.Mutex).TryLock", "(*sync.Mutex).Unlock", "(*sync.Once).Do", "(*sync.RWMutex).Lock", "(*sync.RWMutex).RLock",
		"(*sync.RWMutex).RUnlock", "(*sync.RWMutex).TryLock", "(*sync.RWMutex).TryRLock", "(*sync.RWMutex).Unlock", "(context.Context).Err",
		"(io.Closer).Close", "(io.Reader).Read", "(io.StringWriter).WriteString", "(io.Writer).Write", "(net/http.Header).Del",
		"(net/http.Header).Get", "(net/http.ResponseWriter).Header", "(net/http.ResponseWriter).Write", "(net/http.ResponseWriter).WriteHeader",
		"(net/url.Values).Get", "(time.Duration).Milliseconds", "(time.Duration).Nanoseconds", "(time.Duration).Seconds", "(time.Time).Add",
		"(time.Time).AddDate", "(time.Time).After", "(time.Time).Before", "(time.Time).Date", "(time.Time).Day", "(time.Time).Equal",
		"(time.Time).Hour", "(time.Time).IsZero", "(time.Time).Minute", "(time.Time).Month", "(time.Time).Nanosecond", "(time.Time).Second",
		"(time.Time).Sub", "(time.Time).Unix", "(time.Time).UnixMilli", "(time.Time).Weekday", "(time.Time).Year", "(time.Time).YearDay",
		"bytes.Contains", "bytes.ContainsFunc", "bytes.Count", "bytes.Cut", "bytes.Equal", "bytes.EqualFold", "bytes.HasPrefix",
		"bytes.HasSuffix", "bytes.Index", "bytes.IndexByte", "bytes.IndexFunc", "bytes.LastIndex", "bytes.LastIndexByte", "bytes.LastIndexFunc",
		"bytes.TrimFunc", "bytes.TrimLeftFunc", "bytes.TrimPrefix", "bytes.TrimRightFunc", "bytes.TrimSpace", "bytes.TrimSuffix", "cmp.Compare",
		"context.CancelFunc", "maps.DeleteFunc", "math.Abs", "math.Ceil", "math.Exp", "math.Floor", "math.Inf", "math.IsInf", "math.IsNaN",
		"math.Log", "math.Max", "math.Min", "math.Mod", "math.NaN", "math.Pow", "math.Round", "math.Sqrt", "math.Trunc", "math/rand.Int",
		"math/rand.Intn", "net/http.StatusText", "os.Exit", "os.IsExist", "os.IsNotExist", "os.IsPermission", "os.IsTimeout", "path.Base",
		"path.Ext", "path.IsAbs", "path.Split", "path/filepath.Base", "path/filepath.Ext", "path/filepath.Split", "slices.BinarySearch",
		"slices.Clip", "slices.Compact", "slices.Contains", "slices.ContainsFunc", "slices.Delete", "slices.DeleteFunc", "slices.Equal",
		"slices.Index", "slices.IndexFunc", "slices.Max", "slices.Min", "slices.Reverse", "slices.Sort", "sort.Find", "sort.Ints",
		"sort.IntsAreSorted", "sort.Search", "sort.SearchInts", "sort.Strings", "strings.Contains", "strings.ContainsFunc", "strings.Count", "strings.Cut", "strings.EqualFold",
		"strings.HasPrefix", "strings.HasSuffix", "strings.Index", "strings.IndexByte", "strings.IndexFunc", "strings.LastIndex",
		"strings.LastIndexByte", "strings.LastIndexFunc", "strings.TrimFunc", "strings.TrimLeft", "strings.TrimLeftFunc", "strings.TrimPrefix",
		"strings.TrimRight", "strings.TrimRightFunc", "strings.TrimSpace", "strings.TrimSuffix", "time.Date", "time.Now", "time.Since",
		"time.Unix", "time.Until", "unicode.IsDigit", "unicode.IsLetter", "unicode.IsLower", "unicode.IsSpace", "unicode.IsUpper",
		"unicode/utf8.DecodeRune", "unicode/utf8.DecodeRuneInString", "unicode/utf8.RuneCountInString", "unicode/utf8.RuneLen",
		"unicode/utf8.ValidString",
	},
}

// TestEntryClasses checks that every shipped entry has a class, and that
// an entry declares what it must meet under a declared memory exactly when
// it reserves by a number: a new entry is read before it ships.
func TestEntryClasses(t *testing.T) {
	parallel(t)
	class := map[string]string{}
	for name, keys := range shippedClasses {
		for _, key := range keys {
			if _, twice := class[key]; twice {
				t.Errorf("%s is listed twice", key)
			}
			class[key] = name
		}
	}
	seen := map[string]bool{}
	for _, file := range shippedContracts() {
		for key, entry := range file.entries {
			seen[key] = true
			got, listed := class[key]
			switch {
			case !listed:
				t.Errorf("the shipped entry %s has no class in shippedClasses; read what it reserves and what it writes before it ships", key)
			case got == "N" && len(entry.declared) == 0:
				t.Errorf("%s reserves by a number, and its entry declares nothing for a declared memory", key)
			case got != "N" && len(entry.declared) > 0:
				t.Errorf("%s declares clauses for a declared memory and is listed as %s", key, got)
			}
		}
	}
	for key := range class {
		if !seen[key] {
			t.Errorf("shippedClasses lists %s, which has no shipped entry", key)
		}
	}
}
