// Command mediatype runs mime.ParseMediaType on values of one shape at the
// lengths it is given, for TestMediaTypeBound on this machine and for
// TestMIME386 on a 32-bit target. For each length it builds a value of
// at most that many bytes, calls ParseMediaType once, and prints the length
// of the value and the bytes the call allocated. Given only "shapes", it
// prints the name of each shape.
package main

import (
	"fmt"
	"mime"
	"os"
	"runtime"
	"strconv"
	"strings"
)

// alphabet holds the bytes a parameter's name may start with whose lower
// case is themselves, other than '*', so that names are as short as they
// can be and distinct after lowercasing.
var alphabet = func() string {
	var b strings.Builder
	for c := byte(33); c < 127; c++ {
		if strings.IndexByte(`()<>@,;:\"/[]?=*`, c) < 0 && (c < 'A' || c > 'Z') {
			b.WriteByte(c)
		}
	}
	return b.String()
}()

// name returns the i-th name over alphabet, shortest first.
func name(i int) string {
	s := ""
	for {
		s = string(alphabet[i%len(alphabet)]) + s
		i /= len(alphabet)
		if i == 0 {
			return s
		}
		i--
	}
}

// shapes write the i-th part of a value after its media type "a/b".
var shapes = map[string]func(b *strings.Builder, i int){
	// Repeated parameters with one name and one value.
	"repeated": func(b *strings.Builder, i int) { b.WriteString("; a=b") },
	// Parameters with distinct names, upper case, so that each is lowercased.
	"keys": func(b *strings.Builder, i int) { fmt.Fprintf(b, "; X%s=v", name(i)) },
	// RFC 2231 continuations of one value.
	"continuations": func(b *strings.Builder, i int) { fmt.Fprintf(b, "; x*%d=v", i) },
	// Parameters with a star and distinct names: each makes a map of its own.
	"starred0":     func(b *strings.Builder, i int) { fmt.Fprintf(b, ";%s*0=x", name(i)) },
	"starred":      func(b *strings.Builder, i int) { fmt.Fprintf(b, ";%s*=x", name(i)) },
	"starred0*":    func(b *strings.Builder, i int) { fmt.Fprintf(b, ";%s*0*=x", name(i)) },
	"starredupper": func(b *strings.Builder, i int) { fmt.Fprintf(b, ";X%s*0=x", name(i)) },
	"starredtwo":   func(b *strings.Builder, i int) { fmt.Fprintf(b, ";%s*0=x;%s*1=x", name(i), name(i)) },
	"starredencoded": func(b *strings.Builder, i int) {
		fmt.Fprintf(b, ";%s*0*=utf-8''x;%s*1*=%%41", name(i), name(i))
	},
}

func main() {
	if len(os.Args) == 2 && os.Args[1] == "shapes" {
		fmt.Println("invalid")
		fmt.Println("encoded")
		for shape := range shapes {
			fmt.Println(shape)
		}
		return
	}
	if len(os.Args) < 3 {
		fmt.Fprintln(os.Stderr, "usage: mediatype SHAPE LENGTH...")
		os.Exit(2)
	}
	for _, arg := range os.Args[2:] {
		length, err := strconv.Atoi(arg)
		if err != nil {
			panic(err)
		}
		var v string
		switch shape := os.Args[1]; shape {
		case "invalid":
			// A media type of invalid bytes, each of which lowercasing makes
			// three.
			v = strings.Repeat("\xff", length)
		case "encoded":
			// One encoded value of percent escapes.
			v = "a/b; x*=utf-8''" + strings.Repeat("%41", max(0, length-15)/3)
			v = v[:min(len(v), length)]
		default:
			write, ok := shapes[shape]
			if !ok {
				panic("no shape " + shape)
			}
			// As many parts as fit in length.
			var b, part strings.Builder
			b.WriteString("a/b")
			for i := 0; ; i++ {
				part.Reset()
				write(&part, i)
				if b.Len()+part.Len() > length {
					break
				}
				b.WriteString(part.String())
			}
			v = b.String()
		}
		var before, after runtime.MemStats
		runtime.GC()
		runtime.ReadMemStats(&before)
		_, _, _ = mime.ParseMediaType(v)
		runtime.ReadMemStats(&after)
		fmt.Printf("len %d alloc %d\n", len(v), after.TotalAlloc-before.TotalAlloc)
	}
}
