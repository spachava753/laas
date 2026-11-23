// Command buffers386 brings a strings.Builder or a bytes.Buffer to a state
// near the bound of its shipped entries on a 32-bit target, makes one call,
// and prints the length before the call, what the call was asked, and
// whether it panicked. TestBuffers386 builds it for GOARCH=386 and runs it
// in a memory-limited scope.
//
// Usage: buffers386 builder|buffer grow0 written read n
//
// It grows the empty value by grow0, writes written bytes, reads read of
// them (a Buffer only, with Next), and then calls Grow(n). For append, it
// makes a full []byte of grow0 bytes and appends its first n bytes to it,
// and prints
// the capacity after the append in place of whether it panicked.
package main

import (
	"bytes"
	"fmt"
	"os"
	"strconv"
	"strings"
)

func main() {
	args := make([]int, 4)
	for i := range args {
		n, err := strconv.Atoi(os.Args[2+i])
		if err != nil {
			panic(err)
		}
		args[i] = n
	}
	grow0, written, read, n := args[0], args[1], args[2], args[3]
	chunk := make([]byte, 1<<20)
	var length, capacity int
	var grow func(int)
	switch os.Args[1] {
	case "append":
		s := make([]byte, grow0)
		func() {
			defer func() {
				if r := recover(); r != nil {
					fmt.Printf("len %d cap %d n %d panicked true %q\n", len(s), cap(s), n, fmt.Sprint(r))
					os.Exit(0)
				}
			}()
			length = len(s)
			// What is appended is the start of s itself, so that only the
			// old array and the new one take memory.
			s = append(s, s[:n]...)
		}()
		fmt.Printf("len %d cap %d n %d panicked false %q\n", length, cap(s), n, "")
		return
	case "builder":
		var b strings.Builder
		b.Grow(grow0)
		for b.Len() < written {
			b.Write(chunk[:min(len(chunk), written-b.Len())])
		}
		length, capacity, grow = b.Len(), b.Cap(), b.Grow
	case "buffer":
		var b bytes.Buffer
		b.Grow(grow0)
		for b.Len() < written {
			b.Write(chunk[:min(len(chunk), written-b.Len())])
		}
		b.Next(read)
		length, capacity, grow = b.Len(), b.Cap(), b.Grow
	default:
		panic("builder or buffer")
	}
	chunk = nil
	panicked := false
	message := ""
	func() {
		defer func() {
			if r := recover(); r != nil {
				panicked, message = true, fmt.Sprint(r)
			}
		}()
		grow(n)
	}()
	fmt.Printf("len %d cap %d n %d panicked %v %q\n", length, capacity, n, panicked, message)
}
