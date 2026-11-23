// Command json386 runs one case of TestJSON386: an entry of encoding/json
// on a value at the edge of the bound vego proves, on a 32-bit target. It
// prints the length of what it built, or panics.
package main

import (
	"encoding/json"
	"fmt"
	"os"
	"strconv"
	"strings"
)

func main() {
	n, err := strconv.Atoi(os.Args[2])
	if err != nil {
		panic(err)
	}
	var b []byte
	switch os.Args[1] {
	case "string":
		b, err = json.Marshal(strings.Repeat("\x00", n))
	case "bytes":
		b, err = json.Marshal(make([]byte, n))
	case "map":
		m := make(map[int32]bool, n)
		for i := range n {
			m[int32(-1<<31+i)] = false
		}
		b, err = json.Marshal(m)
	case "indent":
		s := make([]string, n)
		for i := range s {
			s[i] = strings.Repeat("\x00", n)
		}
		b, err = json.MarshalIndent(s, "", "  ")
	default:
		panic("no case " + os.Args[1])
	}
	if err != nil {
		panic(err)
	}
	fmt.Println(len(b))
}
