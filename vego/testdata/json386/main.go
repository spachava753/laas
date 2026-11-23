// Command json386 runs one case of TestJSON386: an entry of encoding/json
// on a value at the edge of the bound vego proves, on a 32-bit target. It
// prints the length of what it built, or panics.
package main

import (
	"bytes"
	"encoding/json"
	"fmt"
	"os"
	"strconv"
	"strings"
)

// Big is a struct of 1 KB.
type Big struct {
	A [128]int64
}

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
	case "dstring":
		// n bytes of data: a string of invalid bytes, each decoded as
		// U+FFFD, three bytes.
		data := append(append([]byte{'"'}, bytes.Repeat([]byte{0xff}, n-2)...), '"')
		var s string
		err = json.Unmarshal(data, &s)
		b = []byte(s[:0])
		fmt.Println(len(s))
	case "dslice":
		// n bytes of data: [{},{},...] into a slice of 1 KB structs.
		data := append([]byte{'['}, bytes.Repeat([]byte("{},"), (n-2)/3)...)
		data[len(data)-1] = ']'
		var s []Big
		err = json.Unmarshal(data, &s)
		fmt.Println(len(s))
	case "dmap":
		// n bytes of data: {"-1000000":true,...} into a map with integer
		// keys.
		var d bytes.Buffer
		d.WriteByte('{')
		for i := 0; d.Len() < n-30; i++ {
			fmt.Fprintf(&d, "%q:true,", fmt.Sprint(-1000000000-i))
		}
		d.WriteString(`"0":true}`)
		var m map[int32]bool
		err = json.Unmarshal(d.Bytes(), &m)
		fmt.Println(len(m))
	default:
		panic("no case " + os.Args[1])
	}
	if err != nil {
		panic(err)
	}
	fmt.Println(len(b))
}
