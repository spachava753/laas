// Command hex386 calls encoding/hex.EncodeToString on a slice of the length
// it is given and prints "ok" when it returns, or "panic:" and the value of
// the panic when it panics. TestHex386 runs it built for 386 at the edge of
// the requires of the shipped entry.
package main

import (
	"encoding/hex"
	"fmt"
	"os"
	"strconv"
)

func main() {
	n, err := strconv.Atoi(os.Args[1])
	if err != nil {
		fmt.Println("bad length:", err)
		os.Exit(2)
	}
	src := make([]byte, n)
	defer func() {
		if r := recover(); r != nil {
			fmt.Println("panic:", r)
		}
	}()
	s := hex.EncodeToString(src)
	fmt.Println("ok", len(s))
}
