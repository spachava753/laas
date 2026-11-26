// Command exitsmain ends the process from main, which needs no Exits
// annotation since only the runtime calls it.
package main

import (
	"exits"
	"log"
	"os"
)

// count returns how many names it was given, and fails for none.
//
// @Ensures err = nil <-> |names| > 0
// @Ensures err = nil -> n = |names|
func count(names []string) (n int, err error) {
	if len(names) == 0 {
		return 0, exits.ErrEmpty
	}
	return len(names), nil
}

// usage prints how to call the program and ends it.
//
// @Exits
// @Ensures False
func usage() {
	log.Print("usage: exitsmain name...")
	os.Exit(2)
}

// main runs count on the arguments and ends the process on its error.
//
// @Ensures True
func main() {
	if len(os.Args) < 2 {
		usage()
	}
	name := os.Args[1]
	n, err := count(os.Args[1:])
	if err != nil {
		log.Fatal(err)
	}
	// @Assert n >= 1
	if name == "-" {
		os.Exit(3)
	}
	if n > 1 {
		os.Exit(0)
	}
	log.Println(exits.Positive(n))
}
