// Command guidemain is the main function of the section on functions that
// end the process.
package main

import (
	"log"
	"os"
)

// usage prints how to call the program and ends it.
//
// @Exits
// @Ensures False
func usage() {
	log.Print("usage: tool name")
	os.Exit(2)
}

// @Ensures True
func main() {
	if len(os.Args) < 2 {
		usage()
	}
	if os.Args[1] == "" {
		log.Fatal("the name is empty")
	}
}
