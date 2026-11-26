package guide

import (
	"log"
	"os"
)

// The programs of the section on functions that end the process.

// MustSucceed ends the process when err is not nil.
//
// @Exits
// @Ensures err = nil
func MustSucceed(err error) {
	if err != nil {
		log.Fatal("failed")
	}
}

// Usage prints how to call the program and ends it.
//
// @Exits
// @Ensures False
func Usage() {
	log.Print("usage: tool name")
	os.Exit(2)
}

// FirstArg returns the first argument after the program's name.
//
// @Exits
// @Ensures |args| >= 2 And name = args[1]
func FirstArg(args []string) (name string) {
	if len(args) < 2 {
		Usage()
	}
	return args[1]
}

// @Exits // want `vego: NoExit has an Exits annotation, but nothing it calls may end the process; remove it, since an Exits annotation must say exactly whether the function may end the process`
// @Ensures True
func NoExit() {
}
