// Command exitsref calls its own main, which therefore says whether it
// may end the process, as any function does.
package main

import "os"

// main ends the process without an Exits annotation, and again is called
// by again.
//
// @Ensures True
func main() {
	if len(os.Args) > 5 {
		os.Exit(1) // want `vego: main calls os\.Exit, which may end the process, and main is referred to at main\.go:22:2; a main that its package calls or uses as a value says so with // @Exits in its doc comment, as any function does`
	}
}

// again runs main once more.
//
// @Exits // want `vego: again has an Exits annotation, but nothing it calls may end the process; remove it, since an Exits annotation must say exactly whether the function may end the process`
// @Ensures True
func again() {
	main()
}
