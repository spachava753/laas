// Package loggervar logs through a logger in a package-level variable
// (step 7 of F32).
package loggervar

import (
	"log"
	"os"
)

var logger = log.New(os.Stderr, "app: ", 0)

// Notify logs a message through a logger over standard error, which needs
// nothing listed.
//
// @Requires |msg| <= 1000
// @Ensures True
func Notify(msg string) {
	logger.Printf("report: %s", msg)
}

// notifyTwice logs twice.
//
// @Requires |msg| <= 1000
// @Ensures True
func notifyTwice(msg string) {
	logger.Print(msg)
	logger.Println(msg)
}

// notifyListed lists a logger that needs nothing listed.
//
// @Requires |msg| <= 1000
// @Modifies logger // want `vego: Modifies lists logger, but notifyListed never needs to modify it; a Modifies clause must list exactly what the function may write`
// @Ensures True
func notifyListed(msg string) {
	logger.Print(msg)
}

// Tally counts what is written to it.
type Tally struct{ n int }

// Write counts.
//
// @Requires t != nil
// @Modifies t
// @Ensures n = |p| And err = nil
func (t *Tally) Write(p []byte) (n int, err error) {
	if t.n < 1000000 {
		t.n++
	}
	return len(p), nil
}

var tally Tally

var counted = log.New(&tally, "", 0)

// count logs into the tally, which the logger's writer writes, so it lists
// the logger.
//
// @Requires |msg| <= 1000
// @Modifies counted
// @Ensures True
func count(msg string) {
	counted.Print(msg)
}

// countUnlisted does not.
//
// @Requires |msg| <= 1000
// @Ensures True
func countUnlisted(msg string) {
	counted.Print(msg) // want `vego: Print may modify counted, which countUnlisted may not modify; it is memory that the package-level variable counted refers to; list counted in a `
}

var renamed = log.New(os.Stderr, "", 0)

// rename sets a prefix, and is not verified.
func rename() { renamed.SetPrefix("x: ") }

// notifyRenamed logs through a logger used in another way.
//
// @Ensures True
func notifyRenamed() {
	renamed.Print("x") // want `vego: cannot verify notifyRenamed: renamed is used at log.go:\d+ other than as the receiver of Printf, Print, or Println or in a comparison with nil, s`
}

// Exported is an exported logger.
var Exported = log.New(os.Stderr, "", 0)

// notifyExported logs through it.
//
// @Ensures True
func notifyExported() {
	Exported.Print("x") // want `vego: cannot verify notifyExported: Exported is an exported logger, which code of another package could use in other ways; a logger in a variable that`
}

var broken = log.New(nil, "", 0)

// notifyBroken logs through a logger whose initialiser does not verify.
//
// @Ensures True
func notifyBroken() {
	broken.Print("x") // want `vego: cannot verify notifyBroken: broken cannot be relied on: its initialiser does not verify, at log.go:\d+:\d+: precondition of New may not hold: out `
}

// Echo writes by logging, which calls Echo again.
type Echo struct{}

// Write logs.
//
// @Ensures n = |p| And err = nil
func (Echo) Write(p []byte) (n int, err error) {
	echoed.Print("again") // want `vego: cannot verify Write: echoed cannot be relied on: its initialiser does not verify, at log.go:\d+:\d+: Write may call through a function value or a`
	return len(p), nil
}

var echoed = log.New(Echo{}, "", 0)

// echo logs through a writer that logs through the same logger.
//
// @Ensures True
func echo() {
	echoed.Print("x") // want `vego: cannot verify echo: echoed cannot be relied on: its initialiser does not verify, at log.go:\d+:\d+: Write may call through a function value or an`
}
