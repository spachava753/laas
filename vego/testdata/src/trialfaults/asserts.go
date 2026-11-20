package trialfaults

import "io"

// Trusted functions whose entries make a claim under asserts that is
// defective, each reported where it is called.

func assertsUnknown(r io.Reader)    {}
func assertsNoCode(n int)           {}
func assertsBadType(r io.Reader)    {}
func assertsNotRun(r io.Reader)     {}
func assertsFormatted(v ...any)     {}
func assertsLiteral(r io.Reader)    {}
func assertsLiteralBad(r io.Reader) {}
func assertsNoCodeType(r io.Reader) {}

// @Requires r != nil
// @Ensures True
func UsesAsserts(r io.Reader) {
	assertsUnknown(r)   // want `its asserts "q": q is not a parameter`
	assertsNoCode(1)    // want `its asserts lists n, whose type int can hold no error, interface value, function value, channel, or unsafe.Pointer, so the claim says nothing`
	assertsBadType(r)   // want `its asserts lists "io.Nope" for r, which names no type that trialfaults or what it imports declares`
	assertsNotRun(r)    // want `its asserts lists r, which its runs and keeps do not list`
	assertsFormatted(1) // want `its asserts lists v, which its formats lists; formats already says what the function runs of it`
	assertsLiteral(r)
	assertsLiteralBad(r) // want `its asserts lists "interface\{ Next\(\) io.Reader \}" for r, which is not an interface type written with predeclared types only`
	assertsNoCodeType(r) // want `its asserts lists flag.ErrorHandling for r, a type that can hold no code, so listing it says nothing`
}
