package vego

import (
	"sync/atomic"
	"testing"
)

// Most tests of the package run side by side. A test that changes a
// setting of the whole package, such as growthRatio or skipCopyWalk, must
// not: every analysis beside it would run with the setting. Go runs the
// top-level tests that do not call t.Parallel first, one after another,
// and releases the parallel ones only after all of them have finished, so
// such a test is a top-level test that calls alone. A subtest of a parallel
// test is not protected that way, and alone fails it.

// parallelBegun is set once a parallel test has been released.
var parallelBegun atomic.Bool

// parallel runs the test beside the other parallel tests.
func parallel(t *testing.T) {
	t.Helper()
	t.Parallel()
	parallelBegun.Store(true)
}

// alone fails the test if parallel tests have begun to run, which is the
// case for a subtest of a parallel test and for nothing that Go runs before
// them.
func alone(t *testing.T) {
	t.Helper()
	if parallelBegun.Load() {
		t.Fatal("this test changes a setting of the whole package while other tests run beside it; make it a top-level test that does not call parallel")
	}
}

// corpusRuns bounds the analyses of corpus programs, and the shipped
// verifiers, that are under way at once. Each type-checks the standard
// library from source and holds it, so without a bound the tests that run
// side by side would hold many copies at once.
var corpusRuns = make(chan struct{}, 2)

// heavy holds one of corpusRuns until the returned function is called.
func heavy() func() {
	corpusRuns <- struct{}{}
	return func() { <-corpusRuns }
}
