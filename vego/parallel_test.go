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

// running counts the parallel tests that have been released and have not
// ended. A parallel test counts until its subtests have ended too.
var running atomic.Int64

// parallel runs the test beside the other parallel tests.
func parallel(t *testing.T) {
	t.Helper()
	t.Parallel()
	running.Add(1)
	t.Cleanup(func() { running.Add(-1) })
}

// alone fails the test if parallel tests are running, which is the case for
// a subtest of a parallel test and for nothing that Go runs before them,
// in every round of -count or -cpu.
func alone(t *testing.T) {
	t.Helper()
	if running.Load() > 0 {
		t.Fatal("this test changes a setting of the whole package while other tests run beside it; make it a top-level test that does not call parallel")
	}
}

// corpusRuns bounds the loads of corpus programs and of the standard
// library from source that are held at once: by an analysis of the corpus,
// a list of its conversions, or a verifier of the shipped entries. Each
// type-checks the standard library from source and holds it, so without a
// bound the tests that run side by side would hold many copies at once.
var corpusRuns = make(chan struct{}, 2)

// heavy holds one of corpusRuns until the returned function is called.
func heavy() func() {
	corpusRuns <- struct{}{}
	return func() { <-corpusRuns }
}

// heavyFor holds one of corpusRuns until the test ends.
func heavyFor(t *testing.T) {
	t.Cleanup(heavy())
}
