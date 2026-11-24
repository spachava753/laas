package typederrors

import "sync"

// Locked holds a mutex by value, and so does an error of its type; taking
// it out of an error copies the mutex (S3 of F33).
type Locked struct {
	mu sync.Mutex
	n  int
}

// @Ensures True
func (l Locked) Error() (s string) { return "locked" } // want `the receiver l has type Locked, which holds a sync.Mutex, and passing it copies the value`

// @Ensures True
func CopyOut(err error) (n int) {
	if l, ok := err.(Locked); ok { // want `the type assertion err.\(Locked\) copies what err holds, a value of type Locked, which holds a sync.Mutex; hold a pointer to it in the error instead`
		return l.n
	}
	return 0
}

// @Ensures True
func CopyCase(err error) (n int) {
	switch l := err.(type) {
	case Locked: // want `the case Locked of the type switch copies what the operand holds, a value of type Locked, which holds a sync.Mutex`
		return l.n
	}
	return 0
}
