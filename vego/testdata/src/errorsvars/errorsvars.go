// Package errorsvars reads error variables that are not made by errors.New
// or fmt.Errorf: aliases of other variables, which hold what those hold,
// and opaque ones, which hold one error of which little or nothing is known.
package errorsvars

import (
	"context"
	"errors"
	"fmt"
	"io"
	"io/fs"
	"math"
	"os"

	"sentinellib"
)

var ErrMine = errors.New("mine")

// Aliases: a variable named by the initialiser, or returned by a function
// of this package whose whole body is that return.
var (
	ErrAlias   = ErrMine
	ErrEOF     = io.EOF
	ErrMissing = errMissing()
	ErrChain   = ErrMissing
)

func errMissing() error { return ErrMine }

// Not aliases: a function that returns its named result, one that takes
// an argument, and one with more than the return in its body.
var (
	ErrNamed = named()
	ErrID    = id(ErrMine)
	ErrTwo   = two()
)

func named() (ErrMine error) { return ErrMine }

func id(e error) error { return e }

func two() error {
	e := ErrMine
	return e
}

// Opaque variables whose initialiser has a concrete type, which makes them
// not nil.
type codeErr struct{ code int }

func (codeErr) Error() string { return "code" }

type ptrErr struct{ items []int }

func (*ptrErr) Error() string { return "ptr" }

type sliceErr []int

func (sliceErr) Error() string { return "slice" }

type nanErr float64

func (nanErr) Error() string { return "nan" }

type floatField struct{ f float64 }

func (floatField) Error() string { return "float" }

var (
	ErrCode       error = codeErr{1}
	ErrPtr        error = &ptrErr{}
	ErrNilPtr     error = (*ptrErr)(nil)
	ErrSlice      error = sliceErr{1}
	ErrSlice2     error = sliceErr{2}
	ErrNaN        error = nanErr(math.NaN())
	ErrFloatField error = floatField{1}
)

// Opaque variables that may be nil.
var (
	ErrA       error = nil
	ErrD, ErrE error = nil, codeErr{2}
	ErrF, ErrG error = pair()
	ErrNone    error
)

func pair() (error, *ptrErr) { return nil, nil }

// ErrFallback holds a variable that its package assigns, so it holds the
// value that variable had when ErrFallback was initialised.
var ErrFallback = sentinellib.ErrChanged

// ErrWrapsCtx wraps an error of which nothing is known.
var ErrWrapsCtx = fmt.Errorf("w: %w", context.DeadlineExceeded)

// ErrWrapsNotExist wraps os.ErrNotExist, which holds a sentinel.
var ErrWrapsNotExist = fmt.Errorf("w: %w", os.ErrNotExist)

// ErrAddr has its address taken below.
var ErrAddr = errors.New("addr")

func addr() *error { return &ErrAddr }

// AliasSame compares an alias with what it holds.
//
// @Ensures same
func AliasSame() (same bool) {
	return ErrAlias == ErrMine && ErrEOF == io.EOF && ErrMissing == ErrMine && ErrChain == ErrMine
}

// AliasNamed says the same in a contract.
//
// @Ensures ErrAlias = ErrMine And ErrMissing = ErrMine And ErrEOF = io.EOF
func AliasNamed() {}

// NotExistSame compares two names of one error of another package.
//
// @Ensures same
// @Ensures differ
func NotExistSame() (same, differ bool) {
	return os.ErrNotExist == fs.ErrNotExist, os.ErrNotExist != nil && os.ErrNotExist != io.EOF && fs.ErrPermission != os.ErrNotExist
}

// NotExistDiffers claims the two names are two errors.
//
// @Ensures ~same
func NotExistDiffers() (same bool) {
	return os.ErrNotExist == fs.ErrNotExist // want `vego: postcondition may not hold: ~same`
}

// NamedSame cannot tell whether a variable that is not an alias holds
// ErrMine.
//
// @Ensures same
func NamedSame() (same bool) {
	return ErrNamed == ErrMine // want `vego: postcondition may not hold: same`
}

// NamedDiffers cannot tell either.
//
// @Ensures ~same
func NamedDiffers() (same bool) {
	return ErrNamed == ErrMine // want `vego: postcondition may not hold: ~same`
}

// IDDiffers claims a value passed through a function differs from what it
// was given.
//
// @Ensures ~same
func IDDiffers() (same bool) {
	return ErrID == ErrMine // want `vego: postcondition may not hold: ~same`
}

// TwoDiffers claims the same of a function with two statements.
//
// @Ensures ~same
func TwoDiffers() (same bool) {
	return ErrTwo == ErrMine // want `vego: postcondition may not hold: ~same`
}

// Concrete reads opaque variables whose initialisers have concrete types.
//
// @Ensures r
func Concrete() (r bool) {
	return ErrCode != nil && ErrPtr != nil && ErrNilPtr != nil && ErrE != nil && ErrG != nil && ErrSlice != nil && ErrNaN != nil &&
		context.DeadlineExceeded != nil
}

// NilA cannot show that a variable initialised with nil is not nil.
//
// @Ensures r
func NilA() (r bool) {
	return ErrA != nil // want `vego: postcondition may not hold: r`
}

// NilD cannot either, for one of two names.
//
// @Ensures r
func NilD() (r bool) {
	return ErrD != nil // want `vego: postcondition may not hold: r`
}

// NilF cannot, for the result of a call that has type error.
//
// @Ensures r
func NilF() (r bool) {
	return ErrF != nil // want `vego: postcondition may not hold: r`
}

// NilNone cannot, for a variable without an initialiser.
//
// @Ensures r
func NilNone() (r bool) {
	return ErrNone != nil // want `vego: postcondition may not hold: r`
}

// NilFallback cannot, for an alias of a variable its package assigns.
//
// @Ensures r
func NilFallback() (r bool) {
	return ErrFallback != nil // want `vego: postcondition may not hold: r`
}

// FallbackIs compares that alias with an error of known origin.
//
// @Ensures True
func FallbackIs() (same bool) {
	return ErrFallback == ErrMine
}

// SameCode compares an error of which nothing is known with an opaque
// variable whose type makes == identity.
//
// @Ensures True
func SameCode(e error) (code, ptr, late bool) {
	return e == ErrCode, e == ErrPtr, e == context.DeadlineExceeded
}

// SameSlice compares it with one whose type is a slice.
//
// @Ensures True
func SameSlice(e error) (same bool) {
	return e == ErrSlice // want `vego: cannot verify SameSlice: comparing two errors can panic when both hold the same uncomparable type`
}

// TwoSlices compares two such variables.
//
// @Ensures True
func TwoSlices() (same bool) {
	return ErrSlice == ErrSlice2 // want `vego: cannot verify TwoSlices: comparing two errors can panic when both hold the same uncomparable type`
}

// SelfNaN compares a NaN with itself, which Go reports as different.
//
// @Ensures same
func SelfNaN() (same bool) {
	return ErrNaN == ErrNaN // want `vego: cannot verify SelfNaN: comparing two errors can panic when both hold the same uncomparable type`
}

// SameFloatField compares one whose type holds a float.
//
// @Ensures True
func SameFloatField(e error) (same bool) {
	return e == ErrFloatField // want `vego: cannot verify SameFloatField: comparing two errors can panic when both hold the same uncomparable type`
}

// SameNamed compares with one whose type is not known.
//
// @Ensures True
func SameNamed(e error) (same bool) {
	return e == ErrNamed // want `vego: cannot verify SameNamed: comparing two errors can panic when both hold the same uncomparable type`
}

// FormatsCode formats an opaque variable.
//
// @Ensures err != nil
func FormatsCode() (err error) {
	return fmt.Errorf("x: %w", ErrCode) // want `vego: cannot verify FormatsCode: formatting ErrCode would run the methods of an error whose origin is not known; only an error made by errors.New or fmt.Errorf, here or in a verified function, or one that a contract vouches for, can be formatted; ErrCode is not initialised with errors.New or fmt.Errorf, so nothing is known of its methods`
}

// FormatsNotExist formats os.ErrNotExist, which holds a sentinel.
//
// @Ensures err != nil
func FormatsNotExist() (err error) { // want `the contract of FormatsNotExist may also be met by a function that always returns an error`
	return fmt.Errorf("x: %w", os.ErrNotExist)
}

// SearchesCtx asks errors.Is about an opaque variable.
//
// @Ensures True
func SearchesCtx() (found bool) {
	return errors.Is(context.DeadlineExceeded, ErrMine) // want `vego: cannot verify SearchesCtx: errors.Is would run the Is and Unwrap methods of context.DeadlineExceeded, an error whose origin is not known`
}

// SearchesWrapsCtx asks it about a sentinel that wraps one.
//
// @Ensures True
func SearchesWrapsCtx() (found bool) {
	return errors.Is(ErrWrapsCtx, ErrMine) // want `vego: cannot verify SearchesWrapsCtx: errors.Is would run the Is and Unwrap methods of ErrWrapsCtx, an error whose origin is not known`
}

// FormatsWrapsCtx formats that sentinel.
//
// @Ensures err != nil
func FormatsWrapsCtx() (err error) {
	return fmt.Errorf("x: %w", ErrWrapsCtx) // want `vego: cannot verify FormatsWrapsCtx: formatting ErrWrapsCtx would run the methods of an error whose origin is not known`
}

// FindsNotExist searches a sentinel that wraps os.ErrNotExist.
//
// @Ensures found
func FindsNotExist() (found bool) {
	return errors.Is(ErrWrapsNotExist, fs.ErrNotExist)
}

// NewDiffers searches a new error for an opaque target: a new error is a
// new allocation, which no variable held before.
//
// @Ensures ~found
func NewDiffers() (found bool) {
	return errors.Is(fmt.Errorf("x"), context.DeadlineExceeded)
}

// NewDiffersFromNamed says the same of a target whose type is not known.
//
// @Ensures ~found
func NewDiffersFromNamed() (found bool) {
	return errors.Is(errors.New("x"), ErrNamed)
}

// Late says which error it returns, naming an opaque variable.
//
// @Ensures err = nil <-> ~late
// @Ensures err = context.DeadlineExceeded <-> late
func Late(late bool) (err error) {
	if late {
		return context.DeadlineExceeded
	}
	return nil
}

// LateNamed claims an opaque variable that may be nil is returned only when
// late.
//
// @Ensures err = nil <-> ~late
// @Ensures err = ErrNamed <-> late
func LateNamed(late bool) (err error) {
	if late {
		return ErrNamed // want `vego: postcondition may not hold: err = nil <-> ~late`
	}
	return nil // want `vego: postcondition may not hold: err = ErrNamed <-> late`
}

// Addressed reads a variable whose address is taken.
//
// @Ensures err != nil
func Addressed() (err error) {
	return ErrAddr // want `vego: cannot verify Addressed: ErrAddr has its address taken at errorsvars.go:\d+, so it is not known to hold the error it was declared with`
}

// Changed reads a variable of another package that its package assigns.
//
// @Ensures err != nil
func Changed() (err error) {
	return sentinellib.ErrChanged // want `vego: cannot verify Changed: sentinellib.ErrChanged is assigned at sentinellib.go:\d+ in package sentinellib, so it is not known to hold the error it was declared with`
}
