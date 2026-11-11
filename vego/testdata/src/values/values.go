// Package values exercises errors, floats, and strings: values the verifier
// follows without knowing much, or anything, about their contents.
package values

import (
	"errors"
	"fmt"
	"os"
)

var errOutOfRange = errors.New("index out of range")

// ErrReassigned is not a reliable sentinel: reset assigns to it.
var ErrReassigned = errors.New("reassigned")

func reset() { ErrReassigned = nil }

// At returns the element at i, or an error when there is none.
func At(A []int, i int) (value int, err error) {
	if i < 0 || i >= len(A) {
		return 0, errOutOfRange
	}
	return A[i], nil
}

//@ Ensures err = nil <-> (0 <= i And i < |A|)
//@ Ensures err = nil -> value = A[i]

// First proves that the error cannot happen, so the panic is unreachable.
//
// @ Requires |A| > 0
func First(A []int) (value int) {
	value, err := At(A, 0)
	if err != nil {
		panic(err)
	}
	return value
}

//@ Ensures value = A[0]

// Unchecked panics on an error that can happen.
func Unchecked(A []int, i int) (value int) {
	value, err := At(A, i)
	if err != nil {
		panic(err) // want `vego:\ panic\ may\ be\ reachable`
	}
	return value
}

//@ Ensures value = A[i]

// Propagates hands the callee's error on.
func Propagates(A []int, i int) (double int, err error) {
	value, err := At(A, i)
	if err != nil {
		return 0, err
	}
	if value > 1000 || value < -1000 {
		return 0, fmt.Errorf("value %d is too large", value)
	}
	return 2 * value, nil
}

//@ Ensures err = nil -> (0 <= i And i < |A| And double = 2 * A[i])
//@ Ensures (0 <= i And i < |A| And -1000 <= A[i] And A[i] <= 1000) -> err = nil

// OnlySaysWhatSuccessMeans never says that it succeeds, so an implementation
// that always fails would meet its contract.
func OnlySaysWhatSuccessMeans(A []int, i int) (value int, err error) { // want `vego:\ the\ contract\ of\ OnlySaysWhatSuccessMeans\ would\ also\ be\ met\ by\ a\ function\ that\ always\ returns\ an\ error;\ state\ when\ it\ succeeds\ with\ a\ clause\ such\ as\ "condition\ \->\ err\ =\ nil",\ where\ the\ condition\ is\ about\ the\ inputs\ and\ some\ input\ satisfies\ it`
	if i < 0 || i >= len(A) {
		return 0, errOutOfRange
	}
	return A[i], nil
}

//@ Ensures err = nil -> value = A[i]

// NoPostcondition has the same problem with no postcondition at all.
//
// @ Requires i >= 0
func NoPostcondition(A []int, i int) (int, error) { // want `vego:\ the\ contract\ of\ NoPostcondition\ would\ also\ be\ met\ by\ a\ function\ that\ always\ returns\ an\ error;\ state\ when\ it\ succeeds\ with\ a\ clause\ such\ as\ "condition\ \->\ err\ =\ nil",\ where\ the\ condition\ is\ about\ the\ inputs\ and\ some\ input\ satisfies\ it`
	if i >= len(A) {
		return 0, errOutOfRange
	}
	return A[i], nil
}

// UnreliableSentinel cannot show that its error is non-nil.
func UnreliableSentinel(ok bool) (err error) {
	if !ok {
		return ErrReassigned // want `vego:\ cannot\ verify\ UnreliableSentinel:\ ErrReassigned\ is\ not\ a\ local\ variable\ of\ a\ supported\ type`
	}
	return nil
}

//@ Ensures err = nil <-> ok = True

// Size cannot say when it succeeds: that depends on the file system. It calls
// a function without a contract that returns an error, so it is excused.
func Size(path string) (size int, err error) {
	info, err := stat(path)
	if err != nil {
		return 0, err
	}
	if info < 0 {
		return 0, errOutOfRange
	}
	return info, nil
}

//@ Ensures err = nil -> size >= 0

func stat(path string) (int, error) {
	info, err := os.Stat(path)
	if err != nil {
		return 0, err
	}
	return int(info.Size()), nil
}

// DoubleSize is excused through Size.
func DoubleSize(path string) (size int, err error) {
	size, err = Size(path)
	if err != nil || size > 1000000 {
		return 0, errOutOfRange
	}
	return 2 * size, nil
}

//@ Ensures err = nil -> size >= 0

// Average shows opaque floats: the indexing and the integer arithmetic are
// proved, and nothing is known or claimed about the result.
//
// @ Requires |A| <= 1000 And Forall k in [0, |A|) : (0 <= A[k] And A[k] <= 1000)
func Average(A []int) float64 {
	sum := 0
	//@ Invariant 0 <= sum <= 1000 * i
	for i := range A {
		sum += A[i]
	}
	return float64(sum) / float64(len(A))
}

// Bucket indexes with a number computed from a float, which could be anything.
//
// @ Requires |counts| > 0
func Bucket(counts []int, ratio float64) int {
	bucket := int(ratio * float64(len(counts)))
	return counts[bucket] // want `vego:\ index\ may\ be\ negative` `vego:\ index\ may\ be\ out\ of\ range`
}

// CheckedBucket range-checks the number first.
//
// @ Requires |counts| > 0
func CheckedBucket(counts []int, ratio float64) int {
	bucket := int(ratio * float64(len(counts)))
	if bucket < 0 || bucket >= len(counts) {
		return 0
	}
	return counts[bucket]
}

// Scale stores floats in a slice; only its length is tracked.
//
// @ Modifies xs
func Scale(xs []float64, factor float64) {
	for i := range xs {
		xs[i] *= factor
	}
}

//@ Ensures |xs'| = |xs|

// Hot compares floats; either branch may be taken.
func Hot(celsius float64) (level int) {
	if celsius > 30.5 {
		return 2
	}
	return 1 // want `vego:\ postcondition\ may\ not\ hold:\ level\ =\ 2`
}

//@ Ensures level = 1 Or level = 2
//@ Ensures level = 2

// IsAdmin compares strings.
func IsAdmin(role string) (ok bool) {
	return role == "admin"
}

//@ Ensures ok = True <-> role = "admin"

// FirstByte reads a byte that exists.
//
// @ Requires |s| > 0
func FirstByte(s string) (b byte) {
	return s[0]
}

//@ Ensures b = s[0]

// LastByte reads past the end of an empty string.
func LastByte(s string) byte {
	//@ Assert |s| >= 0
	return s[len(s)-1] // want `vego:\ index\ may\ be\ negative`
}

// Greeting concatenates strings of bounded length.
//
// @ Requires |name| <= 100
func Greeting(name string) (text string) {
	return "hello, " + name
}

//@ Ensures |text| = |name| + 7
//@ Ensures text[0] = 104 And (|name| > 0 -> text[7] = name[0])

// Unbounded concatenates strings whose total length is not known to fit.
func Unbounded(a, b string) string {
	//@ Assert True
	return a + b // want `vego: the joined string may be more than can be allocated`
}

// Extension returns the last three bytes.
//
// @ Requires |name| >= 3
func Extension(name string) (ext string) {
	return name[len(name)-3:]
}

//@ Ensures |ext| = 3 And ext[2] = name[|name|-1]

// BadCut slices past the end.
func BadCut(name string) string {
	//@ Assert True
	return name[:3] // want `vego:\ substring\ bounds\ may\ be\ out\ of\ range`
}

// CountSpaces walks the bytes of a string.
func CountSpaces(s string) (n int) {
	//@ Invariant 0 <= n <= i <= |s|
	//@ Variant |s| - i
	for i := 0; i < len(s); i++ {
		if s[i] == ' ' {
			n++
		}
	}
	return n
}

//@ Ensures 0 <= n <= |s|

// CountChars walks the characters of a string, each one to four bytes long.
func CountChars(s string) (n int) {
	//@ Invariant 0 <= n <= i
	for i, r := range s {
		if r != ' ' && i >= 0 {
			n++
		}
	}
	return n // want `vego:\ postcondition\ may\ not\ hold:\ n\ =\ \|s\|`
}

//@ Ensures 0 <= n <= |s|
//@ Ensures n = |s|

// Reassigned may rebind a string parameter: the caller's string is its own.
func Reassigned(s string) (n int) {
	s = "ab"
	return len(s)
}

//@ Ensures n = 2

// Bytes copies a string into a slice that can then be changed freely.
//
// @ Requires |s| > 0
func Bytes(s string) (b []byte) {
	b = []byte(s)
	b[0] = 'x'
	return b
}

//@ Ensures |b| = |s| And b[0] = 120
//@ Ensures Forall k in [1, |s|) : b[k] = s[k]

// Before orders strings, which is not modelled.
func Before(a, b string) (less bool) {
	return a < b // want `vego:\ postcondition\ may\ not\ hold:\ less\ =\ True`
}

//@ Ensures less = True

// Classify switches on a string; a case matches when the strings are equal.
func Classify(role string) (level int) {
	switch role {
	case "admin":
		return 2
	case "user":
		return 1 // want `vego:\ postcondition\ may\ not\ hold:\ level\ !=\ 1`
	}
	return 0
}

//@ Ensures role = "admin" -> level = 2
//@ Ensures level = 2 -> role = "admin"
//@ Ensures level != 1

// SameFloat switches on a float. A float need not equal itself: NaN does not.
func SameFloat(f float64) (same bool) {
	switch f {
	case f:
		return true
	}
	return false // want `vego:\ postcondition\ may\ not\ hold:\ same\ =\ True`
}

//@ Ensures same = True

// Describe switches on an error.
func Describe(err error) (code int) {
	switch err {
	case nil:
		return 0
	case errOutOfRange: // want `vego:\ cannot\ verify\ Describe:\ comparing\ two\ errors\ can\ panic\ when\ they\ hold\ an\ uncomparable\ type;\ compare\ with\ nil,\ or\ use\ errors\.Is`
		return 1
	}
	return 2
}

//@ Ensures err = nil <-> code = 0
//@ Ensures code != 1

// Lookup has two unnamed results, called result1 and result2.
func Lookup(A []int, i int) (int, error) {
	if i < 0 || i >= len(A) {
		return 0, errOutOfRange
	}
	return A[i], nil
}

//@ Ensures result2 = nil <-> (0 <= i And i < |A|)
//@ Ensures result2 = nil -> result1 = A[i]

// Equal compares two errors, which panics when both hold the same
// uncomparable type.
func Equal(a, b error) (same bool) {
	return a == b // want `vego:\ cannot\ verify\ Equal:\ comparing\ two\ errors\ can\ panic\ when\ they\ hold\ an\ uncomparable\ type;\ compare\ with\ nil,\ or\ use\ errors\.Is`
}

//@ Ensures True

type numbers []int

func (n numbers) String() string {
	n[0] = 1
	return "n"
}

// Stale formats a value whose String method changes it.
//
// @ Requires |a| = 1 And a[0] = 0
func Stale(a numbers) int {
	_ = fmt.Errorf("%s", a) // want `vego:\ cannot\ verify\ Stale:\ formatting\ a\ value\ of\ type\ values\.numbers\ may\ call\ methods,\ which\ are\ not\ verified,\ or\ follow\ pointers`
	return a[0]
}

//@ Ensures result = 0

// Identity returns its parameter, which happens to be called nil.
func Identity(nil string) string {
	return nil // want `vego:\ postcondition\ may\ not\ hold:\ result\ =\ ""`
}

//@ Ensures result = ""

// UnreachableSource never reaches the call that would excuse it.
func UnreachableSource() error { // want `vego:\ the\ contract\ of\ UnreachableSource\ would\ also\ be\ met\ by\ a\ function\ that\ always\ returns\ an\ error;\ state\ when\ it\ succeeds\ with\ a\ clause\ such\ as\ "condition\ \->\ err\ =\ nil",\ where\ the\ condition\ is\ about\ the\ inputs\ and\ some\ input\ satisfies\ it`
	if false {
		_ = external()
	}
	return errors.New("always")
}

//@ Ensures True

func external() error { return nil }

// Pair is excused: nothing says when external succeeds.
func Pair() (error, error) {
	e := external()
	return e, e
}

//@ Ensures True

// Wrap inherits the excuse from Pair.
func Wrap() error {
	e, _ := Pair()
	return e
}

//@ Ensures True

// ConstrainsOtherResult pins the number down but never promises success.
func ConstrainsOtherResult() (int, error) { // want `vego:\ the\ contract\ of\ ConstrainsOtherResult\ would\ also\ be\ met\ by\ a\ function\ that\ always\ returns\ an\ error;\ state\ when\ it\ succeeds\ with\ a\ clause\ such\ as\ "condition\ \->\ err\ =\ nil",\ where\ the\ condition\ is\ about\ the\ inputs\ and\ some\ input\ satisfies\ it`
	return 1, errors.New("always")
}

//@ Ensures result1 = 1

// ImpossibleCondition promises success only when something impossible holds.
//
// @ Requires i >= 0
func ImpossibleCondition(i int) (err error) { // want `vego:\ the\ contract\ of\ ImpossibleCondition\ would\ also\ be\ met\ by\ a\ function\ that\ always\ returns\ an\ error;\ state\ when\ it\ succeeds\ with\ a\ clause\ such\ as\ "condition\ \->\ err\ =\ nil",\ where\ the\ condition\ is\ about\ the\ inputs\ and\ some\ input\ satisfies\ it`
	return errOutOfRange
}

//@ Ensures i < 0 -> err = nil

// DependsOnOutput makes success depend on what the function itself returns.
func DependsOnOutput(i int) (n int, err error) { // want `vego:\ the\ contract\ of\ DependsOnOutput\ would\ also\ be\ met\ by\ a\ function\ that\ always\ returns\ an\ error;\ state\ when\ it\ succeeds\ with\ a\ clause\ such\ as\ "condition\ \->\ err\ =\ nil",\ where\ the\ condition\ is\ about\ the\ inputs\ and\ some\ input\ satisfies\ it`
	return 1, errOutOfRange
}

//@ Ensures n = 0 -> err = nil

type failing []int

func (f failing) Error() string {
	f[0] = 1
	return "f"
}

func consume(e error) { _ = e.Error() }

// BoxedExplicitly hides a slice behind an error and formats it, which runs
// its Error method.
//
// @ Requires |a| = 1 And a[0] = 0
func BoxedExplicitly(a failing) int {
	_ = fmt.Errorf("%s", error(a)) // want `vego: cannot verify BoxedExplicitly: formatting error\(a\) would run the methods of an error whose origin is not known`
	return a[0]
}

//@ Ensures result = 0

// BoxedImplicitly does the same by passing the slice where an error is
// expected.
//
// @ Requires |a| = 1 And a[0] = 0
func BoxedImplicitly(a failing) int {
	consume(a) // want `vego:\ cannot\ verify\ BoxedImplicitly:\ converting\ a\ values\.failing\ to\ an\ error\ is\ not\ supported`
	return a[0]
}

//@ Ensures result = 0

func describe(error) string { return "" }

// GuardedSource never evaluates the call that would excuse it.
func GuardedSource() error { // want `vego:\ the\ contract\ of\ GuardedSource\ would\ also\ be\ met\ by\ a\ function\ that\ always\ returns\ an\ error;\ state\ when\ it\ succeeds\ with\ a\ clause\ such\ as\ "condition\ \->\ err\ =\ nil",\ where\ the\ condition\ is\ about\ the\ inputs\ and\ some\ input\ satisfies\ it`
	if false && len(describe(external())) > 0 {
		return nil
	}
	return errors.New("always")
}

//@ Ensures True

// NoSuchByte promises success for a byte value that does not exist.
//
// @ Requires |s| = 1
func NoSuchByte(s string) error { // want `vego:\ the\ contract\ of\ NoSuchByte\ would\ also\ be\ met\ by\ a\ function\ that\ always\ returns\ an\ error;\ state\ when\ it\ succeeds\ with\ a\ clause\ such\ as\ "condition\ \->\ err\ =\ nil",\ where\ the\ condition\ is\ about\ the\ inputs\ and\ some\ input\ satisfies\ it`
	_ = s[0]
	return errors.New("always")
}

//@ Ensures s[0] = 256 -> result = nil

// NoSuchSquare promises success for a number that is not a square.
func NoSuchSquare(x int) error { // want `vego:\ the\ contract\ of\ NoSuchSquare\ would\ also\ be\ met\ by\ a\ function\ that\ always\ returns\ an\ error;\ state\ when\ it\ succeeds\ with\ a\ clause\ such\ as\ "condition\ \->\ err\ =\ nil",\ where\ the\ condition\ is\ about\ the\ inputs\ and\ some\ input\ satisfies\ it`
	return errors.New("always") // want `vego:\ postcondition\ may\ not\ hold:\ x\*x\ =\ 2\ \->\ result\ =\ nil`
}

//@ Ensures x*x = 2 -> result = nil

// Alternating and its partner call each other and reach an unpredictable
// call; both are excused whichever is declared first.
//
// @ Requires 0 <= n <= 1
// @ Measure 2*n
func Alternating(n int) error {
	if n > 0 {
		return partner(n - 1)
	}
	return external()
}

//@ Ensures True

// @ Requires 0 <= n <= 1
// @ Measure 2*n+1
func partner(n int) error {
	return Alternating(n)
}

//@ Ensures True

// Circular and its partner only call each other, which excuses neither.
//
// @ Requires 0 <= n <= 1
// @ Measure 2*n
func Circular(n int) error { // want `vego:\ the\ contract\ of\ Circular\ would\ also\ be\ met\ by\ a\ function\ that\ always\ returns\ an\ error;\ state\ when\ it\ succeeds\ with\ a\ clause\ such\ as\ "condition\ \->\ err\ =\ nil",\ where\ the\ condition\ is\ about\ the\ inputs\ and\ some\ input\ satisfies\ it`
	if n > 0 {
		return circularPartner(n - 1)
	}
	return errOutOfRange
}

//@ Ensures True

// @ Requires 0 <= n <= 1
// @ Measure 2*n+1
func circularPartner(n int) error { // want `vego:\ the\ contract\ of\ circularPartner\ would\ also\ be\ met\ by\ a\ function\ that\ always\ returns\ an\ error;\ state\ when\ it\ succeeds\ with\ a\ clause\ such\ as\ "condition\ \->\ err\ =\ nil",\ where\ the\ condition\ is\ about\ the\ inputs\ and\ some\ input\ satisfies\ it`
	return Circular(n)
}

//@ Ensures True

// BlankParameters cannot name its parameters in an annotation, and its two
// blank parameters are different unknowns.
func BlankParameters(_ int8, _ int) error {
	return errors.New("always")
}

//@ Ensures _ > 127 -> result = nil // want `vego:\ in\ Ensures\ annotation:\ unknown\ name\ _`

// DistinctBlanks would verify if both blank parameters were one unknown.
func DistinctBlanks(_ int8, _ int) (n int) {
	return 0
}

//@ Ensures n = 0

// DeadSquareSource never reaches its unpredictable call: no input in range
// squares to two.
//
// @ Requires -2 <= x <= 2
func DeadSquareSource(x int) error { // want `vego:\ the\ contract\ of\ DeadSquareSource\ would\ also\ be\ met\ by\ a\ function\ that\ always\ returns\ an\ error;\ state\ when\ it\ succeeds\ with\ a\ clause\ such\ as\ "condition\ \->\ err\ =\ nil",\ where\ the\ condition\ is\ about\ the\ inputs\ and\ some\ input\ satisfies\ it`
	if x*x == 2 {
		_ = external()
	}
	return errors.New("always")
}

//@ Ensures True

// LiveSquareSource does reach it, for x = 2.
//
// @ Requires -2 <= x <= 2
func LiveSquareSource(x int) error {
	if x*x == 4 {
		return external()
	}
	return errors.New("not a root")
}

//@ Ensures True

// ExplicitResultName names its first result result2, which must not be
// taken for the second result.
func ExplicitResultName() (result2 int, _ int) {
	return 1, 0 // want `vego:\ postcondition\ may\ not\ hold:\ result2\ =\ 0`
}

//@ Ensures result2 = 0

// DiscardedValue hides an unreachable source behind an unrelated unknown.
//
// @ Requires -2 <= x <= 2
func DiscardedValue(x int) error { // want `vego:\ the\ contract\ of\ DiscardedValue\ would\ also\ be\ met\ by\ a\ function\ that\ always\ returns\ an\ error;\ state\ when\ it\ succeeds\ with\ a\ clause\ such\ as\ "condition\ \->\ err\ =\ nil",\ where\ the\ condition\ is\ about\ the\ inputs\ and\ some\ input\ satisfies\ it`
	_ = errors.New("discarded")
	if x*x == 2 {
		_ = external()
	}
	return errors.New("always")
}

//@ Ensures True

// MixedGuard joins the impossible condition on its input with a fact about
// an unknown value; the condition on the input is still necessary.
//
// @ Requires -2 <= x <= 2
func MixedGuard(x int) error { // want `vego:\ the\ contract\ of\ MixedGuard\ would\ also\ be\ met\ by\ a\ function\ that\ always\ returns\ an\ error;\ state\ when\ it\ succeeds\ with\ a\ clause\ such\ as\ "condition\ \->\ err\ =\ nil",\ where\ the\ condition\ is\ about\ the\ inputs\ and\ some\ input\ satisfies\ it`
	e := errors.New("known non-nil")
	if x*x == 2 && e != nil {
		_ = external()
	}
	return errors.New("always")
}

//@ Ensures True

// MixedGuardElse reaches the dead call through the negation of a
// disjunction.
//
// @ Requires -2 <= x <= 2
func MixedGuardElse(x int) error { // want `vego:\ the\ contract\ of\ MixedGuardElse\ would\ also\ be\ met\ by\ a\ function\ that\ always\ returns\ an\ error;\ state\ when\ it\ succeeds\ with\ a\ clause\ such\ as\ "condition\ \->\ err\ =\ nil",\ where\ the\ condition\ is\ about\ the\ inputs\ and\ some\ input\ satisfies\ it`
	e := errors.New("known non-nil")
	if x*x != 2 || e == nil {
		return errors.New("usual")
	}
	return external()
}

//@ Ensures True

// MixedGuardLive has a reachable call behind the same kind of guard.
//
// @ Requires -2 <= x <= 2
func MixedGuardLive(x int) error {
	e := errors.New("known non-nil")
	if x*x == 4 && e != nil {
		return external()
	}
	return e
}

//@ Ensures True

// ImpossibleString requires a string no program can pass, since a byte is
// never 256. The slice literal in its body must not be taken for such a
// string, so the call behind it does not excuse the contract.
//
// @ Requires |s| = 1 And s[0] = 256
func ImpossibleString(s string) error { // want `the contract of ImpossibleString would also be met by a function that always returns an error`
	_ = []int{256}
	_ = external()
	return errors.New("always")
}

//@ Ensures True

// WrapsOwn wraps an error it made itself.
//
// @ Requires x <= 1000
func WrapsOwn(x int) (err error) {
	if x < 0 {
		err = errors.New("negative")
		return fmt.Errorf("checking %d: %w", x, err)
	}
	return nil
}

//@ Ensures err = nil <-> x >= 0

// WrapsVerified wraps the error of a verified function, which only returns
// errors it made.
//
// @ Requires x <= 1000
func WrapsVerified(x int) (err error) {
	if err := WrapsOwn(x); err != nil {
		return fmt.Errorf("outer: %w", err)
	}
	return nil
}

//@ Ensures err = nil <-> x >= 0

// WrapsSentinel wraps an error variable of this package.
func WrapsSentinel(fail bool) error {
	if fail {
		return fmt.Errorf("wrapped: %w", errOutOfRange)
	}
	return nil
}

//@ Ensures result = nil <-> ~fail

// WrapsParameter formats an error from its caller, whose methods could do
// anything.
func WrapsParameter(e error) error {
	return fmt.Errorf("wrapped: %w", e) // want `vego: cannot verify WrapsParameter: formatting e would run the methods of an error whose origin is not known`
}

//@ Ensures result != nil

// WrapsTrusted formats the error of a function that is not verified.
func WrapsTrusted() error {
	err := external()
	if err != nil {
		return fmt.Errorf("external: %w", err) // want `vego: cannot verify WrapsTrusted: formatting err would run the methods of an error whose origin is not known`
	}
	return nil
}

//@ Ensures True

// passes hands its argument on, so what it returns is not of known origin.
func passes(e error) (err error) {
	return e
}

//@ Ensures (err = nil) <-> (e = nil)

// WrapsPassed formats an error that went through such a function.
func WrapsPassed() error {
	err := passes(errOutOfRange)
	return fmt.Errorf("passed: %w", err) // want `vego: cannot verify WrapsPassed: formatting err would run the methods of an error whose origin is not known`
}

//@ Ensures result != nil

// WrapsMixed assigns the variable it formats from a parameter on one path.
func WrapsMixed(e error, flag bool) error {
	err := errors.New("own")
	if flag {
		err = e
	}
	return fmt.Errorf("mixed: %v", err) // want `vego: cannot verify WrapsMixed: formatting err would run the methods of an error whose origin is not known`
}

//@ Ensures result != nil

// ReturnsParameter may hand back an error from outside without formatting
// it, and compare it with nil.
func ReturnsParameter(e error) (err error) {
	if e != nil {
		return e
	}
	return nil
}

//@ Ensures (err = nil) <-> (e = nil)

type boxed struct{ x int }

func (b *boxed) Error() string { return "boxed" }

// pair returns a pointer that is also an error, and a number.
func pair(p *boxed) (b *boxed, tag int) {
	return p, 0
}

//@ Ensures b = p And tag = 0

// TupleToError lets a call result become an error on the way out.
func TupleToError() (err error, tag int) {
	return pair(nil) // want `vego: cannot verify TupleToError: converting a \*values.boxed to a error is not supported here`
}

//@ Ensures err = nil And tag = 0

// TupleAssigned does the same in an assignment and then formats the error.
func TupleAssigned(p *boxed) int {
	var e error
	e, _ = pair(p) // want `vego: cannot verify TupleAssigned: converting a \*values.boxed to a error is not supported here`
	_ = fmt.Errorf("%s", e)
	return 0
}

//@ Ensures result = 0

// TupleDeclared does it in a declaration.
func TupleDeclared(p *boxed) int {
	var e, tag error = nil, nil
	_, _ = e, tag
	var f error
	var n int
	f, n = pair(p) // want `vego: cannot verify TupleDeclared: converting a \*values.boxed to a error is not supported here`
	_ = f
	return n
}

//@ Ensures result = 0

// SkippedBytes has a conversion that is never evaluated, of a string that
// could not exist. Nothing follows from it.
//
// @ Requires n = -1
func SkippedBytes(n int) int {
	_ = false && len([]byte(""[:n])) == 0
	return 1 // want `vego: postcondition may not hold: result = 0`
}

//@ Ensures result = 0

// GuardedBytes converts only when the string exists.
//
// @ Requires -1 <= n <= 0
func GuardedBytes(n int) bool {
	return n >= 0 && len([]byte(""[:n])) == 0
}

//@ Ensures result <-> n = 0
