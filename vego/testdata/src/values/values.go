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
//
// @Ensures err = nil <-> (0 <= i And i < |A|)
// @Ensures err = nil -> value = A[i]
func At(A []int, i int) (value int, err error) {
	if i < 0 || i >= len(A) {
		return 0, errOutOfRange
	}
	return A[i], nil
}

// First proves that the error cannot happen, so the panic is unreachable.
//
// @Requires |A| > 0
// @Ensures value = A[0]
func First(A []int) (value int) {
	value, err := At(A, 0)
	if err != nil {
		panic(err)
	}
	return value
}

// Unchecked panics on an error that can happen.
//
// @Ensures value = A[i]
func Unchecked(A []int, i int) (value int) {
	value, err := At(A, i)
	if err != nil {
		panic(err) // want `vego:\ panic\ may\ be\ reachable`
	}
	return value
}

// Propagates hands the callee's error on.
//
// @Ensures err = nil -> (0 <= i And i < |A| And double = 2 * A[i])
// @Ensures (0 <= i And i < |A| And -1000 <= A[i] And A[i] <= 1000) -> err = nil
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

// OnlySaysWhatSuccessMeans never says that it succeeds, so an implementation
// that always fails would meet its contract.
//
// @Ensures err = nil -> value = A[i]
func OnlySaysWhatSuccessMeans(A []int, i int) (value int, err error) { // want `vego:\ the\ contract\ of\ OnlySaysWhatSuccessMeans\ may\ also\ be\ met\ by\ a\ function\ that\ always\ returns\ an\ error:\ no\ simple\ input\ was\ found\ for\ which\ it\ forces\ success;\ state\ when\ it\ succeeds\ with\ a\ clause\ such\ as\ "condition\ \->\ err\ =\ nil",\ where\ the\ condition\ is\ about\ the\ inputs\ and\ a\ small\ input\ satisfies\ it`
	if i < 0 || i >= len(A) {
		return 0, errOutOfRange
	}
	return A[i], nil
}

// NoPostcondition has the same problem with no postcondition at all.
//
// @Requires i >= 0
func NoPostcondition(A []int, i int) (result1 int, result2 error) { // want `vego:\ the\ contract\ of\ NoPostcondition\ may\ also\ be\ met\ by\ a\ function\ that\ always\ returns\ an\ error:\ it\ requires\ success\ for\ no\ input;\ state\ when\ it\ succeeds\ with\ a\ clause\ such\ as\ "condition\ \->\ err\ =\ nil",\ where\ the\ condition\ is\ about\ the\ inputs`
	if i >= len(A) {
		return 0, errOutOfRange
	}
	return A[i], nil
}

// UnreliableSentinel cannot show that its error is non-nil.
//
// @Ensures err = nil <-> ok = True
func UnreliableSentinel(ok bool) (err error) {
	if !ok {
		return ErrReassigned // want `vego: cannot verify UnreliableSentinel: ErrReassigned is assigned at values.go:16, so it is not known to hold the error it was declared with`
	}
	return nil
}

// Size cannot say when it succeeds: that depends on the file system. It calls
// a function without a contract that returns an error, so it is excused.
//
// @Ensures err = nil -> size >= 0
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

func stat(path string) (int, error) {
	info, err := os.Stat(path)
	if err != nil {
		return 0, err
	}
	return int(info.Size()), nil
}

// DoubleSize is excused through Size.
//
// @Ensures err = nil -> size >= 0
func DoubleSize(path string) (size int, err error) {
	size, err = Size(path)
	if err != nil || size > 1000000 {
		return 0, errOutOfRange
	}
	return 2 * size, nil
}

// Average shows opaque floats: the indexing and the integer arithmetic are
// proved, and nothing is known or claimed about the result.
//
// @Requires |A| <= 1000 And Forall k in [0, |A|) : (0 <= A[k] And A[k] <= 1000)
func Average(A []int) (result float64) {
	sum := 0
	// @Invariant 0 <= sum <= 1000 * i
	for i := range A {
		sum += A[i]
	}
	return float64(sum) / float64(len(A))
}

// Bucket indexes with a number computed from a float, which could be anything.
//
// @Requires |counts| > 0
func Bucket(counts []int, ratio float64) (result int) {
	bucket := int(ratio * float64(len(counts)))
	return counts[bucket] // want `vego:\ index\ may\ be\ negative` `vego:\ index\ may\ be\ out\ of\ range`
}

// CheckedBucket range-checks the number first.
//
// @Requires |counts| > 0
func CheckedBucket(counts []int, ratio float64) (result int) {
	bucket := int(ratio * float64(len(counts)))
	if bucket < 0 || bucket >= len(counts) {
		return 0
	}
	return counts[bucket]
}

// Scale stores floats in a slice; only its length is tracked.
//
// @Modifies xs
// @Ensures |xs'| = |xs|
func Scale(xs []float64, factor float64) {
	for i := range xs {
		xs[i] *= factor
	}
}

// Hot compares floats; either branch may be taken.
//
// @Ensures level = 1 Or level = 2
// @Ensures level = 2
func Hot(celsius float64) (level int) {
	if celsius > 30.5 {
		return 2
	}
	return 1 // want `vego:\ postcondition\ may\ not\ hold:\ level\ =\ 2`
}

// IsAdmin compares strings.
//
// @Ensures ok = True <-> role = "admin"
func IsAdmin(role string) (ok bool) {
	return role == "admin"
}

// FirstByte reads a byte that exists.
//
// @Requires |s| > 0
// @Ensures b = s[0]
func FirstByte(s string) (b byte) {
	return s[0]
}

// LastByte reads past the end of an empty string.
func LastByte(s string) (result byte) {
	// @Assert |s| >= 0
	return s[len(s)-1] // want `vego:\ index\ may\ be\ negative`
}

// Greeting concatenates strings of bounded length.
//
// @Requires |name| <= 100
// @Ensures |text| = |name| + 7
// @Ensures text[0] = 104 And (|name| > 0 -> text[7] = name[0])
func Greeting(name string) (text string) {
	return "hello, " + name
}

// Unbounded concatenates strings whose total length is not known to fit.
func Unbounded(a, b string) (result string) {
	// @Assert True
	return a + b // want `vego: the joined string may be more than can be allocated`
}

// Extension returns the last three bytes.
//
// @Requires |name| >= 3
// @Ensures |ext| = 3 And ext[2] = name[|name|-1]
func Extension(name string) (ext string) {
	return name[len(name)-3:]
}

// BadCut slices past the end.
func BadCut(name string) (result string) {
	// @Assert True
	return name[:3] // want `vego:\ substring\ bounds\ may\ be\ out\ of\ range`
}

// CountSpaces walks the bytes of a string.
//
// @Ensures 0 <= n <= |s|
func CountSpaces(s string) (n int) {
	// @Invariant 0 <= n <= i <= |s|
	// @Variant |s| - i
	for i := 0; i < len(s); i++ {
		if s[i] == ' ' {
			n++
		}
	}
	return n
}

// CountChars walks the characters of a string, each one to four bytes long.
//
// @Ensures 0 <= n <= |s|
// @Ensures n = |s|
func CountChars(s string) (n int) {
	// @Invariant 0 <= n <= i
	for i, r := range s {
		if r != ' ' && i >= 0 {
			n++
		}
	}
	return n // want `vego:\ postcondition\ may\ not\ hold:\ n\ =\ \|s\|`
}

// Reassigned may rebind a string parameter: the caller's string is its own.
//
// @Ensures n = 2
func Reassigned(s string) (n int) {
	s = "ab"
	return len(s)
}

// Bytes copies a string into a slice that can then be changed freely.
//
// @Requires |s| > 0
// @Ensures |b| = |s| And b[0] = 120
// @Ensures Forall k in [1, |s|) : b[k] = s[k]
func Bytes(s string) (b []byte) {
	b = []byte(s)
	b[0] = 'x'
	return b
}

// Before orders strings, which is not modelled.
//
// @Ensures less = True
func Before(a, b string) (less bool) {
	return a < b // want `vego:\ postcondition\ may\ not\ hold:\ less\ =\ True`
}

// Classify switches on a string; a case matches when the strings are equal.
//
// @Ensures role = "admin" -> level = 2
// @Ensures level = 2 -> role = "admin"
// @Ensures level != 1
func Classify(role string) (level int) {
	switch role {
	case "admin":
		return 2
	case "user":
		return 1 // want `vego:\ postcondition\ may\ not\ hold:\ level\ !=\ 1`
	}
	return 0
}

// SameFloat switches on a float. A float need not equal itself: NaN does not.
//
// @Ensures same = True
func SameFloat(f float64) (same bool) {
	switch f {
	case f:
		return true
	}
	return false // want `vego:\ postcondition\ may\ not\ hold:\ same\ =\ True`
}

// Describe switches on an error. A case may be a sentinel, which is a
// pointer, so that == cannot panic.
//
// @Ensures err = nil <-> code = 0
// @Ensures err = errOutOfRange <-> code = 1
func Describe(err error) (code int) {
	switch err {
	case nil:
		return 0
	case errOutOfRange:
		return 1
	}
	return 2
}

// DescribeWrongly claims that the case of the sentinel is never taken.
//
// @Ensures code != 1
func DescribeWrongly(err error) (code int) {
	switch err {
	case errOutOfRange:
		return 1 // want `vego: postcondition may not hold: code != 1`
	}
	return 2
}

// DescribeOther switches on an error with a case that is another error of
// which nothing is known.
//
// @Ensures True
func DescribeOther(err, other error) (code int) {
	switch err {
	case other: // want `vego: cannot verify DescribeOther: comparing two errors can panic when both hold the same uncomparable type; one of them must be nil, an error made by errors.New or fmt.Errorf or vouched for by a trusted contract, or a package-level error variable that holds such an error or a pointer, integer, string, or boolean, or an array or struct of these`
		return 1
	}
	return 2
}

// Lookup has two results.
//
// @Ensures result2 = nil <-> (0 <= i And i < |A|)
// @Ensures result2 = nil -> result1 = A[i]
func Lookup(A []int, i int) (result1 int, result2 error) {
	if i < 0 || i >= len(A) {
		return 0, errOutOfRange
	}
	return A[i], nil
}

// Equal compares two errors, which panics when both hold the same
// uncomparable type.
//
// @Ensures True
func Equal(a, b error) (same bool) {
	return a == b // want `vego: cannot verify Equal: comparing two errors can panic when both hold the same uncomparable type; one of them must be nil`
}

type numbers []int

func (n numbers) String() string {
	n[0] = 1
	return "n"
}

// Stale formats a value whose String method changes it.
//
// @Requires |a| = 1 And a[0] = 0
// @Ensures result = 0
func Stale(a numbers) (result int) {
	_ = fmt.Errorf("%s", a) // want `vego:\ cannot\ verify\ Stale:\ fmt\.Errorf\ formats\ a,\ and\ fmt\ would\ call\ \(values\.numbers\)\.String,\ which\ has\ no\ contract`
	return a[0]
}

// Identity returns its parameter, which happens to be called nil.
//
// @Ensures result = ""
func Identity(nil string) (result string) {
	return nil // want `vego:\ postcondition\ may\ not\ hold:\ result\ =\ ""`
}

// UnreachableSource never reaches the call that would excuse it.
//
// @Ensures True
func UnreachableSource() (result error) { // want `vego:\ the\ contract\ of\ UnreachableSource\ may\ also\ be\ met\ by\ a\ function\ that\ always\ returns\ an\ error:\ it\ requires\ success\ for\ no\ input;\ state\ when\ it\ succeeds\ with\ a\ clause\ such\ as\ "condition\ \->\ err\ =\ nil",\ where\ the\ condition\ is\ about\ the\ inputs`
	if false {
		_ = external()
	}
	return errors.New("always")
}

func external() error { return nil }

// Pair is excused: nothing says when external succeeds.
//
// @Ensures True
func Pair() (result1 error, result2 error) {
	e := external()
	return e, e
}

// Wrap inherits the excuse from Pair.
//
// @Ensures True
func Wrap() (result error) {
	e, _ := Pair()
	return e
}

// ConstrainsOtherResult pins the number down but never promises success.
//
// @Ensures result1 = 1
func ConstrainsOtherResult() (result1 int, result2 error) { // want `vego:\ the\ contract\ of\ ConstrainsOtherResult\ may\ also\ be\ met\ by\ a\ function\ that\ always\ returns\ an\ error:\ it\ requires\ success\ for\ no\ input;\ state\ when\ it\ succeeds\ with\ a\ clause\ such\ as\ "condition\ \->\ err\ =\ nil",\ where\ the\ condition\ is\ about\ the\ inputs`
	return 1, errors.New("always")
}

// ImpossibleCondition promises success only when something impossible holds.
//
// @Requires i >= 0
// @Ensures i < 0 -> err = nil
func ImpossibleCondition(i int) (err error) { // want `vego:\ the\ contract\ of\ ImpossibleCondition\ may\ also\ be\ met\ by\ a\ function\ that\ always\ returns\ an\ error:\ it\ requires\ success\ for\ no\ input;\ state\ when\ it\ succeeds\ with\ a\ clause\ such\ as\ "condition\ \->\ err\ =\ nil",\ where\ the\ condition\ is\ about\ the\ inputs`
	return errOutOfRange
}

// DependsOnOutput makes success depend on what the function itself returns.
//
// @Ensures n = 0 -> err = nil
func DependsOnOutput(i int) (n int, err error) { // want `vego:\ the\ contract\ of\ DependsOnOutput\ may\ also\ be\ met\ by\ a\ function\ that\ always\ returns\ an\ error:\ it\ requires\ success\ for\ no\ input;\ state\ when\ it\ succeeds\ with\ a\ clause\ such\ as\ "condition\ \->\ err\ =\ nil",\ where\ the\ condition\ is\ about\ the\ inputs`
	return 1, errOutOfRange
}

type failing []int

func (f failing) Error() string {
	f[0] = 1
	return "f"
}

func consume(e error) { _ = e.Error() }

// BoxedExplicitly hides a slice behind an error and formats it, which runs
// its Error method.
//
// @Requires |a| = 1 And a[0] = 0
// @Ensures result = 0
func BoxedExplicitly(a failing) (result int) {
	_ = fmt.Errorf("%s", error(a)) // want `vego: cannot verify BoxedExplicitly: formatting error\(a\) would run the methods of an error whose origin is not known`
	return a[0]
}

// BoxedImplicitly does the same by passing the slice where an error is
// expected.
//
// @Requires |a| = 1 And a[0] = 0
// @Ensures result = 0
func BoxedImplicitly(a failing) (result int) {
	consume(a) // want `vego:\ cannot\ verify\ BoxedImplicitly:\ converting\ a\ values\.failing\ to\ an\ error\ is\ not\ supported`
	return a[0]
}

func describe(e error) string { return "" }

// GuardedSource never evaluates the call that would excuse it.
//
// @Ensures True
func GuardedSource() (result error) { // want `vego:\ the\ contract\ of\ GuardedSource\ may\ also\ be\ met\ by\ a\ function\ that\ always\ returns\ an\ error:\ it\ requires\ success\ for\ no\ input;\ state\ when\ it\ succeeds\ with\ a\ clause\ such\ as\ "condition\ \->\ err\ =\ nil",\ where\ the\ condition\ is\ about\ the\ inputs`
	if false && len(describe(external())) > 0 {
		return nil
	}
	return errors.New("always")
}

// NoSuchByte promises success for a byte value that does not exist.
//
// @Requires |s| = 1
// @Ensures s[0] = 256 -> result = nil
func NoSuchByte(s string) (result error) { // want `vego:\ the\ contract\ of\ NoSuchByte\ may\ also\ be\ met\ by\ a\ function\ that\ always\ returns\ an\ error:\ it\ requires\ success\ for\ no\ input;\ state\ when\ it\ succeeds\ with\ a\ clause\ such\ as\ "condition\ \->\ err\ =\ nil",\ where\ the\ condition\ is\ about\ the\ inputs`
	_ = s[0]
	return errors.New("always")
}

// NoSuchSquare promises success for a number that is not a square.
//
// @Ensures x*x = 2 -> result = nil
func NoSuchSquare(x int) (result error) { // want `vego:\ the\ contract\ of\ NoSuchSquare\ may\ also\ be\ met\ by\ a\ function\ that\ always\ returns\ an\ error:\ it\ requires\ success\ for\ no\ input;\ state\ when\ it\ succeeds\ with\ a\ clause\ such\ as\ "condition\ \->\ err\ =\ nil",\ where\ the\ condition\ is\ about\ the\ inputs`
	return errors.New("always")
}

// Alternating and its partner call each other and reach an unpredictable
// call; both are excused whichever is declared first.
//
// @Requires 0 <= n <= 1
// @Variant 2*n
// @Ensures True
func Alternating(n int) (result error) {
	if n > 0 {
		return partner(n - 1)
	}
	return external()
}

// @Requires 0 <= n <= 1
// @Variant 2*n+1
// @Ensures True
func partner(n int) (result error) {
	return Alternating(n)
}

// Circular and its partner only call each other, which excuses neither.
//
// @Requires 0 <= n <= 1
// @Variant 2*n
// @Ensures True
func Circular(n int) (result error) { // want `vego:\ the\ contract\ of\ Circular\ may\ also\ be\ met\ by\ a\ function\ that\ always\ returns\ an\ error:\ it\ requires\ success\ for\ no\ input;\ state\ when\ it\ succeeds\ with\ a\ clause\ such\ as\ "condition\ \->\ err\ =\ nil",\ where\ the\ condition\ is\ about\ the\ inputs`
	if n > 0 {
		return circularPartner(n - 1)
	}
	return errOutOfRange
}

// @Requires 0 <= n <= 1
// @Variant 2*n+1
// @Ensures True
func circularPartner(n int) (result error) { // want `vego:\ the\ contract\ of\ circularPartner\ may\ also\ be\ met\ by\ a\ function\ that\ always\ returns\ an\ error:\ it\ requires\ success\ for\ no\ input;\ state\ when\ it\ succeeds\ with\ a\ clause\ such\ as\ "condition\ \->\ err\ =\ nil",\ where\ the\ condition\ is\ about\ the\ inputs`
	return Circular(n)
}

// BlankParameters cannot name its parameters in an annotation, and its two
// blank parameters are different unknowns.
//
// @Ensures _ > 127 -> result = nil // want `vego:\ in\ Ensures\ annotation:\ unknown\ name\ _`
func BlankParameters(_ int8, _ int) (result error) {
	return errors.New("always")
}

// DistinctBlanks would verify if both blank parameters were one unknown.
//
// @Ensures n = 0
func DistinctBlanks(_ int8, _ int) (n int) {
	return 0
}

// DeadSquareSource never reaches its unpredictable call: no input in range
// squares to two.
//
// @Requires -2 <= x <= 2
// @Ensures True
func DeadSquareSource(x int) (result error) { // want `vego:\ the\ contract\ of\ DeadSquareSource\ may\ also\ be\ met\ by\ a\ function\ that\ always\ returns\ an\ error:\ it\ requires\ success\ for\ no\ input;\ state\ when\ it\ succeeds\ with\ a\ clause\ such\ as\ "condition\ \->\ err\ =\ nil",\ where\ the\ condition\ is\ about\ the\ inputs`
	if x*x == 2 {
		_ = external()
	}
	return errors.New("always")
}

// LiveSquareSource does reach it, for x = 2.
//
// @Requires -2 <= x <= 2
// @Ensures True
func LiveSquareSource(x int) (result error) {
	if x*x == 4 {
		return external()
	}
	return errors.New("not a root")
}

// BlankResult names one of its results and leaves the other blank, which
// leaves a contract no name for it.
//
// @Ensures first = 1
func BlankResult() (first int, _ int) { // want `vego: BlankResult has annotations, so each of its results needs a name, as in func BlankResult\(...\) \(n int, err error\)`
	return 1, 0
}

// DiscardedValue hides an unreachable source behind an unrelated unknown.
//
// @Requires -2 <= x <= 2
// @Ensures True
func DiscardedValue(x int) (result error) { // want `vego:\ the\ contract\ of\ DiscardedValue\ may\ also\ be\ met\ by\ a\ function\ that\ always\ returns\ an\ error:\ it\ requires\ success\ for\ no\ input;\ state\ when\ it\ succeeds\ with\ a\ clause\ such\ as\ "condition\ \->\ err\ =\ nil",\ where\ the\ condition\ is\ about\ the\ inputs`
	_ = errors.New("discarded")
	if x*x == 2 {
		_ = external()
	}
	return errors.New("always")
}

// MixedGuard joins the impossible condition on its input with a fact about
// an unknown value; the condition on the input is still necessary.
//
// @Requires -2 <= x <= 2
// @Ensures True
func MixedGuard(x int) (result error) { // want `vego:\ the\ contract\ of\ MixedGuard\ may\ also\ be\ met\ by\ a\ function\ that\ always\ returns\ an\ error:\ it\ requires\ success\ for\ no\ input;\ state\ when\ it\ succeeds\ with\ a\ clause\ such\ as\ "condition\ \->\ err\ =\ nil",\ where\ the\ condition\ is\ about\ the\ inputs`
	e := errors.New("known non-nil")
	if x*x == 2 && e != nil {
		_ = external()
	}
	return errors.New("always")
}

// MixedGuardElse reaches the dead call through the negation of a
// disjunction.
//
// @Requires -2 <= x <= 2
// @Ensures True
func MixedGuardElse(x int) (result error) { // want `vego:\ the\ contract\ of\ MixedGuardElse\ may\ also\ be\ met\ by\ a\ function\ that\ always\ returns\ an\ error:\ it\ requires\ success\ for\ no\ input;\ state\ when\ it\ succeeds\ with\ a\ clause\ such\ as\ "condition\ \->\ err\ =\ nil",\ where\ the\ condition\ is\ about\ the\ inputs`
	e := errors.New("known non-nil")
	if x*x != 2 || e == nil {
		return errors.New("usual")
	}
	return external()
}

// MixedGuardLive has a reachable call behind the same kind of guard.
//
// @Requires -2 <= x <= 2
// @Ensures True
func MixedGuardLive(x int) (result error) {
	e := errors.New("known non-nil")
	if x*x == 4 && e != nil {
		return external()
	}
	return e
}

// ImpossibleString requires a string no program can pass, since a byte is
// never 256. The slice literal in its body must not be taken for such a
// string, so the call behind it does not excuse the contract.
//
// @Requires |s| = 1 And s[0] = 256
// @Ensures True
func ImpossibleString(s string) (result error) { // want `the contract of ImpossibleString may also be met by a function that always returns an error`
	_ = []int{256}
	_ = external()
	return errors.New("always")
}

// WrapsOwn wraps an error it made itself.
//
// @Requires x <= 1000
// @Ensures err = nil <-> x >= 0
func WrapsOwn(x int) (err error) {
	if x < 0 {
		err = errors.New("negative")
		return fmt.Errorf("checking %d: %w", x, err)
	}
	return nil
}

// WrapsVerified wraps the error of a verified function, which only returns
// errors it made.
//
// @Requires x <= 1000
// @Ensures err = nil <-> x >= 0
func WrapsVerified(x int) (err error) {
	if err := WrapsOwn(x); err != nil {
		return fmt.Errorf("outer: %w", err)
	}
	return nil
}

// WrapsSentinel wraps an error variable of this package.
//
// @Ensures result = nil <-> ~fail
func WrapsSentinel(fail bool) (result error) {
	if fail {
		return fmt.Errorf("wrapped: %w", errOutOfRange)
	}
	return nil
}

// WrapsParameter formats an error from its caller, whose methods could do
// anything.
//
// @Ensures result != nil
func WrapsParameter(e error) (result error) {
	return fmt.Errorf("wrapped: %w", e) // want `vego: cannot verify WrapsParameter: formatting e would run the methods of an error whose origin is not known`
}

// WrapsTrusted formats the error of a function that is not verified.
//
// @Ensures True
func WrapsTrusted() (result error) {
	err := external()
	if err != nil {
		return fmt.Errorf("external: %w", err) // want `vego: cannot verify WrapsTrusted: formatting err would run the methods of an error whose origin is not known`
	}
	return nil
}

// passes hands its argument on, so what it returns is not of known origin.
//
// @Ensures (err = nil) <-> (e = nil)
func passes(e error) (err error) {
	return e
}

// WrapsPassed formats an error that went through such a function.
//
// @Ensures result != nil
func WrapsPassed() (result error) {
	err := passes(errOutOfRange)
	return fmt.Errorf("passed: %w", err) // want `vego: cannot verify WrapsPassed: formatting err would run the methods of an error whose origin is not known`
}

// WrapsMixed assigns the variable it formats from a parameter on one path.
//
// @Ensures result != nil
func WrapsMixed(e error, flag bool) (result error) {
	err := errors.New("own")
	if flag {
		err = e
	}
	return fmt.Errorf("mixed: %v", err) // want `vego: cannot verify WrapsMixed: formatting err would run the methods of an error whose origin is not known`
}

// ReturnsParameter may hand back an error from outside without formatting
// it, and compare it with nil.
//
// @Ensures (err = nil) <-> (e = nil)
func ReturnsParameter(e error) (err error) {
	if e != nil {
		return e
	}
	return nil
}

type boxed struct{ x int }

func (b *boxed) Error() string { return "boxed" }

// pair returns a pointer that is also an error, and a number.
//
// @Ensures b = p And tag = 0
func pair(p *boxed) (b *boxed, tag int) {
	return p, 0
}

// TupleToError lets a call result become an error on the way out.
//
// @Ensures err = nil And tag = 0
func TupleToError() (err error, tag int) {
	return pair(nil) // want `vego: cannot verify TupleToError: converting a \*values.boxed to a error is not supported here`
}

// TupleAssigned does the same in an assignment and then formats the error.
//
// @Ensures result = 0
func TupleAssigned(p *boxed) (result int) {
	var e error
	e, _ = pair(p) // want `vego: cannot verify TupleAssigned: converting a \*values.boxed to a error is not supported here`
	_ = fmt.Errorf("%s", e)
	return 0
}

// TupleDeclared does it in a declaration.
//
// @Ensures result = 0
func TupleDeclared(p *boxed) (result int) {
	var e, tag error = nil, nil
	_, _ = e, tag
	var f error
	var n int
	f, n = pair(p) // want `vego: cannot verify TupleDeclared: converting a \*values.boxed to a error is not supported here`
	_ = f
	return n
}

// SkippedBytes has a conversion that is never evaluated, of a string that
// could not exist. Nothing follows from it.
//
// @Requires n = -1
// @Ensures result = 0
func SkippedBytes(n int) (result int) {
	_ = false && len([]byte(""[:n])) == 0
	return 1 // want `vego: postcondition may not hold: result = 0`
}

// GuardedBytes converts only when the string exists.
//
// @Requires -1 <= n <= 0
// @Ensures result <-> n = 0
func GuardedBytes(n int) (result bool) {
	return n >= 0 && len([]byte(""[:n])) == 0
}

// SameFloats claims two slices of floats are equal, which no annotation can
// say: nothing is known of a float.
//
// @Ensures result = A // want `vego: in Ensures annotation: operator = cannot be applied to .* values`
func SameFloats(A []float64) (result []float64) {
	return A
}

// SameFloatCount says what can be said of them.
//
// @Ensures |result| = |A|
func SameFloatCount(A []float64) (result []float64) {
	return A
}

// PtrCmp compares a pointer whose type has an Error method with an error.
//
// @Requires t != nil
// @Ensures True
func PtrCmp(t *ptrError, err error) (b bool) {
	return t == err // want `vego: cannot verify PtrCmp: comparing an error with a value of type \*values.ptrError is not supported`
}

type ptrError struct{ code int }

func (p *ptrError) Error() string { return "pointer" }
