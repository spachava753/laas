// Package trust exercises calls to functions that are not verified: every
// such call needs a trusted contract, from the project's file or from the
// ones shipped with vego.
package trust

import (
	"errors"
	"math/rand"
	"os"
	"sort"
	"strings"
)

func helper(x int) int { return x + 1 }

// CallsWithoutContract calls a function that is neither verified nor trusted.
//
// @Ensures y = x + 1
func CallsWithoutContract(x int) (y int) {
	return helper(x) // want `vego:\ cannot\ verify\ CallsWithoutContract:\ it\ calls\ helper,\ which\ has\ no\ contract;\ annotate\ helper\ with\ // @\ annotations\ so\ that\ it\ is\ verified,\ or\ add\ a\ trusted\ contract\ for\ trust\.helper\ to\ vego\-trusted\.yaml`
}

// CallsStandardLibrary calls a standard-library function vego ships no
// contract for.
//
// @Ensures n >= 0
func CallsStandardLibrary() (n int) {
	return os.Getpid() // want `vego:\ cannot\ verify\ CallsStandardLibrary:\ it\ calls\ Getpid,\ which\ has\ no\ contract;\ annotate\ Getpid\ with\ // @\ annotations\ so\ that\ it\ is\ verified,\ or\ add\ a\ trusted\ contract\ for\ os\.Getpid\ to\ vego\-trusted\.yaml`
}

func readConfig(path string) (size int, err error) {
	info, err := os.Stat(path)
	if err != nil {
		return 0, err
	}
	return int(info.Size()), nil
}

// ConfigSize relies on the trusted contract of readConfig. Nothing says when
// readConfig succeeds, so ConfigSize is not asked to promise success either.
//
// @Ensures err = nil -> size >= 0
func ConfigSize(path string) (size int, err error) {
	size, err = readConfig(path)
	if err != nil {
		return 0, err
	}
	return size, nil
}

func parsePort(n int) (port int, err error) {
	if n < 0 || n > 65535 {
		return 0, os.ErrInvalid
	}
	return n, nil
}

// Port relies on a trusted contract that does say when the callee succeeds,
// so it has to say when it succeeds itself.
//
// @Ensures err = nil -> port = n
func Port(n int) (port int, err error) { // want `vego:\ the\ contract\ of\ Port\ may\ also\ be\ met\ by\ a\ function\ that\ always\ returns\ an\ error:\ it\ requires\ success\ for\ no\ input;\ state\ when\ it\ succeeds\ with\ a\ clause\ such\ as\ "condition\ \->\ err\ =\ nil",\ where\ the\ condition\ is\ about\ the\ inputs`
	return parsePort(n)
}

// PortExactly does.
//
// @Ensures 0 <= n <= 65535 -> err = nil
// @Ensures err = nil -> port = n
func PortExactly(n int) (port int, err error) {
	return parsePort(n)
}

func fill(dst []int, value int) {
	for i := range dst {
		dst[i] = value
	}
}

func readOnly(src []int) int { return len(src) }

// Filled uses what the trusted contract says about the slice afterwards.
//
// @Requires |A| > 0
// @Modifies A
// @Ensures first = 7
func Filled(A []int) (first int) {
	fill(A, 7)
	return A[0]
}

// Untouched keeps what it knew about a slice that a trusted function does
// not list under modifies.
//
// @Requires |A| > 0 And A[0] = 3
// @Ensures first = 3
func Untouched(A []int) (first int) {
	n := readOnly(A)
	if n < 0 {
		return 0
	}
	return A[0]
}

func contradictory() int { return 0 }

// UsesContradiction would prove anything from a contract that cannot hold.
//
// @Ensures n = 42
func UsesContradiction() (n int) {
	return contradictory() // want `vego:\ the\ trusted\ contract\ of\ trust\.contradictory\ \(trusted\.yaml:\d+\)\ cannot\ be\ used:\ it\ contradicts\ itself,\ so\ anything\ could\ be\ proved\ from\ it`
}

func wrongModifies(count int) {}

// UsesWrongModifies relies on a contract whose modifies makes no sense.
func UsesWrongModifies() {
	// @Assert True
	wrongModifies(1) // want `vego:\ the\ trusted\ contract\ of\ trust\.wrongModifies\ \(trusted\.yaml:\d+\)\ cannot\ be\ used:\ in\ its\ modifies\ \"count\":\ count\ is\ passed\ by\ value,\ so\ the\ caller\ cannot\ see\ a\ change\ to\ it`
}

func wrongName(count int) int { return count }

// UsesWrongName relies on a contract that names something that is not there.
//
// @Ensures n >= 0
func UsesWrongName() (n int) {
	return wrongName(1) // want `vego:\ the\ trusted\ contract\ of\ trust\.wrongName\ \(trusted\.yaml:\d+\)\ cannot\ be\ used:\ in\ its\ ensures\ "total\ >=\ 0":\ unknown\ name\ total`
}

func makesSlice() []int { return nil }

// UsesTrustedSlice gets a slice from a trusted function. Nothing is known of
// the slice but what every slice guarantees.
//
// @Ensures n >= 0
func UsesTrustedSlice() (n int) {
	s := makesSlice()
	return len(s)
}

// ReadsTrustedSlice assumes the slice has an element.
//
// @Ensures n >= 0
func ReadsTrustedSlice() (n int) {
	s := makesSlice()
	return s[0] // want `vego: index may be out of range` `vego: postcondition may not hold: n >= 0`
}

// Verified has annotations and a trusted contract.
//
// @Ensures result = 0
func Verified() (result int) { // want `vego:\ Verified\ has\ annotations\ and\ a\ trusted\ contract;\ a\ function\ is\ either\ verified\ or\ trusted,\ not\ both`
	return 0
}

// Sorted relies on the shipped contract of sort.Ints.
//
// @Requires |A| >= 2
// @Modifies A
// @Ensures ordered = True
func Sorted(A []int) (ordered bool) {
	sort.Ints(A)
	return A[0] <= A[1]
}

// Roll relies on the shipped contract of rand.Intn.
//
// @Ensures 1 <= face <= 6
func Roll() (face int) {
	return rand.Intn(6) + 1
}

// RollZero breaks the precondition that contract states.
func RollZero() (result int) {
	// @Assert True
	return rand.Intn(0) // want `vego:\ precondition\ of\ Intn\ may\ not\ hold:\ n\ >\ 0`
}

// Scheme relies on the shipped contract of strings.HasPrefix.
//
// @Ensures secure = True -> (|url| >= 8 And url[0] = 104)
func Scheme(url string) (secure bool) {
	return strings.HasPrefix(url, "https://")
}

// Overridden calls a function whose shipped contract the project file
// replaces with one that says nothing.
//
// @Requires |A| = 0
// @Ensures ok = True
func Overridden(A []int) (ok bool) {
	return sort.IntsAreSorted(A) // want `vego:\ postcondition\ may\ not\ hold:\ ok\ =\ True`
}

// MaxInt here must not replace the limit that the shipped contract of
// strings.Repeat speaks of.
const MaxInt = 1 << 100

const realMax = int(^uint(0) >> 1)

// HugeRepeat asks for a string longer than any string can be.
//
// @Requires n > realMax/2
// @Ensures False
func HugeRepeat(n int) (result string) {
	return strings.Repeat("xx", n) // want `precondition of Repeat may not hold: \|s\| \* count <= MaxAlloc`
}

// @Predicate good(n) ::= n = 1

func usesPredicate() int { return 0 }

// UsesPredicate relies on a trusted contract that mentions a predicate,
// which would mean something different in every package.
//
// @Ensures n = 1
func UsesPredicate() (n int) {
	return usesPredicate() // want `the trusted contract of trust.usesPredicate \(trusted.yaml:\d+\) cannot be used: in its ensures "good\(result\)": unknown predicate good`
}

func impossibleString() string { return "a" }

// UsesImpossibleString relies on a contract no string can satisfy.
//
// @Ensures False
func UsesImpossibleString() (b byte) {
	s := impossibleString() // want `the trusted contract of trust.impossibleString \(trusted.yaml:\d+\) cannot be used: it contradicts itself`
	return s[0]
}

func take(MaxInt any) int { return 0 }

// UsesBlockedName relies on a contract that mentions a parameter of a type
// vego does not model; the name must not turn into the integer limit.
//
// @Ensures n = MaxInt
func UsesBlockedName() (n int) {
	return take(nil) // want `the trusted contract of trust.take \(trusted.yaml:\d+\) cannot be used: in its ensures "result = MaxInt": cannot compare result \(int\) with MaxInt \(interface value\)`
}

var errAlways = errors.New("always")

func ready() (value *int, err error) { return nil, nil }

// AlwaysFailsAfterReady calls a trusted function that is guaranteed to
// succeed, so it has no excuse for failing every time.
//
// @Ensures True
func AlwaysFailsAfterReady() (result error) { // want `the contract of AlwaysFailsAfterReady may also be met by a function that always returns an error`
	_, _ = ready()
	return errAlways
}

func takeAny(x any) int { return 0 }

// UsesOldOfBlockedName relies on a contract that takes old of a parameter
// vego does not model.
//
// @Ensures n = 0
func UsesOldOfBlockedName() (n int) {
	return takeAny(nil) // want `the trusted contract of trust.takeAny \(trusted.yaml:\d+\) cannot be used: in its ensures "result = old\(x\)": cannot compare result \(int\) with old\(x\) \(interface value\)`
}

func readyWith(a []int) (err error) { return nil }

func readyWriting(a []int) (err error) { return nil }

// AlwaysFailsAfterReadyWith calls a trusted function whose success follows
// from the slice it leaves unchanged.
//
// @Requires |a| = 1 And a[0] = 0
// @Ensures True
func AlwaysFailsAfterReadyWith(a []int) (result error) { // want `the contract of AlwaysFailsAfterReadyWith may also be met by a function that always returns an error`
	_ = readyWith(a)
	return errAlways
}

// AlwaysFailsAfterReadyWriting calls one whose success follows from the
// length of a slice it may write, which a call cannot change.
//
// @Requires |a| = 1
// @Modifies a
// @Ensures True
func AlwaysFailsAfterReadyWriting(a []int) (result error) { // want `the contract of AlwaysFailsAfterReadyWriting may also be met by a function that always returns an error`
	_ = readyWriting(a)
	return errAlways
}

func readyByte() (value uint8, err error) { return 0, nil }

// AlwaysFailsAfterReadyByte calls a trusted function whose success is
// guarded by a condition on its own result that the result's type makes
// true.
//
// @Ensures True
func AlwaysFailsAfterReadyByte() (result error) { // want `the contract of AlwaysFailsAfterReadyByte may also be met by a function that always returns an error`
	_, _ = readyByte()
	return errAlways
}

func maybeSigned() (value int8, err error) { return -1, errAlways }

// MayFailAfterSigned calls one whose guard really depends on its result, so
// nothing says when it succeeds.
//
// @Ensures True
func MayFailAfterSigned() (result error) {
	_, err := maybeSigned()
	return err
}

func readyAtLeast(n int) (value uint8, err error) { return 0, nil }

// AlwaysFailsAfterReadyAtLeast calls a trusted function whose guard holds
// for every byte once the argument is zero.
//
// @Ensures True
func AlwaysFailsAfterReadyAtLeast() (result error) { // want `the contract of AlwaysFailsAfterReadyAtLeast may also be met by a function that always returns an error`
	_, _ = readyAtLeast(0)
	return errAlways
}

func readyBytes(a []byte) (err error) { return nil }

// AlwaysFailsAfterReadyBytes calls one whose guard is about an element of a
// slice it may write; the element is a byte whatever it writes.
//
// @Requires |a| = 1
// @Modifies a
// @Ensures True
func AlwaysFailsAfterReadyBytes(a []byte) (result error) { // want `the contract of AlwaysFailsAfterReadyBytes may also be met by a function that always returns an error`
	_ = readyBytes(a)
	return errAlways
}

func readyNil(e error) (err error) { return nil }

// AlwaysFailsAfterReadyNil calls a trusted function that succeeds on every
// call its contract admits.
//
// @Ensures True
func AlwaysFailsAfterReadyNil() (result error) { // want `the contract of AlwaysFailsAfterReadyNil may also be met by a function that always returns an error`
	_ = readyNil(nil)
	return errAlways
}

func readyLinked() (value uint8, err error) { return 0, nil }

// AlwaysFailsAfterReadyLinked calls one whose success follows from two
// postconditions together.
//
// @Ensures True
func AlwaysFailsAfterReadyLinked() (result error) { // want `the contract of AlwaysFailsAfterReadyLinked may also be met by a function that always returns an error`
	_, _ = readyLinked()
	return errAlways
}

// PassThrough succeeds for the nil error it requires.
//
// @Requires e = nil
// @Ensures err = nil
func PassThrough(e error) (err error) {
	return e
}

// OnlyA succeeds for the one string it requires.
//
// @Requires s = "a"
// @Ensures err = nil
func OnlyA(s string) (err error) {
	return nil
}

// Contrapositive states its success condition the other way round.
//
// @Ensures err != nil -> n < 0
func Contrapositive(n int) (err error) {
	if n < 0 {
		return errAlways
	}
	return nil
}

// readySixtyFive is excused: it reaches an unpredictable call, and the
// search for a witness does not try strings of 65 bytes.
//
// @Ensures |s| = 65 -> result = nil
func readySixtyFive(s string) (result error) {
	if err := external(); err != nil && len(s) != 65 {
		return err
	}
	return nil
}

func external() error { return nil }

// AlwaysFailsAfterSixtyFive calls it with a string for which its contract
// does guarantee success.
//
// @Ensures True
func AlwaysFailsAfterSixtyFive() (result error) { // want `the contract of AlwaysFailsAfterSixtyFive may also be met by a function that always returns an error`
	_ = readySixtyFive("01234567890123456789012345678901234567890123456789012345678901234")
	return errAlways
}

func writesSixtyFive(a []byte) (err error) {
	a[0] = 255
	return nil
}

// AlwaysFailsAfterWriting calls a trusted function whose success follows
// from the type of an element it writes.
//
// @Ensures True
func AlwaysFailsAfterWriting() (result error) { // want `the contract of AlwaysFailsAfterWriting may also be met by a function that always returns an error`
	a := make([]byte, 65)
	_ = writesSixtyFive(a)
	return errAlways
}

// ImpossibleLiteral promises success for a slice that cannot exist: an int8
// cannot hold the byte 128.
//
// @Ensures a = "\x80" -> result = nil
func ImpossibleLiteral(a []int8) (result error) { // want `the contract of ImpossibleLiteral may also be met by a function that always returns an error`
	if len(a) == 1 {
		_ = a[0]
	}
	return errAlways
}

// PossibleLiteral promises it for one that can.
//
// @Ensures a = "\x7f" -> result = nil
func PossibleLiteral(a []int8) (result error) {
	if len(a) == 1 && a[0] == 127 {
		return nil
	}
	return errAlways
}

func readsSixtyFive(a []byte) (err error) { return nil }

// SixtyFive returns a slice of 65 bytes.
//
// @Ensures |result| = 65
func SixtyFive() (result []byte) {
	return make([]byte, 65)
}

// AlwaysFailsAfterReading calls a trusted function whose success follows
// from the type of an element of a slice it only reads, which nothing here
// has read before.
//
// @Ensures True
func AlwaysFailsAfterReading() (result error) { // want `the contract of AlwaysFailsAfterReading may also be met by a function that always returns an error`
	a := SixtyFive()
	_ = readsSixtyFive(a)
	return errAlways
}

// HugeRepeat asks for a string longer than any allocation, which panics.
//
// @Ensures result = 42
func RepeatBeyondMemory() (result int) {
	s := strings.Repeat("ab", 1<<50) // want `vego: precondition of Repeat may not hold: \|s\| \* count <= MaxAlloc`
	return len(s)
}

// SmallRepeat stays under the limit.
//
// @Requires 0 <= n <= 1000
// @Ensures result = 2*n
func SmallRepeat(n int) (result int) {
	s := strings.Repeat("ab", n)
	return len(s)
}

func claimsNegative(n int) {}

// ContradictedHere calls a function whose contract cannot be true of the
// argument it passes.
//
// @Ensures result = 42
func ContradictedHere() (result int) {
	claimsNegative(5) // want `vego: the trusted contract of claimsNegative cannot be true of this call: what it promises contradicts what is known here`
	return 0
}

// NotContradicted passes an argument the contract can be true of.
//
// @Ensures result = 0
func NotContradicted() (result int) {
	claimsNegative(-5)
	return 0
}

// DeadContradiction calls it on a path that is never taken.
//
// @Requires n < 0
// @Ensures result = 0
func DeadContradiction(n int) (result int) {
	if n > 0 {
		claimsNegative(5)
	}
	return 0
}

func claimsChange(xs []int) {}

// UsesClaimsChange relies on a contract that says memory changed which it
// does not list.
//
// @Requires |xs| > 0 And xs[0] = 1
// @Ensures xs'[0] = 99
func UsesClaimsChange(xs []int) {
	claimsChange(xs) // want `vego: the trusted contract of trust.claimsChange \(trusted.yaml:\d+\) cannot be used: its ensures "xs'\[0\] = 7" describes xs'\[0\] after the call, but nothing its modifies lists is memory that xs'\[0\] reads, so the call cannot have changed it; drop the prime or list what the function writes`
}

// Bounced calls a trusted function of this package that calls it back, so
// the two never return.
//
// @Requires n >= 0
// @Ensures result = 0
func Bounced(n int) (result int) {
	return bounce(n) // want `vego: bounce is trusted and calls back into Bounced, so that this call ends cannot be proved; verify bounce instead of trusting it`
}

func bounce(n int) int { return Bounced(n) }

// IgnoresFailure calls a function that may fail, ignores whether it did,
// and then fails for a reason of its own. The call does not excuse it.
//
// @Ensures err = nil -> result = x + 1
func IgnoresFailure(x int) (result int, err error) { // want `the contract of IgnoresFailure may also be met by a function that always returns an error`
	_ = external()
	return 0, errAlways
}

// PassesFailure fails when the call does, and is excused.
//
// @Ensures err = nil -> result = x
func PassesFailure(x int) (result int, err error) {
	if err := external(); err != nil {
		return 0, errAlways
	}
	return x, nil
}

// LoopsOverFailures keeps the first failure of several calls.
//
// @Requires 0 <= n <= 10
// @Ensures True
func LoopsOverFailures(n int) (err error) {
	var first error
	// @Invariant 0 <= i <= n
	// @Variant n - i
	for i := 0; i < n; i++ {
		if failed := external(); failed != nil && first == nil {
			first = failed
		}
	}
	return first
}

// box holds a number.
type box struct{ X int }

func setThrough(p, q *box) { p.X = 1 }

// SeenThroughOther relies on a contract that describes, through one
// parameter, what the function writes through another that is the same.
//
// @Requires p != nil
// @Modifies p
// @Ensures result = 1
func SeenThroughOther(p *box) (result int) {
	setThrough(p, p)
	return p.X
}

// never returns false; its contract says less.
//
// @Ensures result -> (Forall k in [0, |s|) : s[k] < 0)
func never(s []byte) (result bool) { return false }

func nonnegative(s []byte) {}

// NeverTaken calls a trusted function on a path that cannot be taken,
// which only shows once the types of the bytes are taken into account. The
// contract of the function is not to blame for that.
//
// @Requires |s| = 1
// @Ensures result = 0
func NeverTaken(s []byte) (result int) {
	if never(s) {
		nonnegative(s)
	}
	return 0
}

// parent points to a child.
type parent struct{ Child *box }

func orphan(p *parent) { p.Child = nil }

// Orphans relies on a contract that says what a pointer field is after the
// call.
//
// @Requires p != nil
// @Modifies p
// @Ensures result
func Orphans(p *parent) (result bool) {
	orphan(p)
	return p.Child == nil
}

func allNonnegative(s []byte) {}

// NeverTakenAll is NeverTaken with a promise about every byte.
//
// @Requires |s| = 1
// @Ensures result = 0
func NeverTakenAll(s []byte) (result int) {
	if never(s) {
		allNonnegative(s)
	}
	return 0
}

func pair() (int, error) { return 0, nil }

// UsesNumberOnly uses the number a call returned in arithmetic, which adds
// facts about it but chooses no path, and then fails on its own.
//
// @Ensures True
func UsesNumberOnly() (result error) { // want `the contract of UsesNumberOnly may also be met by a function that always returns an error`
	n, _ := pair()
	_ = n / 2
	return errAlways
}

// KeepsFailure puts the error of a call into memory and returns it from
// there.
//
// @Ensures True
func KeepsFailure() (result error) {
	err := external()
	saved := []error{err}
	return saved[0]
}

// KeepsOtherFailure puts the error of a call into memory next to an error
// of its own, and returns its own.
//
// @Ensures True
func KeepsOtherFailure() (result error) { // want `the contract of KeepsOtherFailure may also be met by a function that always returns an error`
	err := external()
	saved := []error{err, errAlways}
	return saved[1]
}

// BranchesOnOwnError keeps the error of a call in memory next to an error
// of its own, and decides by its own.
//
// @Ensures True
func BranchesOnOwnError() (result error) { // want `the contract of BranchesOnOwnError may also be met by a function that always returns an error`
	err := external()
	saved := []error{err, errAlways}
	if saved[1] != nil {
		return errAlways
	}
	return nil
}

// BranchesOnKeptError decides by the error of the call, read back from
// memory.
//
// @Ensures True
func BranchesOnKeptError() (result error) {
	err := external()
	saved := []error{err, errAlways}
	if saved[0] != nil {
		return errAlways
	}
	return nil
}

func bytePair() (byte, error) { return 0, nil }

// BranchesOnAnyByte branches on something every byte satisfies, so the
// call decides nothing.
//
// @Ensures True
func BranchesOnAnyByte() (result error) { // want `the contract of BranchesOnAnyByte may also be met by a function that always returns an error`
	b, _ := bytePair()
	if b >= 0 {
		return errAlways
	}
	return nil
}

// BranchesOnSomeBytes branches on something the call decides.
//
// @Ensures True
func BranchesOnSomeBytes() (result error) {
	b, _ := bytePair()
	if b >= 7 {
		return errAlways
	}
	return nil
}

// hasFailed says whether an error is one.
//
// @Ensures result <-> e != nil
func hasFailed(e error) (result bool) { return e != nil }

// AsksHelper lets a verified function say whether the call failed.
//
// @Ensures True
func AsksHelper() (result error) {
	err := external()
	if hasFailed(err) {
		return errAlways
	}
	return nil
}

// AsksHelperAboutOwn asks it about an error of its own.
//
// @Ensures True
func AsksHelperAboutOwn() (result error) { // want `the contract of AsksHelperAboutOwn may also be met by a function that always returns an error`
	_ = external()
	if hasFailed(errAlways) {
		return errAlways
	}
	return nil
}

// translate makes an error of its own of any error.
//
// @Ensures result = nil <-> e = nil
func translate(e error) (result error) {
	if e != nil {
		return errAlways
	}
	return nil
}

// Translates returns what a verified function makes of the call's error.
//
// @Ensures True
func Translates() (result error) {
	return translate(external())
}

// LoopsWithOwnError calls a function that may fail inside a loop that also
// assigns an error of its own, which is what it returns.
//
// @Requires 0 <= n <= 10
// @Ensures True
func LoopsWithOwnError(n int) (result error) { // want `the contract of LoopsWithOwnError may also be met by a function that always returns an error`
	err := errAlways
	// @Invariant 0 <= i <= n
	// @Invariant err != nil
	// @Variant n - i
	for i := 0; i < n; i++ {
		_ = external()
		err = errAlways
	}
	return err
}

// ForwardsThroughLoops keeps the error of a call made in one loop in a
// variable that a second loop copies.
//
// @Requires 1 <= n <= 3 And 1 <= m <= 3
// @Ensures True
func ForwardsThroughLoops(n, m int) (result error) {
	var a, b error
	// @Invariant 0 <= i <= n
	// @Variant n - i
	for i := 0; i < n; i++ {
		a = external()
	}
	// @Invariant 0 <= j <= m
	// @Variant m - j
	for j := 0; j < m; j++ {
		b = a
	}
	return b
}

// SavesBeforeSecondLoop keeps an error of its own that one loop leaves in a
// variable, before a second loop puts the error of a call into the same
// variable.
//
// @Requires 1 <= n <= 3 And 1 <= m <= 3
// @Ensures True
func SavesBeforeSecondLoop(n, m int) (result error) { // want `the contract of SavesBeforeSecondLoop may also be met by a function that always returns an error`
	err := errAlways
	// @Invariant 0 <= i <= n And err != nil
	// @Variant n - i
	for i := 0; i < n; i++ {
		err = errAlways
	}
	saved := err
	// @Invariant 0 <= j <= m
	// @Variant m - j
	for j := 0; j < m; j++ {
		err = external()
	}
	return saved
}

// AsksHelperAfterLoop asks a verified function about the error a loop left.
//
// @Requires 1 <= n <= 3
// @Ensures True
func AsksHelperAfterLoop(n int) (result error) {
	var err error
	// @Invariant 0 <= i <= n
	// @Variant n - i
	for i := 0; i < n; i++ {
		err = external()
	}
	if hasFailed(err) {
		return errAlways
	}
	return nil
}

// AsksHelperInLoop keeps the answer of the verified function instead.
//
// @Requires 1 <= n <= 3
// @Ensures True
func AsksHelperInLoop(n int) (result error) {
	var failed bool
	// @Invariant 0 <= i <= n
	// @Variant n - i
	for i := 0; i < n; i++ {
		failed = hasFailed(external())
	}
	if failed {
		return errAlways
	}
	return nil
}

// AsksOnBothPaths asks a verified function about the error on both sides of
// a test of it, and passes the error on.
//
// @Ensures True
func AsksOnBothPaths() (result error) {
	err := external()
	if err != nil {
		_ = hasFailed(err)
		return err
	}
	_ = hasFailed(err)
	return nil
}

// onFailure is called with an error that is one.
//
// @Requires e != nil
// @Ensures e != nil
func onFailure(e error) {}

// onSuccess is called with no error.
//
// @Requires e = nil
// @Ensures e = nil
func onSuccess(e error) {}

// ReportsBothWays calls a different verified function on each side of a
// test of the error, each of which says which side it is on.
//
// @Ensures True
func ReportsBothWays() (result error) {
	err := external()
	if err != nil {
		onFailure(err)
		return err
	}
	onSuccess(err)
	return nil
}

func alwaysError(b byte) error { return errAlways }

// CopiesByteInLoop passes on, through a loop, a byte that a call returned,
// to a function that fails for every byte.
//
// @Requires 1 <= n <= 3
// @Ensures True
func CopiesByteInLoop(n int) (result error) { // want `the contract of CopiesByteInLoop may also be met by a function that always returns an error`
	b, _ := bytePair()
	var saved byte
	// @Invariant 0 <= i <= n
	// @Variant n - i
	for i := 0; i < n; i++ {
		saved = b
	}
	return alwaysError(saved)
}

// NotesFailureInLoop remembers, in a number, that a call in a loop failed.
// The number it stores does not depend on the call; that it is stored does.
//
// @Requires 1 <= n <= 3
// @Ensures True
func NotesFailureInLoop(n int) (result error) {
	last := -1
	// @Invariant 0 <= i <= n And -1 <= last < n
	// @Variant n - i
	for i := 0; i < n; i++ {
		if failed := external(); failed != nil {
			last = i
		}
	}
	if last >= 0 {
		return errAlways
	}
	return nil
}

// FailsEitherWay branches on what a call returned and fails on both sides.
//
// @Ensures err = nil -> result = x + 1
func FailsEitherWay(x int) (result int, err error) { // want `the contract of FailsEitherWay may also be met by a function that always returns an error`
	n, _ := pair()
	if n > 5 {
		return 0, errAlways
	}
	return 0, errOther
}

var errOther = errors.New("other")

// FailsAfterPassingOn passes the error of a call on, and fails on its own
// when there is none.
//
// @Ensures err = nil -> result = x + 1
func FailsAfterPassingOn(x int) (result int, err error) { // want `the contract of FailsAfterPassingOn may also be met by a function that always returns an error`
	_, err = pair()
	if err != nil {
		return 0, err
	}
	return 0, errAlways
}

func step(i int) error { return nil }

// FirstSuccessWins tries several times and gives up when every try failed.
//
// @Requires 1 <= n
// @Ensures True
func FirstSuccessWins(n int) (err error) {
	// @Invariant 0 <= i <= n
	// @Variant n - i
	for i := 0; i < n; i++ {
		if step(i) == nil {
			return nil
		}
	}
	return errAlways
}

func setting() string { return "" }

// NeedsSetting fails when something from outside that is not an error is
// missing.
//
// @Ensures err = nil -> |value| > 0
func NeedsSetting() (value string, err error) {
	v := setting()
	if len(v) == 0 {
		return "", errAlways
	}
	return v, nil
}

// BouncedByValue calls a trusted function of this package that calls it
// back through a function value.
//
// @Requires n >= 0
// @Ensures result = 0
func BouncedByValue(n int) (result int) {
	return bounceByValue(n) // want `vego: bounceByValue is trusted and calls back into BouncedByValue, so that this call ends cannot be proved; verify bounceByValue instead of trusting it`
}

func bounceByValue(n int) int {
	f := BouncedByValue
	return f(n)
}

func claimsOtherChange(xs []int, p *box) {}

// UsesClaimsOtherChange relies on a contract that lists one thing and
// describes another after the call.
//
// @Requires |xs| > 0 And p != nil
// @Modifies p
// @Ensures xs'[0] = xs[0]
func UsesClaimsOtherChange(xs []int, p *box) {
	claimsOtherChange(xs, p) // want `vego: the trusted contract of trust.claimsOtherChange \(trusted.yaml:\d+\) cannot be used: its ensures "xs'\[0\] = 7" describes xs'\[0\] after the call, but nothing its modifies lists is memory that xs'\[0\] reads, so the call cannot have changed it; drop the prime or list what the function writes`
}

// FailsInSecondResult returns the error of a call and, next to it, an
// error of its own every time.
//
// @Ensures True
func FailsInSecondResult() (first, second error) { // want `the contract of FailsInSecondResult may also be met by a function that always returns an error`
	return external(), errAlways
}

var callback func(int) int

func init() { callback = BouncedByVariable }

// BouncedByVariable calls a trusted function of this package that calls it
// back through a variable of the package that holds it.
//
// @Requires n >= 0
// @Ensures result = 0
func BouncedByVariable(n int) (result int) {
	return bounceByVariable(n) // want `vego: bounceByVariable is trusted and calls back into BouncedByVariable, so that this call ends cannot be proved; verify bounceByVariable instead of trusting it`
}

func bounceByVariable(n int) int { return callback(n) }

// SucceedsNowhere has a return without an error that no input reaches,
// since no x and y in range have squares that add up to 6.
//
// @Requires -2 <= x <= 2 And -2 <= y <= 2
// @Ensures True
func SucceedsNowhere(x, y int) (result error) { // want `the contract of SucceedsNowhere may also be met by a function that always returns an error`
	err := external()
	if err == nil {
		if x*x+y*y == 6 {
			return nil
		}
	}
	return errAlways
}

func finish(e error, x, y int) error { return errAlways }

// FinishesNowhere returns what a function makes of the call's error that
// never succeeds.
//
// @Requires -2 <= x <= 2 And -2 <= y <= 2
// @Ensures True
func FinishesNowhere(x, y int) (result error) { // want `the contract of FinishesNowhere may also be met by a function that always returns an error`
	return finish(external(), x, y)
}

// FailsNowhere has a return of an error that no input reaches, so the call
// decides nothing: the function always succeeds.
//
// @Requires -2 <= x <= 2 And -2 <= y <= 2
// @Ensures True
func FailsNowhere(x, y int) (result error) { // want `the contract of FailsNowhere may also be met by a function that always returns an error`
	err := external()
	if err != nil {
		if x*x+y*y == 6 {
			return errAlways
		}
	}
	return nil
}

// FirstErrorOfRange returns the first error of a call made for each
// element.
//
// @Requires |xs| >= 1
// @Ensures True
func FirstErrorOfRange(xs []int) (err error) {
	for _, x := range xs {
		if e := step(x); e != nil {
			return e
		}
	}
	return nil
}

// FirstSuccessOfRange gives up when the call failed for every element.
//
// @Requires |xs| >= 1
// @Ensures True
func FirstSuccessOfRange(xs []int) (err error) {
	for _, x := range xs {
		if step(x) == nil {
			return nil
		}
	}
	return errAlways
}

// IgnoresRange calls for each element, ignores what comes back, and fails.
//
// @Requires |xs| >= 1
// @Ensures True
func IgnoresRange(xs []int) (err error) { // want `the contract of IgnoresRange may also be met by a function that always returns an error`
	for _, x := range xs {
		_ = step(x)
	}
	return errAlways
}

var hooks struct{ fn func(int) int }

func init() { hooks.fn = BouncedByField }

// BouncedByField calls a trusted function of this package that calls it
// back through a field of a variable.
//
// @Requires n >= 0
// @Ensures result = 0
func BouncedByField(n int) (result int) {
	return bounceByField(n) // want `vego: bounceByField is trusted and calls back into BouncedByField, so that this call ends cannot be proved; verify bounceByField instead of trusting it`
}

func bounceByField(n int) int { return hooks.fn(n) }

func claimsOtherSlice(xs, ys []int) {}

// UsesClaimsOtherSlice relies on a contract that lists one slice and
// describes another after the call; the two do not overlap.
//
// @Requires |xs| > 0 And |ys| > 0
// @Modifies ys
// @Ensures xs'[0] = xs[0]
func UsesClaimsOtherSlice(xs, ys []int) {
	claimsOtherSlice(xs, ys) // want `vego: the trusted contract of trust.claimsOtherSlice \(trusted.yaml:\d+\) cannot be used: its ensures "xs'\[0\] = 7" describes xs'\[0\] after the call, .*`
}

func setsFirst(xs []int) { xs[0] = 7 }

// UsesSetsFirst relies on a contract that describes the slice it lists.
//
// @Requires |xs| > 0
// @Modifies xs
// @Ensures result = 7
func UsesSetsFirst(xs []int) (result int) {
	setsFirst(xs)
	return xs[0]
}

var literal func() int

func init() { literal = func() int { return BouncedByClosure() } }

// BouncedByClosure calls a trusted function of this package that calls it
// back through a function literal kept in a variable.
//
// @Ensures result = 0
func BouncedByClosure() (result int) {
	return bounceByClosure() // want `vego: bounceByClosure is trusted and calls back into BouncedByClosure, so that this call ends cannot be proved; verify bounceByClosure instead of trusting it`
}

func bounceByClosure() int { return literal() }

// measured is something with a size.
type measured interface{ Size() int }

// sized has a size that a trusted function works out.
type sized struct{ X int }

// Size calls a trusted function of this package that calls it back through
// a method taken from an interface.
//
// @Ensures result = 0
func (s sized) Size() (result int) {
	return bounceByMethodValue(s) // want `vego: bounceByMethodValue is trusted and calls back into Size, so that this call ends cannot be proved; verify bounceByMethodValue instead of trusting it`
}

func bounceByMethodValue(s sized) int {
	var m measured = s
	f := m.Size
	return f()
}

// node holds a value and more nodes.
type node struct {
	Children []node
	Value    int
}

func setsChild(xs, ys []node) { ys[0].Value = 7 }

// UsesSetsChild relies on a contract that describes, through a slice
// inside one parameter, what the function writes through the other. The
// two parameters do not overlap, but the inner slice may be the other one.
//
// @Requires |xs| = 1 And |ys| = 1 And |xs[0].Children| = 1
// @Modifies ys
// @Ensures result = 7
func UsesSetsChild(xs, ys []node) (result int) {
	setsChild(xs, ys)
	return ys[0].Value
}

func claimsOtherCell(xs, ys []box) {}

// UsesClaimsOtherCell relies on a contract that lists one slice of structs
// and describes a field in another after the call.
//
// @Requires |xs| > 0 And |ys| > 0
// @Modifies ys
// @Ensures xs'[0].X = xs[0].X
func UsesClaimsOtherCell(xs, ys []box) {
	claimsOtherCell(xs, ys) // want `vego: the trusted contract of trust.claimsOtherCell \(trusted.yaml:\d+\) cannot be used: its ensures "xs'\[0\]\.X = 7" describes xs'\[0\]\.X after the call, .*`
}

var sequence func(func() bool)

func init() { sequence = iterate }

func iterate(_ func() bool) { _ = BouncedByRange() }

// BouncedByRange calls a trusted function of this package that calls it
// back by ranging over a function kept in a variable.
//
// @Ensures result = 0
func BouncedByRange() (result int) {
	return bounceByRange() // want `vego: bounceByRange is trusted and calls back into BouncedByRange, so that this call ends cannot be proved; verify bounceByRange instead of trusting it`
}

func bounceByRange() int {
	for range sequence {
	}
	return 0
}

var generic func(func() bool)

func init() { generic = stepBack }

func stepBack(_ func() bool) { _ = BouncedByGeneric() }

func consume[S ~func(func() bool)](s S) {
	for range s {
	}
}

// BouncedByGeneric calls a trusted function of this package that calls it
// back through a generic function that ranges over what it is given.
//
// @Ensures result = 0
func BouncedByGeneric() (result int) {
	return bounceByGeneric() // want `vego: bounceByGeneric is trusted and calls back into BouncedByGeneric, so that this call ends cannot be proved; verify bounceByGeneric instead of trusting it`
}

func bounceByGeneric() int {
	consume(generic)
	return 0
}

// The functions below hand values that carry code to trusted functions. A
// trusted function is believed as far as its own code goes; what it runs
// through an error, an interface, or a function it was given is somebody
// else's code, and its contract covers that only when it says so with runs.

func tell(e error)    {}
func tellAny(e error) {}

type sinkHolder struct {
	n   int
	out func(string)
}

func (s *sinkHolder) flush()     {}
func (s *sinkHolder) flushRuns() {}
func runsNothing(x int)          {}
func runsNobody(x int)           {}

// TellsUnknown passes on an error that could be anything.
//
// @Ensures True
func TellsUnknown(e error) {
	tell(e) // want `cannot verify TellsUnknown: e is passed to tell, which is trusted, and is an error whose origin is not known; tell could run code through it that nobody has seen. If its contract holds whatever that code does, list e under runs in the contract`
}

// TellsKnown passes an error whose methods are those of the standard
// library.
//
// @Ensures True
func TellsKnown(x int) {
	if x > 0 {
		tell(errAlways)
	}
	tell(errors.New("x"))
	tell(nil)
}

// TellsDeclared passes an unknown error to a function whose contract
// vouches for what it runs.
//
// @Ensures True
func TellsDeclared(e error) {
	tellAny(e)
}

// Flushes calls a trusted method on a struct that holds a function.
//
// @Requires s != nil And s.n = 1
// @Ensures result = 1
func Flushes(s *sinkHolder) (result int) {
	s.flush() // want `cannot verify Flushes: s is passed to flush, which is trusted, and is a value of type \*trust.sinkHolder, which is or holds a function value; flush could run code through it that nobody has seen. If its contract holds whatever that code does, list s under runs in the contract`
	return s.n
}

// FlushesDeclared calls one whose contract says that it runs it.
//
// @Requires s != nil And s.n = 1
// @Ensures result = 1
func FlushesDeclared(s *sinkHolder) (result int) {
	s.flushRuns()
	return s.n
}

// UsesRunsNothing calls a function whose contract lists a number as code.
//
// @Ensures True
func UsesRunsNothing() {
	runsNothing(1) // want `the trusted contract of trust.runsNothing \(trusted.yaml:\d+\) cannot be used: its runs lists x, whose type int can hold no error, interface value, function value, channel, or unsafe.Pointer to run`
}

// UsesRunsNobody calls one whose contract lists a name that is no parameter.
//
// @Ensures True
func UsesRunsNobody() {
	runsNobody(1) // want `the trusted contract of trust.runsNobody \(trusted.yaml:\d+\) cannot be used: its runs "y": y is not a parameter`
}

type pinged struct{ n int }

func (b *pinged) ping() {}

// PingsByExpression calls a trusted method by a method expression, whose
// receiver is its first argument.
//
// @Ensures True
func PingsByExpression(b *pinged) {
	(*pinged).ping(b) // want `cannot verify PingsByExpression: this method call is not supported`
}

// PingsLater defers such a call.
//
// @Ensures True
func PingsLater(b *pinged) {
	defer (*pinged).ping(b) // want `cannot verify PingsLater: this method call is not supported`
}

// Pings calls it on a value.
//
// @Ensures True
func Pings(b *pinged) {
	b.ping()
}

// Trusted functions keep the signatures they have, so their unnamed
// results are called result, or result1, result2, and so on.

func twoPlain() (int, error)            { return 0, nil }
func secondNamed() (result2 int, _ int) { return 0, 1 }
func clash(result int) int              { return 7 }

// UsesPair relies on a contract that speaks of two unnamed results.
//
// @Ensures err = nil -> n >= 0
func UsesPair() (n int, err error) {
	n, err = twoPlain()
	return n, err
}

// UsesPairWrongly expects more than the contract says.
//
// @Ensures n >= 0
func UsesPairWrongly() (n int, err error) {
	n, err = twoPlain()
	return n, err // want `vego: postcondition may not hold: n >= 0`
}

// UsesSecondNamed calls a function that itself names its first result
// result2: the name the function gives wins over the generated one.
//
// @Ensures a = 0
func UsesSecondNamed() (a int) {
	a, _ = secondNamed()
	return a
}

// UsesClash calls a function whose parameter has the name its unnamed
// result would get.
//
// @Ensures r = 7
func UsesClash() (r int) {
	return clash(1) // want `the trusted contract of trust.clash \(trusted.yaml:\d+\) cannot be used: its parameter result has a name that means something else in a contract`
}
