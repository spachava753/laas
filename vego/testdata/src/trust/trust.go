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
func CallsWithoutContract(x int) (y int) {
	return helper(x) // want `vego:\ cannot\ verify\ CallsWithoutContract:\ it\ calls\ helper,\ which\ has\ no\ contract;\ annotate\ helper\ with\ //@\ so\ that\ it\ is\ verified,\ or\ add\ a\ trusted\ contract\ for\ trust\.helper\ to\ vego\-trusted\.yaml`
}

//@ Ensures y = x + 1

// CallsStandardLibrary calls a standard-library function vego ships no
// contract for.
func CallsStandardLibrary() (n int) {
	return os.Getpid() // want `vego:\ cannot\ verify\ CallsStandardLibrary:\ it\ calls\ Getpid,\ which\ has\ no\ contract;\ annotate\ Getpid\ with\ //@\ so\ that\ it\ is\ verified,\ or\ add\ a\ trusted\ contract\ for\ os\.Getpid\ to\ vego\-trusted\.yaml`
}

//@ Ensures n >= 0

func readConfig(path string) (size int, err error) {
	info, err := os.Stat(path)
	if err != nil {
		return 0, err
	}
	return int(info.Size()), nil
}

// ConfigSize relies on the trusted contract of readConfig. Nothing says when
// readConfig succeeds, so ConfigSize is not asked to promise success either.
func ConfigSize(path string) (size int, err error) {
	size, err = readConfig(path)
	if err != nil {
		return 0, err
	}
	return size, nil
}

//@ Ensures err = nil -> size >= 0

func parsePort(n int) (port int, err error) {
	if n < 0 || n > 65535 {
		return 0, os.ErrInvalid
	}
	return n, nil
}

// Port relies on a trusted contract that does say when the callee succeeds,
// so it has to say when it succeeds itself.
func Port(n int) (port int, err error) { // want `vego:\ the\ contract\ of\ Port\ would\ also\ be\ met\ by\ a\ function\ that\ always\ returns\ an\ error;\ state\ when\ it\ succeeds\ with\ a\ clause\ such\ as\ "condition\ \->\ err\ =\ nil",\ where\ the\ condition\ is\ about\ the\ inputs\ and\ some\ input\ satisfies\ it`
	return parsePort(n)
}

//@ Ensures err = nil -> port = n

// PortExactly does.
func PortExactly(n int) (port int, err error) {
	return parsePort(n)
}

//@ Ensures 0 <= n <= 65535 -> err = nil
//@ Ensures err = nil -> port = n

func fill(dst []int, value int) {
	for i := range dst {
		dst[i] = value
	}
}

func readOnly(src []int) int { return len(src) }

// Filled uses what the trusted contract says about the slice afterwards.
//
// @ Requires |A| > 0
// @ Modifies A
func Filled(A []int) (first int) {
	fill(A, 7)
	return A[0]
}

//@ Ensures first = 7

// Untouched keeps what it knew about a slice that a trusted function does
// not list under modifies.
//
// @ Requires |A| > 0 And A[0] = 3
func Untouched(A []int) (first int) {
	n := readOnly(A)
	if n < 0 {
		return 0
	}
	return A[0]
}

//@ Ensures first = 3

func contradictory() int { return 0 }

// UsesContradiction would prove anything from a contract that cannot hold.
func UsesContradiction() (n int) {
	return contradictory() // want `vego:\ cannot\ verify\ UsesContradiction:\ contradictory\ has\ a\ contract\ that\ could\ not\ be\ understood` `vego:\ the\ trusted\ contract\ of\ trust\.contradictory\ \(trusted\.yaml:\d+\)\ cannot\ be\ used:\ it\ contradicts\ itself,\ so\ anything\ could\ be\ proved\ from\ it`
}

//@ Ensures n = 42

func wrongModifies(count int) {}

// UsesWrongModifies relies on a contract whose modifies makes no sense.
func UsesWrongModifies() {
	//@ Assert True
	wrongModifies(1) // want `vego:\ cannot\ verify\ UsesWrongModifies:\ wrongModifies\ has\ a\ contract\ that\ could\ not\ be\ understood` `vego:\ the\ trusted\ contract\ of\ trust\.wrongModifies\ \(trusted\.yaml:\d+\)\ cannot\ be\ used:\ in\ its\ modifies\ \"count\":\ count\ is\ passed\ by\ value,\ so\ the\ caller\ cannot\ see\ a\ change\ to\ it`
}

func wrongName(count int) int { return count }

// UsesWrongName relies on a contract that names something that is not there.
func UsesWrongName() (n int) {
	return wrongName(1) // want `vego:\ cannot\ verify\ UsesWrongName:\ wrongName\ has\ a\ contract\ that\ could\ not\ be\ understood` `vego:\ the\ trusted\ contract\ of\ trust\.wrongName\ \(trusted\.yaml:\d+\)\ cannot\ be\ used:\ in\ its\ ensures\ "total\ >=\ 0":\ unknown\ name\ total`
}

//@ Ensures n >= 0

func makesSlice() []int { return nil }

// UsesTrustedSlice gets a slice from a trusted function. Nothing is known of
// the slice but what every slice guarantees.
func UsesTrustedSlice() (n int) {
	s := makesSlice()
	return len(s)
}

//@ Ensures n >= 0

// ReadsTrustedSlice assumes the slice has an element.
func ReadsTrustedSlice() (n int) {
	s := makesSlice()
	return s[0] // want `vego: index may be out of range` `vego: postcondition may not hold: n >= 0`
}

//@ Ensures n >= 0

// Verified has annotations and a trusted contract.
func Verified() int { // want `vego:\ Verified\ has\ //@\ annotations\ and\ a\ trusted\ contract;\ a\ function\ is\ either\ verified\ or\ trusted,\ not\ both`
	return 0
}

//@ Ensures result = 0

// Sorted relies on the shipped contract of sort.Ints.
//
// @ Requires |A| >= 2
// @ Modifies A
func Sorted(A []int) (ordered bool) {
	sort.Ints(A)
	return A[0] <= A[1]
}

//@ Ensures ordered = True

// Roll relies on the shipped contract of rand.Intn.
func Roll() (face int) {
	return rand.Intn(6) + 1
}

//@ Ensures 1 <= face <= 6

// RollZero breaks the precondition that contract states.
func RollZero() int {
	//@ Assert True
	return rand.Intn(0) // want `vego:\ precondition\ of\ Intn\ may\ not\ hold:\ n\ >\ 0`
}

// Scheme relies on the shipped contract of strings.HasPrefix.
func Scheme(url string) (secure bool) {
	return strings.HasPrefix(url, "https://")
}

//@ Ensures secure = True -> (|url| >= 8 And url[0] = 104)

// Overridden calls a function whose shipped contract the project file
// replaces with one that says nothing.
//
// @ Requires |A| = 0
func Overridden(A []int) (ok bool) {
	return sort.IntsAreSorted(A) // want `vego:\ postcondition\ may\ not\ hold:\ ok\ =\ True`
}

//@ Ensures ok = True

// MaxInt here must not replace the limit that the shipped contract of
// strings.Repeat speaks of.
const MaxInt = 1 << 100

const realMax = int(^uint(0) >> 1)

// HugeRepeat asks for a string longer than any string can be.
//
// @ Requires n > realMax/2
func HugeRepeat(n int) string {
	return strings.Repeat("xx", n) // want `precondition of Repeat may not hold: \|s\| \* count <= MaxAlloc`
}

//@ Ensures False

//@ Predicate good(n) ::= n = 1

func usesPredicate() int { return 0 }

// UsesPredicate relies on a trusted contract that mentions a predicate,
// which would mean something different in every package.
func UsesPredicate() (n int) {
	return usesPredicate() // want `the trusted contract of trust.usesPredicate \(trusted.yaml:\d+\) cannot be used: in its ensures "good\(result\)": unknown predicate good` `cannot verify UsesPredicate: usesPredicate has a contract that could not be understood`
}

//@ Ensures n = 1

func impossibleString() string { return "a" }

// UsesImpossibleString relies on a contract no string can satisfy.
func UsesImpossibleString() (b byte) {
	s := impossibleString() // want `the trusted contract of trust.impossibleString \(trusted.yaml:\d+\) cannot be used: it contradicts itself` `cannot verify UsesImpossibleString: impossibleString has a contract that could not be understood`
	return s[0]
}

//@ Ensures False

func take(MaxInt any) int { return 0 }

// UsesBlockedName relies on a contract that mentions a parameter of a type
// vego does not model; the name must not turn into the integer limit.
func UsesBlockedName() (n int) {
	return take(nil) // want `cannot verify UsesBlockedName: ` `the trusted contract of trust.take \(trusted.yaml:\d+\) cannot be used: in its ensures "result = MaxInt": parameter MaxInt has type any, which cannot be used in a contract`
}

//@ Ensures n = MaxInt

var errAlways = errors.New("always")

func ready() (value *int, err error) { return nil, nil }

// AlwaysFailsAfterReady calls a trusted function that is guaranteed to
// succeed, so it has no excuse for failing every time.
func AlwaysFailsAfterReady() error { // want `the contract of AlwaysFailsAfterReady would also be met by a function that always returns an error`
	_, _ = ready()
	return errAlways
}

//@ Ensures True

func takeAny(x any) int { return 0 }

// UsesOldOfBlockedName relies on a contract that takes old of a parameter
// vego does not model.
func UsesOldOfBlockedName() (n int) {
	return takeAny(nil) // want `cannot verify UsesOldOfBlockedName: ` `the trusted contract of trust.takeAny \(trusted.yaml:\d+\) cannot be used: in its ensures "result = old\(x\)": parameter x has type any, which cannot be used in a contract`
}

//@ Ensures n = 0

func readyWith(a []int) (err error) { return nil }

func readyWriting(a []int) (err error) { return nil }

// AlwaysFailsAfterReadyWith calls a trusted function whose success follows
// from the slice it leaves unchanged.
//
// @ Requires |a| = 1 And a[0] = 0
func AlwaysFailsAfterReadyWith(a []int) error { // want `the contract of AlwaysFailsAfterReadyWith would also be met by a function that always returns an error`
	_ = readyWith(a)
	return errAlways
}

//@ Ensures True

// AlwaysFailsAfterReadyWriting calls one whose success follows from the
// length of a slice it may write, which a call cannot change.
//
// @ Requires |a| = 1
// @ Modifies a
func AlwaysFailsAfterReadyWriting(a []int) error { // want `the contract of AlwaysFailsAfterReadyWriting would also be met by a function that always returns an error`
	_ = readyWriting(a)
	return errAlways
}

//@ Ensures True

func readyByte() (value uint8, err error) { return 0, nil }

// AlwaysFailsAfterReadyByte calls a trusted function whose success is
// guarded by a condition on its own result that the result's type makes
// true.
func AlwaysFailsAfterReadyByte() error { // want `the contract of AlwaysFailsAfterReadyByte would also be met by a function that always returns an error`
	_, _ = readyByte()
	return errAlways
}

//@ Ensures True

func maybeSigned() (value int8, err error) { return -1, errAlways }

// MayFailAfterSigned calls one whose guard really depends on its result, so
// nothing says when it succeeds.
func MayFailAfterSigned() error {
	_, err := maybeSigned()
	return err
}

//@ Ensures True

func readyAtLeast(n int) (value uint8, err error) { return 0, nil }

// AlwaysFailsAfterReadyAtLeast calls a trusted function whose guard holds
// for every byte once the argument is zero.
func AlwaysFailsAfterReadyAtLeast() error { // want `the contract of AlwaysFailsAfterReadyAtLeast would also be met by a function that always returns an error`
	_, _ = readyAtLeast(0)
	return errAlways
}

//@ Ensures True

func readyBytes(a []byte) (err error) { return nil }

// AlwaysFailsAfterReadyBytes calls one whose guard is about an element of a
// slice it may write; the element is a byte whatever it writes.
//
// @ Requires |a| = 1
// @ Modifies a
func AlwaysFailsAfterReadyBytes(a []byte) error { // want `the contract of AlwaysFailsAfterReadyBytes would also be met by a function that always returns an error`
	_ = readyBytes(a)
	return errAlways
}

//@ Ensures True

func readyNil(e error) (err error) { return nil }

// AlwaysFailsAfterReadyNil calls a trusted function that succeeds on every
// call its contract admits.
func AlwaysFailsAfterReadyNil() error { // want `the contract of AlwaysFailsAfterReadyNil would also be met by a function that always returns an error`
	_ = readyNil(nil)
	return errAlways
}

//@ Ensures True

func readyLinked() (value uint8, err error) { return 0, nil }

// AlwaysFailsAfterReadyLinked calls one whose success follows from two
// postconditions together.
func AlwaysFailsAfterReadyLinked() error { // want `the contract of AlwaysFailsAfterReadyLinked would also be met by a function that always returns an error`
	_, _ = readyLinked()
	return errAlways
}

//@ Ensures True

// PassThrough succeeds for the nil error it requires.
//
// @ Requires e = nil
func PassThrough(e error) (err error) {
	return e
}

//@ Ensures err = nil

// OnlyA succeeds for the one string it requires.
//
// @ Requires s = "a"
func OnlyA(s string) (err error) {
	return nil
}

//@ Ensures err = nil

// Contrapositive states its success condition the other way round.
func Contrapositive(n int) (err error) {
	if n < 0 {
		return errAlways
	}
	return nil
}

//@ Ensures err != nil -> n < 0

// readySixtyFive is excused: it reaches an unpredictable call, and the
// search for a witness does not try strings of 65 bytes.
func readySixtyFive(s string) error {
	if err := external(); err != nil && len(s) != 65 {
		return err
	}
	return nil
}

//@ Ensures |s| = 65 -> result = nil

func external() error { return nil }

// AlwaysFailsAfterSixtyFive calls it with a string for which its contract
// does guarantee success.
func AlwaysFailsAfterSixtyFive() error { // want `the contract of AlwaysFailsAfterSixtyFive would also be met by a function that always returns an error`
	_ = readySixtyFive("01234567890123456789012345678901234567890123456789012345678901234")
	return errAlways
}

//@ Ensures True

func writesSixtyFive(a []byte) (err error) {
	a[0] = 255
	return nil
}

// AlwaysFailsAfterWriting calls a trusted function whose success follows
// from the type of an element it writes.
func AlwaysFailsAfterWriting() error { // want `the contract of AlwaysFailsAfterWriting would also be met by a function that always returns an error`
	a := make([]byte, 65)
	_ = writesSixtyFive(a)
	return errAlways
}

//@ Ensures True

// ImpossibleLiteral promises success for a slice that cannot exist: an int8
// cannot hold the byte 128.
func ImpossibleLiteral(a []int8) error { // want `the contract of ImpossibleLiteral would also be met by a function that always returns an error`
	if len(a) == 1 {
		_ = a[0]
	}
	return errAlways
}

//@ Ensures a = "\x80" -> result = nil

// PossibleLiteral promises it for one that can.
func PossibleLiteral(a []int8) error {
	if len(a) == 1 && a[0] == 127 {
		return nil
	}
	return errAlways
}

//@ Ensures a = "\x7f" -> result = nil

func readsSixtyFive(a []byte) (err error) { return nil }

// SixtyFive returns a slice of 65 bytes.
func SixtyFive() []byte {
	return make([]byte, 65)
}

//@ Ensures |result| = 65

// AlwaysFailsAfterReading calls a trusted function whose success follows
// from the type of an element of a slice it only reads, which nothing here
// has read before.
func AlwaysFailsAfterReading() error { // want `the contract of AlwaysFailsAfterReading would also be met by a function that always returns an error`
	a := SixtyFive()
	_ = readsSixtyFive(a)
	return errAlways
}

//@ Ensures True

// HugeRepeat asks for a string longer than any allocation, which panics.
func RepeatBeyondMemory() int {
	s := strings.Repeat("ab", 1<<50) // want `vego: precondition of Repeat may not hold: \|s\| \* count <= MaxAlloc`
	return len(s)
}

//@ Ensures result = 42

// SmallRepeat stays under the limit.
//
// @ Requires 0 <= n <= 1000
func SmallRepeat(n int) int {
	s := strings.Repeat("ab", n)
	return len(s)
}

//@ Ensures result = 2*n

func claimsNegative(n int) {}

// ContradictedHere calls a function whose contract cannot be true of the
// argument it passes.
func ContradictedHere() int {
	claimsNegative(5) // want `vego: the trusted contract of claimsNegative cannot be true of this call: what it promises contradicts what is known here`
	return 0
}

//@ Ensures result = 42

// NotContradicted passes an argument the contract can be true of.
func NotContradicted() int {
	claimsNegative(-5)
	return 0
}

//@ Ensures result = 0

// DeadContradiction calls it on a path that is never taken.
//
// @ Requires n < 0
func DeadContradiction(n int) int {
	if n > 0 {
		claimsNegative(5)
	}
	return 0
}

//@ Ensures result = 0

func claimsChange(xs []int) {}

// UsesClaimsChange relies on a contract that says memory changed which it
// does not list.
//
// @ Requires |xs| > 0 And xs[0] = 1
func UsesClaimsChange(xs []int) {
	claimsChange(xs) // want `vego: cannot verify UsesClaimsChange: claimsChange has a contract that could not be understood` `vego: the trusted contract of trust.claimsChange \(trusted.yaml:\d+\) cannot be used: its ensures "xs'\[0\] = 7" describes xs'\[0\] after the call, but nothing its modifies lists is memory that xs'\[0\] reads, so the call cannot have changed it; drop the prime or list what the function writes`
}

//@ Ensures xs'[0] = 99

// Bounced calls a trusted function of this package that calls it back, so
// the two never return.
//
// @ Requires n >= 0
func Bounced(n int) int {
	return bounce(n) // want `vego: bounce is trusted and calls back into Bounced, so that this call ends cannot be proved; verify bounce instead of trusting it`
}

//@ Ensures result = 0

func bounce(n int) int { return Bounced(n) }

// IgnoresFailure calls a function that may fail, ignores whether it did,
// and then fails for a reason of its own. The call does not excuse it.
func IgnoresFailure(x int) (result int, err error) { // want `the contract of IgnoresFailure would also be met by a function that always returns an error`
	_ = external()
	return 0, errAlways
}

//@ Ensures err = nil -> result = x + 1

// PassesFailure fails when the call does, and is excused.
func PassesFailure(x int) (result int, err error) {
	if err := external(); err != nil {
		return 0, errAlways
	}
	return x, nil
}

//@ Ensures err = nil -> result = x

// LoopsOverFailures keeps the first failure of several calls.
//
// @ Requires 0 <= n <= 10
func LoopsOverFailures(n int) (err error) {
	var first error
	//@ Invariant 0 <= i <= n
	//@ Variant n - i
	for i := 0; i < n; i++ {
		if failed := external(); failed != nil && first == nil {
			first = failed
		}
	}
	return first
}

//@ Ensures True

// box holds a number.
type box struct{ X int }

func setThrough(p, q *box) { p.X = 1 }

// SeenThroughOther relies on a contract that describes, through one
// parameter, what the function writes through another that is the same.
//
// @ Requires p != nil
// @ Modifies p
func SeenThroughOther(p *box) int {
	setThrough(p, p)
	return p.X
}

//@ Ensures result = 1

// never returns false; its contract says less.
func never(s []byte) bool { return false }

//@ Ensures result -> (Forall k in [0, |s|) : s[k] < 0)

func nonnegative(s []byte) {}

// NeverTaken calls a trusted function on a path that cannot be taken,
// which only shows once the types of the bytes are taken into account. The
// contract of the function is not to blame for that.
//
// @ Requires |s| = 1
func NeverTaken(s []byte) int {
	if never(s) {
		nonnegative(s)
	}
	return 0
}

//@ Ensures result = 0

// parent points to a child.
type parent struct{ Child *box }

func orphan(p *parent) { p.Child = nil }

// Orphans relies on a contract that says what a pointer field is after the
// call.
//
// @ Requires p != nil
// @ Modifies p
func Orphans(p *parent) bool {
	orphan(p)
	return p.Child == nil
}

//@ Ensures result

func allNonnegative(s []byte) {}

// NeverTakenAll is NeverTaken with a promise about every byte.
//
// @ Requires |s| = 1
func NeverTakenAll(s []byte) int {
	if never(s) {
		allNonnegative(s)
	}
	return 0
}

//@ Ensures result = 0

func pair() (int, error) { return 0, nil }

// UsesNumberOnly uses the number a call returned in arithmetic, which adds
// facts about it but chooses no path, and then fails on its own.
func UsesNumberOnly() error { // want `the contract of UsesNumberOnly would also be met by a function that always returns an error`
	n, _ := pair()
	_ = n / 2
	return errAlways
}

//@ Ensures True

// KeepsFailure puts the error of a call into memory and returns it from
// there.
func KeepsFailure() error {
	err := external()
	saved := []error{err}
	return saved[0]
}

//@ Ensures True

// KeepsOtherFailure puts the error of a call into memory next to an error
// of its own, and returns its own.
func KeepsOtherFailure() error { // want `the contract of KeepsOtherFailure would also be met by a function that always returns an error`
	err := external()
	saved := []error{err, errAlways}
	return saved[1]
}

//@ Ensures True

// BranchesOnOwnError keeps the error of a call in memory next to an error
// of its own, and decides by its own.
func BranchesOnOwnError() error { // want `the contract of BranchesOnOwnError would also be met by a function that always returns an error`
	err := external()
	saved := []error{err, errAlways}
	if saved[1] != nil {
		return errAlways
	}
	return nil
}

//@ Ensures True

// BranchesOnKeptError decides by the error of the call, read back from
// memory.
func BranchesOnKeptError() error {
	err := external()
	saved := []error{err, errAlways}
	if saved[0] != nil {
		return errAlways
	}
	return nil
}

//@ Ensures True

func bytePair() (byte, error) { return 0, nil }

// BranchesOnAnyByte branches on something every byte satisfies, so the
// call decides nothing.
func BranchesOnAnyByte() error { // want `the contract of BranchesOnAnyByte would also be met by a function that always returns an error`
	b, _ := bytePair()
	if b >= 0 {
		return errAlways
	}
	return nil
}

//@ Ensures True

// BranchesOnSomeBytes branches on something the call decides.
func BranchesOnSomeBytes() error {
	b, _ := bytePair()
	if b >= 7 {
		return errAlways
	}
	return nil
}

//@ Ensures True

// hasFailed says whether an error is one.
func hasFailed(e error) bool { return e != nil }

//@ Ensures result <-> e != nil

// AsksHelper lets a verified function say whether the call failed.
func AsksHelper() error {
	err := external()
	if hasFailed(err) {
		return errAlways
	}
	return nil
}

//@ Ensures True

// AsksHelperAboutOwn asks it about an error of its own.
func AsksHelperAboutOwn() error { // want `the contract of AsksHelperAboutOwn would also be met by a function that always returns an error`
	_ = external()
	if hasFailed(errAlways) {
		return errAlways
	}
	return nil
}

//@ Ensures True

// translate makes an error of its own of any error.
func translate(e error) error {
	if e != nil {
		return errAlways
	}
	return nil
}

//@ Ensures result = nil <-> e = nil

// Translates returns what a verified function makes of the call's error.
func Translates() error {
	return translate(external())
}

//@ Ensures True

// LoopsWithOwnError calls a function that may fail inside a loop that also
// assigns an error of its own, which is what it returns.
//
// @ Requires 0 <= n <= 10
func LoopsWithOwnError(n int) error { // want `the contract of LoopsWithOwnError would also be met by a function that always returns an error`
	err := errAlways
	//@ Invariant 0 <= i <= n
	//@ Invariant err != nil
	//@ Variant n - i
	for i := 0; i < n; i++ {
		_ = external()
		err = errAlways
	}
	return err
}

//@ Ensures True

// ForwardsThroughLoops keeps the error of a call made in one loop in a
// variable that a second loop copies.
//
// @ Requires 1 <= n <= 3 And 1 <= m <= 3
func ForwardsThroughLoops(n, m int) error {
	var a, b error
	//@ Invariant 0 <= i <= n
	//@ Variant n - i
	for i := 0; i < n; i++ {
		a = external()
	}
	//@ Invariant 0 <= j <= m
	//@ Variant m - j
	for j := 0; j < m; j++ {
		b = a
	}
	return b
}

//@ Ensures True

// SavesBeforeSecondLoop keeps an error of its own that one loop leaves in a
// variable, before a second loop puts the error of a call into the same
// variable.
//
// @ Requires 1 <= n <= 3 And 1 <= m <= 3
func SavesBeforeSecondLoop(n, m int) error { // want `the contract of SavesBeforeSecondLoop would also be met by a function that always returns an error`
	err := errAlways
	//@ Invariant 0 <= i <= n And err != nil
	//@ Variant n - i
	for i := 0; i < n; i++ {
		err = errAlways
	}
	saved := err
	//@ Invariant 0 <= j <= m
	//@ Variant m - j
	for j := 0; j < m; j++ {
		err = external()
	}
	return saved
}

//@ Ensures True

// AsksHelperAfterLoop asks a verified function about the error a loop left.
//
// @ Requires 1 <= n <= 3
func AsksHelperAfterLoop(n int) error {
	var err error
	//@ Invariant 0 <= i <= n
	//@ Variant n - i
	for i := 0; i < n; i++ {
		err = external()
	}
	if hasFailed(err) {
		return errAlways
	}
	return nil
}

//@ Ensures True

// AsksHelperInLoop keeps the answer of the verified function instead.
//
// @ Requires 1 <= n <= 3
func AsksHelperInLoop(n int) error {
	var failed bool
	//@ Invariant 0 <= i <= n
	//@ Variant n - i
	for i := 0; i < n; i++ {
		failed = hasFailed(external())
	}
	if failed {
		return errAlways
	}
	return nil
}

//@ Ensures True

// AsksOnBothPaths asks a verified function about the error on both sides of
// a test of it, and passes the error on.
func AsksOnBothPaths() error {
	err := external()
	if err != nil {
		_ = hasFailed(err)
		return err
	}
	_ = hasFailed(err)
	return nil
}

//@ Ensures True

// onFailure is called with an error that is one.
//
// @ Requires e != nil
func onFailure(e error) {}

//@ Ensures e != nil

// onSuccess is called with no error.
//
// @ Requires e = nil
func onSuccess(e error) {}

//@ Ensures e = nil

// ReportsBothWays calls a different verified function on each side of a
// test of the error, each of which says which side it is on.
func ReportsBothWays() error {
	err := external()
	if err != nil {
		onFailure(err)
		return err
	}
	onSuccess(err)
	return nil
}

//@ Ensures True

func alwaysError(b byte) error { return errAlways }

// CopiesByteInLoop passes on, through a loop, a byte that a call returned,
// to a function that fails for every byte.
//
// @ Requires 1 <= n <= 3
func CopiesByteInLoop(n int) error { // want `the contract of CopiesByteInLoop would also be met by a function that always returns an error`
	b, _ := bytePair()
	var saved byte
	//@ Invariant 0 <= i <= n
	//@ Variant n - i
	for i := 0; i < n; i++ {
		saved = b
	}
	return alwaysError(saved)
}

//@ Ensures True

// NotesFailureInLoop remembers, in a number, that a call in a loop failed.
// The number it stores does not depend on the call; that it is stored does.
//
// @ Requires 1 <= n <= 3
func NotesFailureInLoop(n int) error {
	last := -1
	//@ Invariant 0 <= i <= n And -1 <= last < n
	//@ Variant n - i
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

//@ Ensures True

// FailsEitherWay branches on what a call returned and fails on both sides.
func FailsEitherWay(x int) (result int, err error) { // want `the contract of FailsEitherWay would also be met by a function that always returns an error`
	n, _ := pair()
	if n > 5 {
		return 0, errAlways
	}
	return 0, errOther
}

//@ Ensures err = nil -> result = x + 1

var errOther = errors.New("other")

// FailsAfterPassingOn passes the error of a call on, and fails on its own
// when there is none.
func FailsAfterPassingOn(x int) (result int, err error) { // want `the contract of FailsAfterPassingOn would also be met by a function that always returns an error`
	_, err = pair()
	if err != nil {
		return 0, err
	}
	return 0, errAlways
}

//@ Ensures err = nil -> result = x + 1

func step(i int) error { return nil }

// FirstSuccessWins tries several times and gives up when every try failed.
//
// @ Requires 1 <= n
func FirstSuccessWins(n int) (err error) {
	//@ Invariant 0 <= i <= n
	//@ Variant n - i
	for i := 0; i < n; i++ {
		if step(i) == nil {
			return nil
		}
	}
	return errAlways
}

//@ Ensures True

func setting() string { return "" }

// NeedsSetting fails when something from outside that is not an error is
// missing.
func NeedsSetting() (value string, err error) {
	v := setting()
	if len(v) == 0 {
		return "", errAlways
	}
	return v, nil
}

//@ Ensures err = nil -> |value| > 0

// BouncedByValue calls a trusted function of this package that calls it
// back through a function value.
//
// @ Requires n >= 0
func BouncedByValue(n int) int {
	return bounceByValue(n) // want `vego: bounceByValue is trusted and calls back into BouncedByValue, so that this call ends cannot be proved; verify bounceByValue instead of trusting it`
}

//@ Ensures result = 0

func bounceByValue(n int) int {
	f := BouncedByValue
	return f(n)
}

func claimsOtherChange(xs []int, p *box) {}

// UsesClaimsOtherChange relies on a contract that lists one thing and
// describes another after the call.
//
// @ Requires |xs| > 0 And p != nil
// @ Modifies p
func UsesClaimsOtherChange(xs []int, p *box) {
	claimsOtherChange(xs, p) // want `vego: cannot verify UsesClaimsOtherChange: claimsOtherChange has a contract that could not be understood` `vego: the trusted contract of trust.claimsOtherChange \(trusted.yaml:\d+\) cannot be used: its ensures "xs'\[0\] = 7" describes xs'\[0\] after the call, but nothing its modifies lists is memory that xs'\[0\] reads, so the call cannot have changed it; drop the prime or list what the function writes`
}

//@ Ensures xs'[0] = xs[0]

// FailsInSecondResult returns the error of a call and, next to it, an
// error of its own every time.
func FailsInSecondResult() (first, second error) { // want `the contract of FailsInSecondResult would also be met by a function that always returns an error`
	return external(), errAlways
}

//@ Ensures True

var callback func(int) int

func init() { callback = BouncedByVariable }

// BouncedByVariable calls a trusted function of this package that calls it
// back through a variable of the package that holds it.
//
// @ Requires n >= 0
func BouncedByVariable(n int) int {
	return bounceByVariable(n) // want `vego: bounceByVariable is trusted and calls back into BouncedByVariable, so that this call ends cannot be proved; verify bounceByVariable instead of trusting it`
}

//@ Ensures result = 0

func bounceByVariable(n int) int { return callback(n) }

// SucceedsNowhere has a return without an error that no input reaches,
// although ruling that out takes more than the solver does.
//
// @ Requires -2 <= x <= 2 And -2 <= y <= 2
func SucceedsNowhere(x, y int) error { // want `the contract of SucceedsNowhere would also be met by a function that always returns an error`
	err := external()
	if err == nil {
		if x*x+y*y == 6 {
			return nil
		}
	}
	return errAlways
}

//@ Ensures True

func finish(e error, x, y int) error { return errAlways }

// FinishesNowhere returns what a function makes of the call's error that
// never succeeds.
//
// @ Requires -2 <= x <= 2 And -2 <= y <= 2
func FinishesNowhere(x, y int) error { // want `the contract of FinishesNowhere would also be met by a function that always returns an error`
	return finish(external(), x, y)
}

//@ Ensures True
