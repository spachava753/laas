package locks

import "sync"

// Every function below copies or overwrites a value that holds a state, in
// one of the ways Go has, and cannot be verified.

// @Requires a != nil
// @Ensures True
func CopyDeref(a *Account) {
	b := *a // want `vego: cannot verify CopyDeref: \*a copies a locks.Account, which holds a sync.Mutex; use a pointer to it; a value that holds a state`
	_ = &b
}

// @Requires a != nil
// @Ensures True
func CopyField(a *Account) {
	m := a.mu // want `vego: cannot verify CopyField: a.mu copies a sync.Mutex, which holds a state`
	_ = &m
}

// @Requires a != nil
// @Ensures True
func CopyVar(a *Account) {
	var m = a.mu // want `cannot verify CopyVar: a.mu copies a sync.Mutex`
	_ = &m
}

// @Ensures True
func CopyArgument(a *Account) {
	take(*a) // want `cannot verify CopyArgument: \*a copies a locks.Account`
}

func take(a Account) {}

// @Requires a != nil
// @Ensures True
func CopyInLiteral(a *Account) {
	g := Guards{inner: *a} // want `cannot verify CopyInLiteral: \*a copies a locks.Account`
	_ = &g
}

// @Ensures True
func CopyParameter(a Account) { // want `cannot verify CopyParameter: the parameter a has type locks.Account, which holds a sync.Mutex, and passing it copies the value; use a pointer to locks.Account`
}

// @Ensures True
func CopyResult() (a Account) { // want `cannot verify CopyResult: the result a has type locks.Account`
	return Account{}
}

// @Ensures True
func (a Account) CopyReceiver() { // want `cannot verify CopyReceiver: the receiver a has type locks.Account`
}

// @Requires len(as) > 0
// @Ensures True
func CopyRange(as []Account) {
	for _, a := range as { // want `cannot verify CopyRange: the range variable a copies each element, a locks.Account, which holds a sync.Mutex; range over the indices and use &s\[i\]`
		_ = &a
	}
}

// @Ensures True
func CopyMapIndex(m map[int]Account) (n int) {
	return m[0].balance // want `cannot verify CopyMapIndex: m\[0\] cannot be addressed, so Go copies a locks.Account, which holds a sync.Mutex, to select balance from it; hold the value by pointer, as in a map of pointers`
}

func makeAccount() Account { return Account{} }

// @Ensures True
func CopyCall() (n int) {
	return makeAccount().balance // want `cannot verify CopyCall: makeAccount returns a locks.Account, which holds a sync.Mutex, by value, which copies it; return a pointer`
}

// @Ensures True
func CopyCallStatement() {
	makeAccount() // want `cannot verify CopyCallStatement: makeAccount returns a locks.Account`
}

// @Ensures True
func CopyCallBlank() {
	_ = makeAccount() // want `cannot verify CopyCallBlank: makeAccount returns a locks.Account`
}

// @Ensures True
func DeferredResult() {
	defer makeAccount() // want `cannot verify DeferredResult: makeAccount returns a locks.Account`
}

// Valued has a method with a value receiver.
type Valued struct {
	mu sync.Mutex
	n  int
}

// Get is not verified.
func (v Valued) Get() int { return v.n }

// Getter is satisfied by Valued and *Valued.
type Getter interface {
	// @Ensures True
	Get() (n int)
}

// @Requires v != nil
// @Ensures True
func CopyValueReceiver(v *Valued) (n int) {
	return v.Get() // want `cannot verify CopyValueReceiver: Get has a value receiver of type locks.Valued, which holds a sync.Mutex, so calling it copies the value; give the method a pointer receiver`
}

// @Requires v != nil
// @Ensures g != nil
func CopyByInterface(v *Valued) (g Getter) {
	return v // want `cannot verify CopyByInterface: v is converted to locks.Getter, whose method Get has a value receiver of type locks.Valued, which holds a sync.Mutex, so each call copies the value`
}

// @Requires a != nil
// @Ensures True
func CopyToAny(a *Account) (x any) {
	return *a // want `cannot verify CopyToAny: \*a copies a locks.Account`
}

// Twin is a struct type of its own with the same fields as Account.
type Twin struct {
	mu      sync.Mutex
	balance int
}

// @Requires a != nil
// @Ensures True
func CopyConversion(a *Account) {
	s := Twin(*a) // want `cannot verify CopyConversion: Twin\(\*a\) copies a locks.Twin, which holds a sync.Mutex`
	_ = &s
}

// @Requires a != nil
// @Modifies a
// @Ensures True
func Overwrite(a *Account) {
	*a = Account{} // want `cannot verify Overwrite: \*a is assigned, which overwrites a locks.Account, which holds a sync.Mutex; create the value where it is declared, as in x := T\{\} or p := &T\{\}, and change it only through its methods`
}

// @Requires a != nil
// @Modifies a.mu
// @Ensures True
func OverwriteField(a *Account) {
	a.mu = sync.Mutex{} // want `cannot verify OverwriteField: a.mu is assigned, which overwrites a sync.Mutex`
}

// @Requires g != nil
// @Modifies g
// @Ensures True
func OverwriteEnclosing(g *Guards) {
	*g = Guards{n: 1} // want `cannot verify OverwriteEnclosing: \*g is assigned, which overwrites a locks.Guards, which holds a sync.Mutex`
}

// @Ensures True
func OverwriteRedeclared() (n int) {
	x := Account{}
	n, x, y := 1, Account{}, 2 // want `cannot verify OverwriteRedeclared: x is assigned, which overwrites a locks.Account`
	_ = &x
	return n + y
}

// @Requires |as| < 10
// @Ensures True
func Append(as []Account) {
	as = append(as, Account{}) // want `cannot verify Append: append to a slice of locks.Account, which holds a sync.Mutex, copies every element when the slice grows; build the slice with its final length, as in make\(\[\]T, n\), or hold the elements by pointer`
	_ = as
}

// @Requires a != nil
// @Ensures True
func CopyInLiteralBody(a *Account) {
	func() {
		b := *a // want `cannot verify CopyInLiteralBody: \*a copies a locks.Account`
		_ = &b
	}()
}

// @Ensures True
func CopyLiteralParameter() {
	f := func(a Account) {} // want `cannot verify CopyLiteralParameter: the parameter of the function literal, a has type locks.Account`
	f(Account{})
}

// These do not copy and verify.

// @Requires a != nil
// @Ensures result = a.balance
func Select(a *Account) (result int) {
	return a.balance
}

// @Ensures result = 1
func Literal() (result int) {
	a := Account{balance: 1}
	b := &Account{}
	take2(&a, b)
	return a.balance
}

// @Requires a != nil And b != nil
// @Ensures True
func take2(a, b *Account) {
}

// @Requires |as| > 0
// @Ensures result = as[0].balance
func Element(as []Account) (result int) {
	p := &as[0]
	return p.balance
}

// @Ensures |result| = 3
func Make() (result []Account) {
	return make([]Account, 3)
}

// @Ensures True
func Fields() (n int) {
	return Account{balance: 2}.balance
}

// @Ensures True
func Captured() {
	var a Account
	func() {
		a.balance = 1
	}()
}
