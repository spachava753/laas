package keeps

import (
	"io"

	"keepslib"
)

// KeepsGlobally hands a handler to a function that keeps it in a
// package-level variable. Its entry lists no destination, which is the only
// thing it could write, and is refused; without keeps the hand-over is
// refused, since the parameter holds code.
//
// @Ensures True
func KeepsGlobally() {
	keepslib.Keep(show) // want `the trusted contract of keepslib.Keep \(trusted.yaml:\d+\) cannot be used: its keeps lists h with no destination`
}

// @Ensures True
func KeepsCount() {
	_ = keepslib.KeepsCount(1) // want `its keeps lists n, whose type int can hold no error, interface value, function value, channel, or unsafe.Pointer to keep`
}

// @Requires r != nil
// @Ensures True
func KeepsInCount(r io.Reader) {
	_ = keepslib.KeepsInCount(r) // want `its keeps lists r as kept in result, whose type int can hold no code`
}

// @Requires r != nil
// @Ensures True
func KeepsInSelf(r io.Reader) {
	keepslib.KeepsInSelf(r) // want `its keeps lists r as kept in itself`
}

// @Requires reg != nil
// @Ensures True
func KeepsInUnlisted(reg *keepslib.Registry) {
	keepslib.KeepsInUnlisted(reg, show) // want `its keeps lists h as kept in reg, which its modifies does not list`
}

// KeepsInError keeps a handler in an error, through which a later call
// would run it without being counted as one that may call through a value.
//
// @Ensures True
func KeepsInError() {
	_ = keepslib.KeepsInError(show) // want `its keeps lists h as kept in result, whose type error can hold no function value and no value of an interface whose methods all have contracts. But h can hold a function value of type keepslib.Handler, and a call handed result would run that code without being counted as one that may call through a value`
}

// @Ensures True
func KeepsInNothing() {
	keepslib.KeepsInNothing(show) // want `its keeps lists h as kept in box, which is not a result or a parameter`
}

// @Ensures True
func KeepsUnknown() {
	keepslib.KeepsUnknown(show) // want `its keeps "g": g is not a parameter`
}

// @Ensures True
func KeepsCalled() {
	_ = keepslib.KeepsCalled(func(i int) bool { return true }) // want `its keeps lists f, which its calls gives a contract`
}

// @Ensures True
func KeepsFormatted() {
	_ = keepslib.KeepsFormatted(1) // want `its keeps lists v, which its formats lists`
}

// @Ensures True
func KeepsTwice() {
	_ = keepslib.KeepsTwice(show) // want `its keeps lists h as kept in result twice`
}

// AddsRaw hands a literal of a type without a contract to a parameter under
// keeps, which would run it after the call.
//
// @Requires reg != nil
// @Modifies reg
// @Ensures True
func AddsRaw(reg *keepslib.Registry) {
	reg.AddRaw(func(n int) {}) // want `cannot verify AddsRaw: the function literal is handed to AddRaw as f, which its trusted contract lists under keeps, and whose type func\(int\) has no contract; declare a named function type with a contract and pass a value of it`
}

// Maker makes a box.
//
// @Requires r != nil
// @Ensures True
type Maker func(r io.Reader) (b *keepslib.Box)

// MakesMaker makes a value of a trusted function that keeps what it is
// given.
//
// @Ensures m != nil
func MakesMaker() (m Maker) {
	return keepslib.Wrap // want `cannot verify MakesMaker: Wrap keeps code it is given, and cannot be used as a value: what it would be given would come from whoever calls the value`
}

// Server fires the registry it holds.
type Server struct {
	reg *keepslib.Registry
}

// serve fires the registry again, so a handler made of it calls back into
// what calls it.
//
// @Requires s != nil And s.reg != nil And n >= 0
// @Ensures True
func (s *Server) serve(n int) {
	s.reg.Fire(n)
}

// Loops keeps a handler that fires the registry it is kept in: Fire would
// run it, and it would run Fire, with nothing to show that this ends.
//
// @Requires s != nil And s.reg != nil
// @Modifies s.reg
// @Ensures True
func Loops(s *Server) {
	s.reg.Add(func(n int) { s.serve(n) }) // want `cannot verify Loops: the function literal used as a value calls serve, which may call through a function value or an interface value: serve calls Fire, which is trusted and runs what r holds`
	s.reg.Fire(1)
}

// Again reads by filling a box, so a box that keeps it calls back into
// itself.
type Again struct {
	box *keepslib.Box
}

// Read fills p through the box.
//
// @Requires |p| > 0
// @Modifies p
// @Ensures 0 <= n And n <= |p| And err = nil
func (a Again) Read(p []byte) (n int, err error) {
	if a.box == nil {
		return 0, nil
	}
	return a.box.Fill(p), nil // want `this call may not end: Again.Read hands a.box to a.box.Fill\(p\) at defects.go:\d+:\d+, which may run Again.Read`
}

// Cycles keeps a reader whose Read fills the box it is kept in.
//
// @Ensures True
func Cycles() {
	var a Again
	a.box = keepslib.Wrap(a) // want `cannot verify Cycles: Read may call through a function value or an interface value.*Read calls Fill, which is trusted and runs what b holds, which can be a value of io.Reader`
	_ = a.box.Fill(make([]byte, 1))
}

// Drained reads by handing a closer that keeps it to Consume: a closer, of
// an interface whose contracts speak of a state, now holds code that
// verified code made, so Consume counts as a call through a value.
type Drained struct{}

// Read hands a closer over a zero reader to Consume.
//
// @Requires |p| > 0
// @Modifies p
// @Ensures 0 <= n And n <= |p| And err = nil
func (Drained) Read(p []byte) (n int, err error) {
	p[0] = 0
	drain() // want `this call may not end: Drained.Read calls drain at defects.go:\d+:\d+, drain hands keepslib.Closing\(Drained\{\}\) to keepslib.Consume\(keepslib.Closing\(Drained\{\}\)\) at defects.go:\d+:\d+, which may run Drained.Read`
	return 1, nil
}

// @Ensures True
func drain() {
	keepslib.Consume(keepslib.Closing(Drained{})) // want `cannot verify drain: Read may call through a function value or an interface value.*Read calls drain, which calls Consume`
}

// Drains keeps a reader that drains itself in a closer, and drains it.
//
// @Ensures True
func Drains() {
	keepslib.Consume(keepslib.Closing(Drained{})) // want `cannot verify Drains: Read may call through a function value or an interface value.*Read calls drain, which calls Consume, which is trusted and runs what rc holds, which can be a value of io.ReadCloser, whose methods all have contracts, so that it can hold code that verified code made`
}

// KeepsInCountField keeps a handler in a registry, and its modifies lists only a
// count, which cannot hold one.
//
// @Requires reg != nil
// @Ensures True
func KeepsInCountField(reg *keepslib.Registry) {
	reg.AddCounted(show) // want `its keeps lists h as kept in r, but nothing its modifies lists under r can hold it`
}
