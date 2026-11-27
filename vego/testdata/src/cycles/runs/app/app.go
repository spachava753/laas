// Package app hands lib and uses values whose methods call back (F43, step
// 1). Code that is not verified makes the values, as a main would; the
// verified functions are handed them.
package app

import (
	"bufio"
	"io"

	"cycles/runs/lib"
	"cycles/runs/libg"
	"cycles/runs/libr"
	"cycles/runs/uses"
)

// T reads, and its Read, which is not verified, calls back into each
// verified function of the package that hands a T on.
type T struct{}

func (T) Read(p []byte) (int, error) {
	UseCount(box)
	UsePull(box)
	UseVia(box.R)
	UseLater(box)
	UseNext(src)
	return 0, io.EOF
}

var (
	box = &lib.Box{}
	src lib.Source
)

// Setup is not verified.
func Setup() {
	box.R = T{}
	src = lib.NewWrap(T{})
}

// UseCount hands lib.Count a box that holds a T; Count runs nothing of it.
//
// @Requires b != nil
// @Ensures True
func UseCount(b *lib.Box) (n int) { return lib.Count(b) }

// @Requires b != nil And b.R != nil
// @Modifies b.R
// @Ensures True
func UsePull(b *lib.Box) { lib.Pull(b) } // want `this call may not end: UsePull hands b to lib.Pull\(b\) at app.go:\d+:\d+, which may run T.Read, T.Read calls UsePull at app.go:\d+:\d+; .*; cycles/runs/lib.Pull may run the methods named Read`

// @Requires r != nil
// @Modifies r
// @Ensures True
func UseVia(r io.Reader) { lib.Via(r) } // want `this call may not end: UseVia hands r to lib.Via\(r\) at app.go:\d+:\d+, which may run T.Read, T.Read calls UseVia at app.go:\d+:\d+; .*; cycles/runs/lib.Via may run the methods named Read`

// @Requires b != nil And b.R != nil
// @Modifies b.R
// @Ensures True
func UseLater(b *lib.Box) { lib.Later(b) } // want `this call may not end: UseLater hands b to lib.Later\(b\) at app.go:\d+:\d+, which may run T.Read, T.Read calls UseLater`

// @Requires x != nil
// @Ensures True
func UseNext(x lib.Source) (c byte) { return uses.Next(x) } // want `this call may not end: UseNext hands x to uses.Next\(x\) at app.go:\d+:\d+, which may run T.Read, T.Read calls UseNext.*cycles/runs/uses.Next may run the methods named Next, Read`

// hook calls back into UseFire; it is not verified.
func hook() int { return UseFire(box) }

// SetHook is not verified.
func SetHook() { box.F = hook }

// @Requires b != nil
// @Ensures True
func UseFire(b *lib.Box) (n int) { return lib.Fire(b) } // want `this call may not end: UseFire hands b to lib.Fire\(b\) at app.go:\d+:\d+, which may run hook, hook calls UseFire`

// M encodes as JSON by calling back into UseName; it is not verified.
type M struct{}

func (M) MarshalJSON() ([]byte, error) {
	UseName(lib.Encoded{V: M{}})
	return []byte("1"), nil
}

// @Requires x != nil
// @Ensures True
func UseName(x lib.Namer) (s string) { return uses.Name(x) } // want `this call may not end: UseName hands x to uses.Name\(x\) at app.go:\d+:\d+, which may run UseName`

// R reads, and its Read calls back into UseRun; it is not verified.
type R struct{}

func (R) Read(p []byte) (int, error) {
	UseRun(lib.Valued{BR: bufio.NewReader(R{})})
	return 0, io.EOF
}

// @Requires x != nil
// @Ensures True
func UseRun(x lib.Runner) { uses.Run(x) } // want `this call may not end: UseRun hands x to uses.Run\(x\) at app.go:\d+:\d+, which may run R.Read, R.Read calls UseRun`

// Exported calls back into UseTime. hidden.F, which lib calls by its
// symbol, calls it.
func Exported() { UseTime(lib.Timed{}) }

// @Requires x != nil
// @Ensures True
func UseTime(x lib.Timer) (n int64) { return uses.Time(x) } // want `this call may not end: UseTime hands x to uses.Time\(x\) at app.go:\d+:\d+, which may run UseTime`

// S is formatted, and its String calls back into UseLabel; it is not
// verified.
type S struct{}

func (S) String() string {
	UseLabel(lib.Printed{V: S{}})
	return ""
}

// @Requires x != nil
// @Ensures True
func UseLabel(x lib.Labeler) (s string) { return uses.Label(x) } // want `this call may not end: UseLabel hands x to uses.Label\(x\) at app.go:\d+:\d+, which may run S.String, S.String calls UseLabel`

// V is shown by reflection, and its String calls back into UseShow; it is
// not verified.
type V struct{}

func (V) String() string {
	UseShow(libr.Reflected{V: V{}})
	return ""
}

// @Requires x != nil
// @Ensures True
func UseShow(x libr.Shower) { uses.Show(x) } // want `this call may not end: UseShow hands x to uses.Show\(x\) at app.go:\d+:\d+, which may run`

// seq calls back into UseRange; it is not verified.
func seq(yield func(int) bool) { UseRange(lib.Ranged{Seq: seq}) }

// @Requires x != nil
// @Ensures True
func UseRange(x lib.Ranger) { uses.Range(x) } // want `this call may not end: UseRange hands x to uses.Range\(x\) at app.go:\d+:\d+, which may run seq, seq calls UseRange`

// U reads, and its Read calls back into UseVal; it is not verified.
type U struct{}

func (U) Read(p []byte) (int, error) {
	UseVal(lib.MethodValued{R: U{}})
	return 0, io.EOF
}

// @Requires x != nil
// @Ensures True
func UseVal(x lib.Valuer) { uses.Val(x) } // want `this call may not end: UseVal hands x to uses.Val\(x\) at app.go:\d+:\d+, which may run U.Read, U.Read calls UseVal`

// W calls back into UseGen; it is not verified.
type W struct{}

func (W) Back() { UseGen(libg.Generic{V: W{}}) }

// @Requires x != nil
// @Ensures True
func UseGen(x libg.Genner) { uses.Gen(x) } // want `this call may not end: UseGen hands x to uses.Gen\(x\) at app.go:\d+:\d+, which may run`

// pred calls back into UseIndex; it is not verified.
func pred(r rune) bool { return UseIndex(pred) > 0 }

// @Requires p != nil
// @Ensures True
func UseIndex(p lib.Pred) (i int) { return lib.Index("ab", p) } // want `this call may not end: UseIndex hands p to lib.Index\("ab", p\) at app.go:\d+:\d+, which may run pred, pred calls UseIndex`
