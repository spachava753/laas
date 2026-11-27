package arraystructs

import (
	"encoding/json"
	"fmt"
	"io"
)

// A struct that holds an array of elements larger than a byte was not
// modelled at the base of F36, wherever it lay: beside another struct, in a
// slice, inside another struct, converted, owned, or handed to a callee
// (F1 of the design review). Since step 3a of F42 it is, for arrays of
// numbers and booleans, and these programs verify or are refused for what
// they claim (F42, numberArray).

type plain struct{ n int }

// @Requires p != nil
// @Modifies p
// @Ensures err = nil And n = |b|
func (p *plain) Write(b []byte) (n int, err error) {
	p.n = 1
	return len(b), nil
}

type wide struct {
	t   plain
	arr [4]int64
}

// Beside converts a struct beside an array of int64 in one allocation:
// the footprint of &u.t is its bytes, which hold no element of u.arr, so
// nothing is a contradiction, and False is not proved. With F36's floor,
// u.arr lay at 1 to 4, in the footprint's [0, 8), and leafOnly made it one
// (the prototype of step 3a).
//
// @Ensures False
func Beside() {
	u := new(wide)
	var w io.Writer = &u.t
	w.Write(nil)
	_ = u.arr[0]
} // want `vego: postcondition may not hold: False`

// @Requires |ws| > 0
// @Ensures True
func InSliceWide(ws []wide) (r int) {
	return int(ws[0].arr[0])
}

type outer struct {
	in wide
}

// @Ensures True
func Nested(o *outer) {
}

// @Ensures True
func Handed(w *wide) {
}

// On 386, where an int64 is aligned to four, y lies at four, and its run
// at 4 and 5, inside its bytes [4, 20).
type aligned struct {
	x byte
	y [2]int64
}

// @Ensures True
func Aligned(a *aligned) {
}

// A pointer to a struct with an array converted to an interface.
//
// @Requires b != nil
// @Modifies b
// @Ensures err = nil And n = |p|
func (b *buffer) Write(p []byte) (n int, err error) {
	b.n = 0
	return len(p), nil
}

// Convert converts a pointer to a struct that holds an array, whose
// footprint is the struct with its array (F42, step 3a).
//
// @Ensures True
func Convert() (w io.Writer) {
	return &buffer{}
}

// Owns names a field that refers to memory, which an array is not.
//
// @Owns data // want `data cannot be owned: it holds a \[8\]byte, and a field can be owned when it holds a pointer to a struct, a slic`
type owner struct {
	data [8]byte
	n    int
}

// Formatting a struct that holds an array.
//
// @Ensures True
func Format(b buffer) (s string) {
	return fmt.Sprint(b) // want `cannot verify Format: Sprint formats b, a value of type arraystructs.buffer, and that may run code nobody has checked: arraystructs.buffer holds an array in field out, which verified code cannot format yet`
}

// A package-level struct that holds an array, whose address is taken.
var shared buffer

// @Ensures True
func Shared() (r byte) {
	return shared.out[0] // want `cannot verify Shared: shared has its address taken at refused.go:\d+; package-level structs that hold an array and whose address is taken are not supported yet`
}

func takeShared() *buffer { return &shared }

type encoded struct {
	A [4]byte
	N int
}

// encoding/json does not walk an array yet.
//
// @Ensures True
func Marshal(j encoded) (b []byte, err error) {
	return json.Marshal(j) // want `cannot verify Marshal: Marshal encodes j, and j.A is of type \[4\]byte, which encoding/json cannot encode or vego does not support`
}
