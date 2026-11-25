package arraystructs

import (
	"encoding/json"
	"fmt"
	"io"
)

// A struct that holds an array of elements larger than a byte is not
// modelled, as at the base, whatever else it holds and wherever it lies:
// beside another struct, in a slice, inside another struct, converted,
// owned, or handed to a callee (F1 of the design review).

type plain struct{ n int }

// @Requires p != nil
// @Modifies p
// @Ensures err = nil
func (p *plain) Write(b []byte) (n int, err error) {
	p.n = 1
	return 0, nil
}

type wide struct {
	t   plain
	arr [4]int64
}

// @Ensures False
func Beside() {
	u := new(wide) // want `cannot verify Beside: u has unsupported type \*arraystructs\.wide; arraystructs\.wide holds an array of int64 in `
	var w io.Writer = &u.t
	w.Write(nil)
	_ = u.arr[0]
}

// @Ensures True
func InSliceWide(ws []wide) (r int) {
	return int(ws[0].arr[0]) // want `cannot verify InSliceWide: ws\[0\] has unsupported type arraystructs\.wide; arraystructs\.wide holds an array of i`
}

type outer struct {
	in wide
}

// @Ensures True
func Nested(o *outer) { // want `cannot verify Nested: parameter o has unsupported type \*arraystructs\.outer; arraystructs\.outer holds an array `
}

// @Ensures True
func Handed(w *wide) { // want `cannot verify Handed: parameter w has unsupported type \*arraystructs\.wide; arraystructs\.wide holds an array of`
}

// An array of one byte is modelled in a struct; on 386, where an int64 is
// aligned to four, it would lie at four, and larger elements are refused.
type aligned struct {
	x byte
	y [2]int64
}

// @Ensures True
func Aligned(a *aligned) { // want `cannot verify Aligned: parameter a has unsupported type \*arraystructs\.aligned; arraystructs\.aligned holds an a`
}

// A pointer to a struct with an array converted to an interface.
//
// @Requires b != nil
// @Modifies b
// @Ensures err = nil
func (b *buffer) Write(p []byte) (n int, err error) {
	b.n = 0
	return 0, nil
}

// @Ensures True
func Convert() (w io.Writer) {
	return &buffer{} // want `cannot verify Convert: converting a \*buffer to io\.Writer is not supported yet: what it points to holds an arra`
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
