package jsondec

import "encoding/json"

// Decoding through a pointer writes the fields themselves (F25 of the
// review of step 3), and keeps what json does not write; an unexported
// embedded struct is decoded into (F26).

// Inner is what a pointer of Holder points to.
type Inner struct{ X int }

// Holder holds a field of each kind json writes, and two it does not.
type Holder struct {
	Tags []string
	M    map[string]int
	P    *Inner
	B    []byte
	n    int
	s    string
}

// LocalSlice states that the decoded slice is empty, which it need not be.
//
// @Requires |a| <= 1000
// @Ensures err = nil -> |r.Tags| = 0
func LocalSlice(a []byte) (r Holder, err error) {
	err = json.Unmarshal(a, &r)
	return r, err // want `postcondition may not hold: err = nil -> \|r\.Tags\| = 0`
}

// LocalMap states that the decoded map is nil.
//
// @Requires |a| <= 1000
// @Ensures err = nil -> r.M = nil
func LocalMap(a []byte) (r Holder, err error) {
	err = json.Unmarshal(a, &r)
	return r, err // want `postcondition may not hold: err = nil -> r\.M = nil`
}

// LocalPtr states that the decoded pointer is nil.
//
// @Requires |a| <= 1000
// @Ensures err = nil -> r.P = nil
func LocalPtr(a []byte) (r Holder, err error) {
	err = json.Unmarshal(a, &r)
	return r, err // want `postcondition may not hold: err = nil -> r\.P = nil`
}

// LocalBytes states that the decoded bytes are empty.
//
// @Requires |a| <= 1000
// @Ensures err = nil -> |r.B| = 0
func LocalBytes(a []byte) (r Holder, err error) {
	err = json.Unmarshal(a, &r)
	return r, err // want `postcondition may not hold: err = nil -> \|r\.B\| = 0`
}

// EmptyThrough states the same through a pointer it is handed.
//
// @Requires p != nil And cap(p.Tags) = 0 And cap(p.B) = 0 And p.M = nil And p.P = nil And |a| <= 1000
// @Modifies p
// @Ensures err = nil -> |p.Tags'| = 0
func EmptyThrough(a []byte, p *Holder) (err error) {
	return json.Unmarshal(a, p) // want `postcondition may not hold: err = nil -> \|p\.Tags'\| = 0`
}

// KeptThrough relies on what json does not write, through the pointer.
//
// @Requires p != nil And cap(p.Tags) = 0 And cap(p.B) = 0 And p.M = nil And p.P = nil And |a| <= 1000
// @Modifies p
// @Ensures p.n' = p.n And p.s' = p.s
func KeptThrough(a []byte, p *Holder) {
	_ = json.Unmarshal(a, p)
}

// Kept relies on an unexported field keeping its value.
//
// @Requires |a| <= 1000
// @Ensures k = 7
func Kept(a []byte) (k int) {
	var r Holder
	r.n = 7
	_ = json.Unmarshal(a, &r)
	return r.n
}

// Twice decodes into a value that the first decode may have filled.
//
// @Requires |a| <= 1000
// @Ensures True
func Twice(a []byte) (err error) {
	var r Holder
	if err = json.Unmarshal(a, &r); err != nil {
		return err
	}
	return json.Unmarshal(a, &r) // want `Unmarshal may decode into memory that r\.Tags refers to, which the caller may hold: it appends into a slice's array, keeps a map's entries, and decodes through a pointer it finds; decode into a value w` `Unmarshal may decode into memory that r\.M refers to, which the caller may hold: it appends into a slice's array, keeps a map's entries, and decodes through a pointer it finds; decode into a value whos` `Unmarshal may decode into memory that r\.P refers to, which the caller may hold: it appends into a slice's array, keeps a map's entries, and decodes through a pointer it finds; decode into a value whos` `Unmarshal may decode into memory that r\.B refers to, which the caller may hold: it appends into a slice's array, keeps a map's entries, and decodes through a pointer it finds; decode into a value whos`
}

// TwiceFresh decodes the second time into a value of its own.
//
// @Requires |a| <= 1000
// @Ensures True
func TwiceFresh(a []byte) (err error) {
	var r Holder
	if err = json.Unmarshal(a, &r); err != nil {
		return err
	}
	var again Holder
	return json.Unmarshal(a, &again)
}

// tagged is embedded and not exported; json decodes its exported fields.
type tagged struct {
	Tags []string
	k    int
}

// Wrapped embeds it.
type Wrapped struct {
	tagged
	Name string
}

// Embedded decodes into a struct that embeds an unexported struct, whose
// unexported field keeps its value.
//
// @Requires |data| <= 1000
// @Ensures k = 3
func Embedded(data []byte) (k int) {
	var w Wrapped
	w.k = 3
	_ = json.Unmarshal(data, &w)
	return w.k
}

// Hidden has an unexported slice, which Unmarshal leaves as it was.
type Hidden struct {
	Name string
	seen []int
}

// IntoHidden decodes into it.
//
// @Requires |data| <= 1000
// @Ensures True
func IntoHidden(data []byte) (err error) {
	var h Hidden
	return json.Unmarshal(data, &h) // want `cannot verify IntoHidden: Unmarshal decodes into &h, and its field seen is a slice that Unmarshal leaves as it was, which vego cannot yet state; decode into a type without the field, and copy from it what you need`
}
