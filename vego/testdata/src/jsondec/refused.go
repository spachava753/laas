package jsondec

import "encoding/json"

// What is refused, each with its message.

// IntoUsed may decode into the array of p.Tags.
//
// @Requires p != nil And |data| <= 1000000
// @Modifies p
// @Ensures True
func IntoUsed(data []byte, p *Req) (err error) {
	return json.Unmarshal(data, p) // want `Unmarshal may decode into memory that p\.Tags refers to, which the caller may hold: it appends into a slice's array, keeps a map's entries, and decodes through a pointer it finds; decode into a value w`
}

// IntoUnlisted does not list what it decodes into.
//
// @Requires p != nil And |data| <= 1000000 And cap(p.Tags) = 0
// @Ensures True
func IntoUnlisted(data []byte, p *Req) (err error) {
	return json.Unmarshal(data, p) // want `Unmarshal may modify p, which IntoUnlisted may not modify; list it in a // @Modifies clause, as p\.Text`
}

// Unbounded decodes data of any length.
//
// @Ensures True
func Unbounded(data []byte) (err error) {
	var rt Req
	return json.Unmarshal(data, &rt) // want `precondition of Unmarshal may not hold: 16 \* \(\|data\| \+ 1\) \+ 65536 <= MaxAlloc; it holds when \|data\| <= 10000000000000`
}

// Anys decodes into an interface value.
//
// @Requires |data| <= 1000
// @Ensures True
func Anys(data []byte) (err error) {
	var v any
	return json.Unmarshal(data, &v) // want `cannot verify Anys: Unmarshal decodes into &v, and v is an interface value of type any, whose dynamic type vego does not know; use a value of a concrete type`
}

// Value decodes into a value, not a pointer.
//
// @Requires |data| <= 1000
// @Ensures True
func Value(data []byte, r Req) (err error) {
	return json.Unmarshal(data, r) // want `cannot verify Value: Unmarshal decodes into r, and r is of type Req; decode into &x for a variable x, or into a pointer to a struct`
}

// Unchanged relies on a failed decode writing nothing; it may write the
// fields before the one that failed.
//
// @Requires |data| <= 1000
// @Ensures r
func Unchanged(data []byte) (r bool) {
	var it Item
	it.Name = "x"
	if err := json.Unmarshal(data, &it); err != nil {
		return it.Name == "x" // want `postcondition may not hold: r`
	}
	return true
}

// IntoData decodes into an element of the data itself.
//
// @Requires |data| >= 1 And |data| <= 1000
// @Ensures True
func IntoData(data []byte) (err error) {
	return json.Unmarshal(data, &data[0]) // want `cannot verify IntoData: Unmarshal decodes into &data\[0\], and data\[0\] is an element of data, which is not supported; decode into a variable`
}

// Deferred loses the error.
//
// @Requires |data| <= 1000
// @Ensures True
func Deferred(data []byte) {
	var rt Req
	defer json.Unmarshal(data, &rt) // want `cannot verify Deferred: deferring a call of Unmarshal is not supported: what it returns would be lost, and what it decodes into is checked where it is called`
}

// Decoder is a function type with a contract.
//
// @Ensures True
type Decoder func(data []byte, v any) (err error)

// AsValue makes json.Unmarshal a value.
//
// @Ensures True
func AsValue() {
	var f Decoder = json.Unmarshal // want `cannot verify AsValue: Unmarshal decodes into what it is given as encoding/json does, and cannot be used as a value: what it is given is checked at each call written out, and a value is called with wh`
	_ = f(nil, nil)
}

// ownUnmarshal is a function of the project with an entry that lists
// decodes, which only the shipped entries may.
func ownUnmarshal(data []byte, v any) error {
	return json.Unmarshal(data, v)
}

// Own calls it.
//
// @Requires |data| <= 1000
// @Ensures True
func Own(data []byte) {
	var rt Req
	_ = ownUnmarshal(data, &rt) // want `the trusted contract of jsondec\.ownUnmarshal \(trusted\.yaml:\d+\) cannot be used: it lists decodes, which only the entries that come with vego can list; a function of your own that decodes into a value`
}

// B holds bytes that decode from base64.
type B struct {
	B []byte
}

// Differ relies on the errors of two calls being different, which nothing
// decides (D8 of the design review).
//
// @Ensures r
func Differ() (r bool) {
	var a, b B
	e1 := json.Unmarshal([]byte(`{"B":"!!"}`), &a)
	e2 := json.Unmarshal([]byte(`{"B":"!!"}`), &b)
	return e1 != e2 // want `postcondition may not hold: r`
}

// Same relies on them being one error.
//
// @Ensures r
func Same() (r bool) {
	var a, b B
	e1 := json.Unmarshal([]byte(`{"B":"!!"}`), &a)
	e2 := json.Unmarshal([]byte(`{"B":"!!"}`), &b)
	return e1 == e2 // want `postcondition may not hold: r`
}
