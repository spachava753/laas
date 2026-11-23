package jsonenc

import "encoding/json"

// Ordinary shapes that must prove at the default limit from honest bounds
// of a thousand, written in the Requires and on the type (F15 of the
// review of step 1), and the length of what Marshal returns (F17).

// RecM holds a map of slices.
type RecM struct {
	M map[string][]string
}

// MapOfSlices encodes a map of slices below a field: refused, since vego
// does not bound the elements of a slice that is a map's value under a
// quantifier over the keys.
//
// @Requires r != nil And |r.M| <= 1000 And (Forall k in r.M : |k| <= 1000 And |r.M[k]| <= 1000 And (Forall j in [0, |r.M[k]|) : |r.M[k][j]| <= 1000))
// @Ensures True
func MapOfSlices(r *RecM) (n int) {
	js, _ := json.Marshal(r) // want `cannot verify MapOfSlices: Marshal encodes r, and r\.M\[k\] holds elements inside the value of r\.M, a map with string keys, and vego cannot yet bound what they hold under a quantifier over the keys; enco`
	return len(js)
}

// RecS holds a map of strings.
type RecS struct {
	M map[string]string
}

// MapOfStrings encodes a map of strings below a field.
//
// @Requires r != nil And |r.M| <= 1000 And (Forall k in r.M : |k| <= 1000 And |r.M[k]| <= 1000)
// @Ensures True
func MapOfStrings(r *RecS) (n int) {
	js, _ := json.Marshal(r)
	return len(js)
}

// TopMapOfSlices encodes a map of slices handed directly, refused the same
// way.
//
// @Requires |m| <= 1000 And (Forall k in m : |k| <= 1000 And |m[k]| <= 1000 And (Forall j in [0, |m[k]|) : |m[k][j]| <= 1000))
// @Ensures True
func TopMapOfSlices(m map[string][]string) (n int) {
	js, _ := json.Marshal(m) // want `cannot verify TopMapOfSlices: Marshal encodes m, and m\[k\] holds elements inside the value of m, a map with string keys, and vego cannot yet bound what they hold under a quantifier over the keys; encod`
	return len(js)
}

// Rec3 holds two slices of strings and a string.
type Rec3 struct {
	A    []string
	B    []string
	Name string
}

// TwoSlicesName encodes two slices of strings and a string.
//
// @Requires r != nil And |r.Name| <= 1000 And |r.A| <= 1000 And |r.B| <= 1000 And (Forall i in [0, |r.A|) : |r.A[i]| <= 1000) And (Forall i in [0, |r.B|) : |r.B[i]| <= 1000)
// @Ensures True
func TwoSlicesName(r *Rec3) (n int) {
	js, _ := json.Marshal(r)
	return len(js)
}

// Rec5 holds two slices of strings, a map of strings, and a string.
type Rec5 struct {
	A    []string
	B    []string
	M    map[string]string
	Name string
}

// SeveralFlat encodes all four with a map of strings.
//
// @Requires |r.Name| <= 1000 And |r.A| <= 1000 And |r.B| <= 1000 And |r.M| <= 1000 And (Forall i in [0, |r.A|) : |r.A[i]| <= 1000) And (Forall i in [0, |r.B|) : |r.B[i]| <= 1000) And (Forall k in r.M : |k| <= 1000 And |r.M[k]| <= 1000)
// @Ensures True
func SeveralFlat(r Rec5) (n int) {
	js, _ := json.Marshal(r)
	return len(js)
}

// Rec4 holds two slices of strings, a map of slices, and a string.
type Rec4 struct {
	A    []string
	B    []string
	M    map[string][]string
	Name string
}

// Several encodes all four, bounded in the nested form the message
// suggests: refused for its map of slices.
//
// @Requires |r.Name| <= 1000 And |r.A| <= 1000 And |r.B| <= 1000 And |r.M| <= 1000 And (Forall i in [0, |r.A|) : |r.A[i]| <= 1000) And (Forall i in [0, |r.B|) : |r.B[i]| <= 1000) And (Forall k in r.M : |k| <= 1000 And |r.M[k]| <= 1000 And (Forall j in [0, |r.M[k]|) : |r.M[k][j]| <= 1000))
// @Ensures True
func Several(r Rec4) (n int) {
	js, _ := json.Marshal(r) // want `cannot verify Several: Marshal encodes r, and r\.M\[k\] holds elements inside the value of r\.M, a map with string keys, and vego cannot yet bound what they hold under a quantifier over the keys; encode a`
	return len(js)
}

// IndentParams indents with a prefix and an indent it is handed.
//
// @Requires |prefix| <= 100 And |indent| <= 100 And |ls| <= 1000 And (Forall i in [0, |ls|) : |ls[i].Name| <= 1000 And |ls[i].Tags| <= 1000 And (Forall j in [0, |ls[i].Tags|) : |ls[i].Tags[j]| <= 1000))
// @Ensures True
func IndentParams(ls []Loose, prefix, indent string) (n int) {
	js, _ := json.MarshalIndent(ls, prefix, indent)
	return len(js)
}

// SeparateClauses bounds one slice in two quantified clauses.
//
// @Requires |ls| <= 1000 And (Forall i in [0, |ls|) : |ls[i].Name| <= 1000 And |ls[i].Tags| <= 1000) And (Forall i in [0, |ls|) : (Forall j in [0, |ls[i].Tags|) : |ls[i].Tags[j]| <= 1000))
// @Ensures True
func SeparateClauses(ls []Loose) (n int) {
	js, _ := json.Marshal(ls)
	return len(js)
}

// Catalog bounds what it holds on its type.
//
// @Invariant |Name| <= 1000 And |A| <= 1000 And (Forall i in [0, |A|) : |A[i]| <= 1000) And |M| <= 1000 And (Forall k in M : |k| <= 1000 And |M[k]| <= 1000)
type Catalog struct {
	Name string
	A    []string
	M    map[string]string
}

// OnTheType encodes a Catalog whose invariant gives every bound.
//
// @Requires c != nil
// @Ensures True
func OnTheType(c *Catalog) (n int) {
	js, _ := json.Marshal(c)
	return len(js)
}

// Line appends a newline to what Marshal returns, whose length the bound
// gives.
//
// @Requires |l.Name| <= 100 And |l.Tags| <= 10 And (Forall i in [0, |l.Tags|) : |l.Tags[i]| <= 100)
// @Ensures err = nil -> |out| >= 1
func Line(l Loose) (out []byte, err error) {
	js, err := json.Marshal(l)
	if err != nil {
		return nil, err
	}
	out = append(js, '\n')
	return out, nil
}
