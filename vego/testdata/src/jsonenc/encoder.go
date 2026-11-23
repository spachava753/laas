package jsonenc

import (
	"bufio"
	"bytes"
	"encoding/json"
	"io"
	"net/http"
	"os"
)

// json.NewEncoder(w).Encode(v), written as one expression (F29, step 2):
// verified as Marshal followed by w's own Write of what it returns and a
// newline; the encoder lives for the expression and keeps nothing.

// Item bounds its text.
//
// @Invariant |Text| <= 1000
type Item struct{ Text string }

// Handler encodes into the writer of a handler, which is never kept.
//
// @Requires w != nil And |its| <= 1000 And (Forall i in [0, |its|) : valid(its[i]))
// @Modifies w
// @Ensures True
func Handler(w http.ResponseWriter, its []Item) {
	w.Header().Set("Content-Type", "application/json")
	json.NewEncoder(w).Encode(its)
}

// ToWriter encodes into a writer it is handed.
//
// @Requires out != nil
// @Modifies out
// @Ensures True
func ToWriter(out io.Writer, it Item) (err error) {
	return json.NewEncoder(out).Encode(it)
}

// ToFile encodes into a file, whose Write writes nothing verified code
// sees.
//
// @Requires f != nil
// @Ensures True
func ToFile(f *os.File, it Item) (err error) {
	return json.NewEncoder(f).Encode(it)
}

// ToBufio encodes into a bufio.Writer through its own Write.
//
// @Requires bw != nil And ready(bw)
// @Modifies bw
// @Ensures True
func ToBufio(bw *bufio.Writer, it Item) (err error) {
	return json.NewEncoder(bw).Encode(it)
}

// ToBuffer encodes into a bytes.Buffer, whose Write needs a bound on what
// it is given: the bound of what Encode writes gives it.
//
// @Requires b != nil And |b| <= 1000
// @Modifies b
// @Ensures True
func ToBuffer(b *bytes.Buffer, it Item) (err error) {
	return json.NewEncoder(b).Encode(it)
}

// Unlisted does not list the writer.
//
// @Requires out != nil
// @Ensures True
func Unlisted(out io.Writer, it Item) (err error) {
	return json.NewEncoder(out).Encode(it) // want `out\.Write may modify the footprint of out, which Unlisted may not modify; list it in a // @Modifies clause`
}

// Held keeps the encoder in a variable.
//
// @Requires out != nil
// @Modifies out
// @Ensures True
func Held(out io.Writer, it Item) (err error) {
	enc := json.NewEncoder(out) // want `cannot verify Held: json\.NewEncoder keeps w in the encoder it returns; write json\.NewEncoder\(w\)\.Encode\(v\) in one expression, since an encoder held in a variable is not supported yet`
	return enc.Encode(it)
}

// Given is handed an encoder that may indent or hold an earlier error.
//
// @Requires enc != nil
// @Ensures True
func Given(enc *json.Encoder, it Item) (err error) {
	return enc.Encode(it) // want `cannot verify Given: Encode is verified only on a new encoder, written as json\.NewEncoder\(w\)\.Encode\(v\) in one expression: an Encoder made elsewhere may indent, may not escape HTML, or may hold an earl`
}

// EncodeDeferred would lose the error.
//
// @Requires out != nil
// @Modifies out
// @Ensures True
func EncodeDeferred(out io.Writer, it Item) {
	defer json.NewEncoder(out).Encode(it) // want `cannot verify EncodeDeferred: deferring json\.NewEncoder\(w\)\.Encode\(v\) is not supported: what it returns would be lost, and what it encodes is checked where it is called`
}

// NilWriter hands NewEncoder a nil writer, on which Encode panics.
//
// @Ensures True
func NilWriter(it Item) (err error) {
	var out io.Writer
	return json.NewEncoder(out).Encode(it) // want `the writer out handed to json\.NewEncoder may be nil`
}

// FormatsErr reads the text of an error that may be the writer's.
//
// @Requires out != nil
// @Modifies out
// @Ensures True
func FormatsErr(out io.Writer, it Item) (s string) {
	if err := json.NewEncoder(out).Encode(it); err != nil {
		return err.Error() // want `cannot verify FormatsErr: calling Error on err would run the methods of an error whose origin is not known; only an error made by errors\.New or fmt\.Errorf, here or in a verified function, or one that `
	}
	return ""
}

// Loop is a writer whose Write encodes into itself again.
type Loop struct{ N int }

// Write calls EncodeTo, which calls Write.
//
// @Requires l != nil
// @Modifies l
// @Ensures 0 <= n
func (l *Loop) Write(p []byte) (n int, err error) {
	_ = EncodeTo(l, Item{}) // want `recursive call needs a // @Variant annotation in the doc comment of Write to prove termination; the cycle: \(\*Loop\)\.Write calls EncodeTo at encoder\.go:132:6, EncodeTo calls \(\*Loop\)\.Write at encoder\.go:`
	return 0, nil
}

// EncodeTo encodes into a Loop.
//
// @Requires l != nil
// @Modifies l
// @Ensures True
func EncodeTo(l *Loop, it Item) (err error) {
	return json.NewEncoder(l).Encode(it) // want `recursive call needs a // @Variant annotation in the doc comment of EncodeTo to prove termination; the cycle: EncodeTo calls \(\*Loop\)\.Write at encoder\.go:142:25, \(\*Loop\)\.Write calls EncodeTo at encoder`
}

// The writer's Write is chosen as a conversion to io.Writer chooses it
// (F24 of the review of step 2).

// VW has Write on its value.
type VW struct{ N int }

// Write writes nothing.
//
// @Ensures n = |p| And err = nil
func (v VW) Write(p []byte) (n int, err error) { return len(p), nil }

// ValueRecvNil hands a pointer that may be nil: Go reads what it points to
// to call Write, and panics on nil.
//
// @Ensures True
func ValueRecvNil(p *VW, it Item) (err error) {
	return json.NewEncoder(p).Encode(it) // want `VW\.Write has a value receiver, and the pointer p handed to json\.NewEncoder may be nil`
}

// ValueRecv hands a pointer that is not nil.
//
// @Requires p != nil
// @Ensures True
func ValueRecv(p *VW, it Item) (err error) {
	return json.NewEncoder(p).Encode(it)
}

// WithBuffer gets Write from an embedded field.
type WithBuffer struct {
	N int
	bytes.Buffer
}

// Promoted encodes into it.
//
// @Requires w != nil
// @Modifies w
// @Ensures True
func Promoted(w *WithBuffer, it Item) (err error) {
	return json.NewEncoder(w).Encode(it) // want `cannot verify Promoted: \*WithBuffer gets Write from an embedded field, and a promoted method cannot be used as a method of an interface yet`
}

// Wrap gets Write from an embedded interface value.
type Wrap struct {
	io.Writer
}

// ThroughWrap encodes into it.
//
// @Requires w != nil
// @Modifies w
// @Ensures True
func ThroughWrap(w *Wrap, it Item) (err error) {
	return json.NewEncoder(w).Encode(it) // want `cannot verify ThroughWrap: \*Wrap gets Write from an embedded field that holds an interface value, so it calls through that value, and code that an interface value runs cannot do that yet: no contract `
}
