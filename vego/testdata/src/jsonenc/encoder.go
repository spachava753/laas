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

// ToBuffer would need a bound on what Encode writes, which is no term.
//
// @Requires b != nil And |b| <= 1000
// @Modifies b
// @Ensures True
func ToBuffer(b *bytes.Buffer, it Item) (err error) {
	return json.NewEncoder(b).Encode(it) // want `json\.NewEncoder\(b\)\.Encode writes to b JSON whose length is not a term the logic has, and the Write of \*bytes\.Buffer needs a bound on what it is given; encode wi`
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
	enc := json.NewEncoder(out) // want `cannot verify Held: json\.NewEncoder keeps w in the encoder it returns; write json\.NewEncoder\(w\)\.Encode\(v\) in one expression, since an encoder held in a variable`
	return enc.Encode(it)
}

// Given is handed an encoder that may indent or hold an earlier error.
//
// @Requires enc != nil
// @Ensures True
func Given(enc *json.Encoder, it Item) (err error) {
	return enc.Encode(it) // want `cannot verify Given: Encode is verified only on a new encoder, written as json\.NewEncoder\(w\)\.Encode\(v\) in one expression: an Encoder made elsewhere may indent, `
}

// EncodeDeferred would lose the error.
//
// @Requires out != nil
// @Modifies out
// @Ensures True
func EncodeDeferred(out io.Writer, it Item) {
	defer json.NewEncoder(out).Encode(it) // want `cannot verify EncodeDeferred: deferring json\.NewEncoder\(w\)\.Encode\(v\) is not supported: what it returns would be lost, and what it encodes is checked where it is`
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
		return err.Error() // want `cannot verify FormatsErr: calling Error on err would run the methods of an error whose origin is not known; only an error made by errors\.New or fmt\.Errorf, here`
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
	_ = EncodeTo(l, Item{}) // want `recursive call needs a // @Variant annotation in the doc comment of Write to prove termination; the cycle: \(\*Loop\)\.Write calls EncodeTo at encoder\.go:131:6, Enc`
	return 0, nil
}

// EncodeTo encodes into a Loop.
//
// @Requires l != nil
// @Modifies l
// @Ensures True
func EncodeTo(l *Loop, it Item) (err error) {
	return json.NewEncoder(l).Encode(it) // want `recursive call needs a // @Variant annotation in the doc comment of EncodeTo to prove termination; the cycle: EncodeTo calls \(\*Loop\)\.Write at encoder\.go:141:25,`
}
