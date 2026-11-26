// Package unseen converts values of the types of another module to
// interfaces of that module whose methods nobody verified (F39, part A).
// The methods are code no verified function calls: what they do is
// answered for by the entry of the code that runs them.
package unseen

import (
	"bufio"
	"io"

	"unseensdk"
)

// Handle builds a result as an MCP handler does and hands it back.
//
// @Ensures result != nil
func Handle(msg string) (result *unseensdk.Result) {
	return &unseensdk.Result{Content: []unseensdk.Content{&unseensdk.Text{Text: msg}}}
}

// HandleLocal builds the result in a variable whose address it returns.
//
// @Ensures result != nil And |result.Content| = 1
func HandleLocal(msg string) (result *unseensdk.Result) {
	var res unseensdk.Result
	res.Content = []unseensdk.Content{&unseensdk.Text{Text: msg}}
	return &res
}

// Reply keeps a content in a struct of the project.
type Reply struct {
	C    unseensdk.Content
	Code int
}

// Keep returns a reply that holds a content.
//
// @Ensures r.Code = 200 And r.C != nil
func Keep(msg string) (r Reply) {
	return Reply{C: &unseensdk.Text{Text: msg}, Code: 200}
}

// Back asserts the content back to the text it holds.
//
// @Ensures r = msg
func Back(msg string) (r string) {
	var c unseensdk.Content = &unseensdk.Text{Text: msg}
	t, ok := c.(*unseensdk.Text)
	if !ok {
		return msg
	}
	return t.Text
}

// Sent hands a result to a function of the SDK whose entry says that what
// it runs writes nothing, and reads the slice the content holds after.
//
// @Requires |data| > 0
// @Modifies data
// @Ensures r
func Sent(data []byte) (r bool) {
	data[0] = 7
	res := &unseensdk.Result{Content: []unseensdk.Content{&unseensdk.Text{Data: data}}}
	_, _ = unseensdk.Send(res)
	return data[0] == 7
}

// SentTwice hands one content to two functions.
//
// @Ensures True
func SentTwice(msg string) {
	c := &unseensdk.Text{Text: msg}
	res := &unseensdk.Result{Content: []unseensdk.Content{c}}
	_, _ = unseensdk.Send(res)
	_, _ = unseensdk.Send(res)
}

// MadeHere hands a text it made to Run, whose Bump writes the text, and
// says the count is unchanged, which is false (pa5 of the design review).
//
// @Ensures r
func MadeHere() (r bool) {
	t := &unseensdk.Text{}
	unseensdk.Run(t) // want `Run may modify the footprint of t, which MadeHere may not modify; it is a \*unseensdk.Text converted to unseensdk.Bumper, whose method for Bumper.Bump is code of another module that nobody verified`
	return t.N == 0 // want `postcondition may not hold: r`
}

// DataKept hands Run a text over a slice and reads the slice after.
//
// @Requires |data| > 0
// @Modifies data
// @Ensures r
func DataKept(data []byte) (r bool) {
	data[0] = 7
	t := &unseensdk.Text{Data: data}
	unseensdk.Run(t) // want `Run may modify the footprint of t`
	return data[0] == 7 // want `postcondition may not hold: r`
}

// Wrapped writes through a writer that keeps a text it made, whose Write
// bumps the text (pa6 of the design review).
//
// @Ensures r
func Wrapped() (r bool) {
	t := &unseensdk.Text{}
	w := unseensdk.WrapIO(t)
	_, _ = w.Write([]byte("x")) // want `w.Write may modify the footprint of w, which Wrapped may not modify`
	return t.N == 0 // want `postcondition may not hold: r`
}

// up and DownHidden hide a cycle in a box of the SDK, whose Fire runs the
// hook (pa7 of the design review).
//
// @Requires k >= 0
// @Ensures True
// @Variant k
func up(k int) (n int) {
	if k == 0 {
		return 0
	}
	return DownHidden(k - 1)
}

// DownHidden hands the box to FireAll.
//
// @Requires k >= 0
// @Ensures True
// @Variant k
func DownHidden(k int) (n int) {
	return unseensdk.FireAll(&unseensdk.KBox{F: up, K: k}) // want `converting a \*unseensdk.KBox to unseensdk.Firer is not supported: Firer.Fire has no contract, and its implementation is code of another module that could run what the value holds, under no claim; its field F \(unseensdk.KHook\) is a function value`
}

// FirePlain hands FireAll a value that holds no code.
//
// @Requires k >= 0
// @Ensures True
func FirePlain(k int) (n int) {
	return unseensdk.FireAll(&unseensdk.Plain{K: k})
}

// FireHolder hands FireAll a value that holds a writer.
//
// @Requires w != nil
// @Ensures True
func FireHolder(w io.Writer) (n int) {
	return unseensdk.FireAll(&unseensdk.Holder{W: w}) // want `converting a \*unseensdk.Holder to unseensdk.Firer is not supported: .*its field W \(io.Writer\) is an interface value of io.Writer, whose methods all have contracts`
}

// mine is a sink of the project, whose Put has a contract.
type mine struct{ n int }

// Put counts.
//
// @Requires m != nil
// @Modifies m
// @Ensures True
func (m *mine) Put(s string) {
	if m.n < 1000 {
		m.n++
	}
}

// FillMine converts a sink of the project to the SDK's Sink, whose Put has
// no contract: the project's own method still needs one there.
//
// @Ensures True
func FillMine() {
	unseensdk.Fill(&mine{}) // want `converting a \*unseen.mine to unseensdk.Sink is not supported: its method Sink.Put has no contract, so nothing would say what code that calls it may rely on`
}

// FillLines converts a sink of the SDK to the same interface and hands it
// to a function whose entry says it writes it: nothing is known of what
// Put writes, so nothing a frame lists covers it.
//
// @Ensures True
func FillLines() {
	l := &unseensdk.Lines{}
	unseensdk.Fill(l) // want `Fill may modify the footprint of l, which FillLines may not modify; it is a \*unseensdk.Lines converted to unseensdk.Sink, whose method for Sink.Put is code of another module that nobody verified, so nothing is known of what it writes, converted at unseen.go:178:17; hand the value only to functions whose contracts do not write it`
}

// FireBox converts an instance of a generic type of the SDK.
//
// @Ensures True
func FireBox() (n int) {
	return unseensdk.FireAll(&unseensdk.Box[int]{V: 1}) // want `converting a \*unseensdk.Box\[int\] to unseensdk.Firer is not supported: its method Firer.Fire has no contract, and \*unseensdk.Box\[int\] is an instance of a generic type of another module`
}

// marshaler is an interface of the project without contracts.
type marshaler interface {
	MarshalJSON() ([]byte, error)
}

// Own converts a text of the SDK to an interface of the project.
//
// @Ensures m != nil
func Own(msg string) (m marshaler) {
	return &unseensdk.Text{Text: msg}
}

// outer embeds a text of the SDK: its methods are promoted, and so the
// project's.
type outer struct {
	*unseensdk.Text
}

// Promoted converts a struct of the project with a promoted method.
//
// @Ensures True
func Promoted(msg string) (m marshaler) {
	return outer{&unseensdk.Text{Text: msg}} // want `converting a unseen.outer to unseen.marshaler is not supported: its method marshaler.MarshalJSON has no contract, so nothing would say`
}

// flusher is an interface of the project without contracts.
type flusher interface {
	Flush() error
}

// Buffered converts a writer of the standard library that calls through
// what it keeps, which the methods nobody verified would run.
//
// @Requires w != nil
// @Ensures True
func Buffered(w io.Writer) (f flusher) {
	return bufio.NewWriter(w) // want `converting a value of type \*bufio.Writer to flusher is not supported yet: its Write calls through the writer it keeps`
}

// Shut converts to an interface with a state.
//
// @Ensures True
func Shut() (s unseensdk.Shutter) {
	return &unseensdk.Door{} // want `converting a \*unseensdk.Door to unseensdk.Shutter is not supported: its method Shutter.Shut has no contract, and the interface has states`
}

// Call calls a method nobody verified.
//
// @Requires c != nil
// @Ensures True
func Call(c unseensdk.Content) {
	_, _ = c.MarshalJSON() // want `c.MarshalJSON calls Content.MarshalJSON, which has no contract`
}

// AsWriter uses the value of an assertion to an interface the operand's
// type lacks (R2).
//
// @Requires c != nil
// @Ensures True
func AsWriter(c unseensdk.Content) {
	if w, ok := c.(io.Writer); ok { // want `using the value of c.\(io.Writer\) is not supported: io.Writer has the method Write, which unseensdk.Content does not have`
		_, _ = w.Write(nil)
	}
}
