package jsonenc

import (
	"encoding/json"
	"net/http"
	"time"
)

// json.Marshal and json.MarshalIndent of values of the project's own types
// (F29): the static type of what a call hands over is walked as
// encoding/json encodes it, and what it builds is proved to fit, from the
// lengths of every string, slice, and map it holds.

// Task bounds what it holds in its invariant, so that encoding one needs
// nothing at the call.
//
// @Invariant |Text| <= 10000 And |Tags| <= 100 And (Forall j in [0, |Tags|) : |Tags[j]| <= 100)
type Task struct {
	Id   int       `json:"id"`
	Text string    `json:"text"`
	Tags []string  `json:"tags"`
	Due  time.Time `json:"due"`
}

// Get writes one task as JSON.
//
// @Requires w != nil
// @Modifies w
// @Ensures True
func Get(w http.ResponseWriter, t Task) {
	js, err := json.Marshal(t)
	if err != nil {
		http.Error(w, err.Error(), http.StatusInternalServerError)
		return
	}
	w.Header().Set("Content-Type", "application/json")
	w.Write(js)
}

// All writes tasks whose invariants hold, with a bound on how many.
//
// @Requires w != nil And |ts| <= 100000 And (Forall i in [0, |ts|) : valid(ts[i]))
// @Modifies w
// @Ensures True
func All(w http.ResponseWriter, ts []Task) {
	js, err := json.Marshal(ts)
	if err != nil {
		return
	}
	w.Write(js)
}

// Loose has no invariant; a function that encodes one bounds it.
type Loose struct {
	Name string
	Tags []string
}

// Bounded encodes loose values under a Requires that bounds each length.
//
// @Requires |ls| <= 100 And (Forall i in [0, |ls|) : |ls[i].Name| <= 100 And |ls[i].Tags| <= 100 And (Forall j in [0, |ls[i].Tags|) : |ls[i].Tags[j]| <= 100))
// @Ensures True
func Bounded(ls []Loose) (n int) {
	js, _ := json.MarshalIndent(ls, "", "  ")
	return len(js)
}

// Literal encodes a value of a type declared in the function.
//
// @Requires |name| <= 100
// @Ensures err = nil -> fresh(js)
func Literal(name string, id int) (js []byte, err error) {
	type ResponseId struct {
		Id   int    `json:"id"`
		Name string `json:"name"`
	}
	return json.Marshal(ResponseId{Id: id, Name: name})
}

// Node is reached through a pointer that may be nil: the bound of what it
// holds counts only when it is not nil (F12 of the review).
type Node struct {
	Label string
	Next  *Leaf
}

// Leaf is the end of a Node.
type Leaf struct {
	Text string
}

// Pointed encodes nodes, some of whose pointers are nil.
//
// @Requires |ns| <= 1000 And (Forall i in [0, |ns|) : |ns[i].Label| <= 1000 And (ns[i].Next != nil -> |ns[i].Next.Text| <= 1000))
// @Ensures True
func Pointed(ns []Node) (n int) {
	js, _ := json.Marshal(ns)
	return len(js)
}

// inner is embedded and not exported, and encoding/json lists its exported
// fields as Outer's own (F2 of the review).
type inner struct {
	Tags []string
	Text string
}

type innerP struct {
	X int
	Y []string
}

// Outer embeds structs that are not exported, by value and through a
// pointer.
type Outer struct {
	inner
	*innerP
	Name string
}

// EmbedsBounded bounds the fields that come from the embedded struct too.
//
// @Requires |o.Name| <= 100 And |o.inner.Text| <= 100 And |o.inner.Tags| <= 10 And (Forall i in [0, |o.inner.Tags|) : |o.inner.Tags[i]| <= 10)
// @Requires o.innerP != nil -> |o.innerP.Y| <= 10 And (Forall i in [0, |o.innerP.Y|) : |o.innerP.Y[i]| <= 10)
// @Ensures True
func EmbedsBounded(o Outer) (n int) {
	js, _ := json.Marshal(o)
	return len(js)
}

// Counts holds a map with integer keys and one with string keys.
type Counts struct {
	ByDay  map[int]int
	ByName map[string]bool
}

// Mapped encodes maps whose keys and number are bounded.
//
// @Requires |c.ByDay| <= 1000 And |c.ByName| <= 1000 And (Forall k in c.ByName : |k| <= 100)
// @Ensures True
func Mapped(c Counts) (n int) {
	js, _ := json.Marshal(c)
	return len(js)
}

// Server is a type with an exported method that ends up calling Marshal of
// a Task: encoding/json runs no method of what it is handed, so no cycle
// goes through it (F10 of the review).
type Server struct{ N int }

// Dump encodes a task.
//
// @Requires s != nil
// @Ensures True
func (s *Server) Dump() (js []byte, err error) {
	t := Leaf{Text: "x"}
	js, err = json.Marshal(t)
	return js, err
}

// Again is an exported method of the type Dump encodes, and calls Dump.
//
// @Ensures True
func (l Leaf) Again() (n int) {
	s := &Server{}
	_, _ = s.Dump()
	return 0
}

// HintFollowed has the Requires the message for Unbounded suggests.
//
// @Requires |l.Name| <= 1000000 And |l.Tags| <= 1000000 And (Forall i in [0, |l.Tags|) : |l.Tags[i]| <= 1000000)
// @Ensures True
func HintFollowed(l Loose) (n int) {
	js, _ := json.Marshal(l)
	return len(js)
}

// SliceHintFollowed has the Requires the message for UnboundedSlice
// suggests.
//
// @Requires |ls| <= 10000 And (Forall i in [0, |ls|) : |ls[i].Name| <= 10000 And |ls[i].Tags| <= 10000 And (Forall j in [0, |ls[i].Tags|) : |ls[i].Tags[j]| <= 10000))
// @Ensures True
func SliceHintFollowed(ls []Loose) (n int) {
	js, _ := json.Marshal(ls)
	return len(js)
}
