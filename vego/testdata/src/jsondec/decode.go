package jsondec

import (
	"encoding/json"
	"errors"
	"fmt"
	"time"
)

// json.Unmarshal into values of the project's own types (F29, step 3):
// verified as a contract made for the call, which writes the exported
// fields encoding/json writes, with nothing known of them but their types,
// and requires what it would reuse to be nil.

// Item is what the memory server stores.
type Item struct {
	Type string   `json:"type"`
	Name string   `json:"name,omitempty"`
	Obs  []string `json:"observations,omitempty"`
	n    int
}

// Load decodes into a slice, declared nil, and wraps the error.
//
// @Requires |data| <= 1000000
// @Ensures True
func Load(data []byte) (n int, err error) {
	var items []Item
	if err := json.Unmarshal(data, &items); err != nil {
		return 0, fmt.Errorf("failed to unmarshal: %w", err)
	}
	return len(items), nil
}

// Req is the body of a request.
type Req struct {
	Text string    `json:"text"`
	Tags []string  `json:"tags"`
	Due  time.Time `json:"due"`
}

// LoadOne decodes into a struct, declared zero.
//
// @Requires |data| <= 1000000
// @Ensures True
func LoadOne(data []byte) (r Req, err error) {
	var rt Req
	err = json.Unmarshal(data, &rt)
	return rt, err
}

// Into decodes through a pointer it is handed, whose slice has no
// capacity.
//
// @Requires p != nil And |data| <= 1000000 And cap(p.Tags) = 0
// @Modifies p
// @Ensures True
func Into(data []byte, p *Req) (err error) {
	return json.Unmarshal(data, p)
}

// KeepsUnexported relies on an unexported field keeping its value.
//
// @Requires |data| <= 1000
// @Ensures k = 7
func KeepsUnexported(data []byte) (k int) {
	var it Item
	it.n = 7
	_ = json.Unmarshal(data, &it)
	return it.n
}

// Headers decodes a map of slices with string keys, which decoding
// counts no length of.
//
// @Requires |data| <= 1000000
// @Ensures True
func Headers(data []byte) (n int, err error) {
	var h map[string][]string
	err = json.Unmarshal(data, &h)
	return len(h), err
}

// Message is decoded and then checked.
//
// @Invariant |Text| <= 100
type Message struct {
	Text string
}

// Checked decodes a Message and returns it once its invariant is
// checked: nothing is known of what was decoded but its type.
//
// @Requires |data| <= 1000000
// @Ensures err = nil -> |m.Text| <= 100
func Checked(data []byte) (m Message, err error) {
	var got Message
	if err = json.Unmarshal(data, &got); err != nil {
		return Message{}, err
	}
	if len(got.Text) > 100 {
		return Message{}, errors.New("text too long")
	}
	return got, nil
}

// Envelope holds what is decoded later and when it was made.
type Envelope struct {
	Raw  json.RawMessage
	At   time.Time
	Next *Req
}

// Enveloped decodes a RawMessage, a time, and a pointer, all nil or zero.
//
// @Requires |data| <= 1000000
// @Ensures True
func Enveloped(data []byte) (e Envelope, err error) {
	var env Envelope
	err = json.Unmarshal(data, &env)
	return env, err
}
