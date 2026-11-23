package main

import (
	"encoding/json"
	"reflect"
	"time"
)

// The types the test walks as vego does and the program encodes.

type Basics struct {
	B   bool
	I   int
	I8  int8
	I16 int16
	I32 int32
	I64 int64
	U   uint
	U8  uint8
	U16 uint16
	U32 uint32
	U64 uint64
	UP  uintptr
	F32 float32
	F64 float64
	S   string
}

type Quoted struct {
	S  string  `json:"s,string"`
	I  int64   `json:",string"`
	F  float64 `json:",string"`
	F3 float32 `json:",string"`
	B  bool    `json:"b,string"`
	U8 uint8   `json:",string"`
}

type NamedBytes []byte

type Bytes struct {
	B []byte
	N NamedBytes `json:"n"`
}

type Leaves struct {
	T  time.Time
	R  json.RawMessage
	N  json.Number
	TZ time.Time       `json:",omitzero"`
	RE json.RawMessage `json:",omitempty"`
}

type Inner struct {
	Text string
	Tags []string
}

// Flat is what a map's value may hold: no slice or map of elements of
// unknown length.
type Flat struct {
	Text string
	N    int32
	R    []bool
}

type Nest struct {
	Items  []Inner
	ByName map[string]Flat
	ByInt  map[int8]string
	ByU    map[uint64]bool
	Ptr    *Inner
	Deep   [][]map[string]int16
}

type inner struct {
	Tags []string
	Text string
}

type innerP struct {
	X int
	Y []string
}

type ExpEmb struct{ Z string }

type Embeds struct {
	inner
	*innerP
	*ExpEmb
	Name string
}

type Tags struct {
	A     int    `json:"<a&b>"`
	B     string `json:"-"`
	C     string `json:"-,"`
	D     string `json:",omitempty"`
	E     Inner  `json:",omitzero"`
	F     []int  `json:"f,omitempty"`
	g     int
	Loud  Loud
	LoudS LoudStruct
	LM    LoudMap
	LS    LoudSlice
	LK    map[LoudKey]int
	LoudEmbedded
}

type TopSlice []Inner

type TopMap map[string]Flat

type Empty struct{}

// Types in which one weight decides, so that it one smaller shows.
type TwoBools struct{ A, B bool }
type TwoTimes struct{ A, B time.Time }
type TwoF64 struct{ A, B float64 }
type TwoF32 struct{ A, B float32 }
type TwoStrings struct{ A, B string }
type TwoQuoted struct {
	A string `json:",string"`
	B string `json:",string"`
}
type TwoQInts struct {
	A int64 `json:",string"`
	B int64 `json:",string"`
}
type TopBools []bool
type BoolMap map[string]bool

var registry = map[string]reflect.Type{
	"Basics":     reflect.TypeFor[Basics](),
	"Quoted":     reflect.TypeFor[Quoted](),
	"Bytes":      reflect.TypeFor[Bytes](),
	"Leaves":     reflect.TypeFor[Leaves](),
	"Inner":      reflect.TypeFor[Inner](),
	"*Inner":     reflect.TypeFor[*Inner](),
	"Nest":       reflect.TypeFor[Nest](),
	"Embeds":     reflect.TypeFor[Embeds](),
	"Tags":       reflect.TypeFor[Tags](),
	"TopSlice":   reflect.TypeFor[TopSlice](),
	"TopMap":     reflect.TypeFor[TopMap](),
	"Empty":      reflect.TypeFor[Empty](),
	"TwoBools":   reflect.TypeFor[TwoBools](),
	"TwoTimes":   reflect.TypeFor[TwoTimes](),
	"TwoF64":     reflect.TypeFor[TwoF64](),
	"TwoF32":     reflect.TypeFor[TwoF32](),
	"TwoStrings": reflect.TypeFor[TwoStrings](),
	"TwoQuoted":  reflect.TypeFor[TwoQuoted](),
	"TwoQInts":   reflect.TypeFor[TwoQInts](),
	"TopBools":   reflect.TypeFor[TopBools](),
	"BoolMap":    reflect.TypeFor[BoolMap](),
	"Loud":       reflect.TypeFor[Loud](),
	"Raw":        reflect.TypeFor[json.RawMessage](),
	"Number":     reflect.TypeFor[json.Number](),
}
