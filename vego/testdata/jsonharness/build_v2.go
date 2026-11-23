//go:build goexperiment.jsonv2

package main

import (
	"encoding/json/jsontext"
	"runtime"
)

func build() string { return runtime.Version() + " v2" }

type HasMarshalJSONTo struct{ X int }
type HasUnmarshalJSONFrom struct{ X int }

func (HasMarshalJSONTo) MarshalJSONTo(e *jsontext.Encoder) error {
	record("MarshalJSONTo")
	return e.WriteToken(jsontext.Null)
}

func (*HasUnmarshalJSONFrom) UnmarshalJSONFrom(d *jsontext.Decoder) error {
	record("UnmarshalJSONFrom")
	return d.SkipValue()
}

func init() {
	methodValues = append(methodValues, HasMarshalJSONTo{}, HasUnmarshalJSONFrom{})
}
