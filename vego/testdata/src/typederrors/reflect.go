package typederrors

import (
	"encoding/json"
	"errors"
)

// Built without GOEXPERIMENT=jsonv2, json.Marshal returns for a NaN a
// *json.UnsupportedValueError whose Value, a reflect.Value, refers to the
// float in the memory of what it was handed, which reflection could set
// (F11 of the review). Taking such a value out of an error is refused, in
// each form.

// @Ensures True
func ReadsStr(f float64) (n int) {
	_, err := json.Marshal(f)
	if uv, ok := err.(*json.UnsupportedValueError); ok && uv != nil { // want `cannot verify ReadsStr: asserting an error to \*encoding/json.UnsupportedValueError is not supported: it holds in field Value a reflect.Value, through which reflection could set the memory it refers to`
		return len(uv.Str)
	}
	return 0
}

// @Ensures True
func SwitchesUnsupported(f float64) (ok bool) {
	_, err := json.Marshal(f)
	switch err.(type) {
	case *json.UnsupportedValueError: // want `cannot verify SwitchesUnsupported: a case of \*encoding/json.UnsupportedValueError in a type switch is not supported: it holds in field Value a reflect.Value`
		return true
	}
	return false
}

// @Ensures True
func FindsUnsupported(f float64) (ok bool) {
	_, err := json.Marshal(f)
	var uv *json.UnsupportedValueError
	return errors.As(err, &uv) // want `cannot verify FindsUnsupported: errors.As with a target of \*encoding/json.UnsupportedValueError is not supported: it holds in field Value a reflect.Value`
}
