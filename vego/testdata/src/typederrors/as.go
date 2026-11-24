package typederrors

import "errors"

// No trusted contract for errors.As or errors.AsType can be true, and the
// message says so instead of advising one.

// @Ensures True
func As(err error) (line int) {
	var pe *PE
	if errors.As(err, &pe) { // want `it calls errors.As, which is not supported yet: it stores what it finds through the pointer it is handed`
		return pe.Line
	}
	return 0
}

// @Ensures True
func AsType(err error) (line int) {
	if pe, ok := errors.AsType[*PE](err); ok { // want `it calls errors.AsType, which is not supported yet: it runs the As and Unwrap methods`
		return pe.Line
	}
	return 0
}
