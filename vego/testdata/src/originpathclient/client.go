// Package originpathclient formats the errors of functions of originpath,
// which publishes whether each returns only errors of known origin.
package originpathclient

import (
	"fmt"

	"originpath"
)

// WrapsLoad formats the error of Load, every return of which returns an
// error of known origin.
//
// @Ensures True
func WrapsLoad() (err error) {
	if err := originpath.Load(); err != nil {
		return fmt.Errorf("client: %w", err)
	}
	return nil
}

// WrapsNormalised formats the error of Normalised.
//
// @Ensures True
func WrapsNormalised() (err error) {
	if err := originpath.Normalised(); err != nil {
		return fmt.Errorf("client: %w", err)
	}
	return nil
}

// WrapsOpens formats the error of Opens, whose last return returns an error
// nothing vouches for.
//
// @Ensures True
func WrapsOpens() (err error) {
	if err := originpath.Opens(); err != nil {
		return fmt.Errorf("client: %w", err) // want `formatting err would run the methods of an error whose origin is not known`
	}
	return nil
}

// WrapsSwitched formats the error of TypeSwitched, which returns the
// variable of a type switch.
//
// @Ensures True
func WrapsSwitched(e error) (err error) {
	if err := originpath.TypeSwitched(e); err != nil { // want `the contract of originpath.TypeSwitched cannot be used: its verification failed in package originpath`
		return fmt.Errorf("client: %w", err) // want `formatting err would run the methods of an error whose origin is not known`
	}
	return nil
}
