// Package wrapp: code that is not verified wraps values of the package in
// a wrapr.T and hands them back. X hands one to wrapq.F, which calls its
// M (k3a); Y calls its M itself (k3b). Before F43, Y and QT.N verified,
// and a program that called SetupY and then Y ran out of stack: the graph
// sent i.M() only to methods named M of this package.
package wrapp

import (
	"cycles/held/wrapq"
	"cycles/held/wrapr"
)

// PT calls back into X.
type PT struct{}

// @Ensures True
func (PT) N() {
	if Made != nil {
		X(Made) // want `this call may not end: PT.N calls X at p.go:\d+:\d+, X calls wrapq.F\(i\) at p.go:\d+:\d+, which may run PT.N`
	}
}

// Made is set by code that is not verified.
var Made wrapr.I

// Setup is not verified.
func Setup() { Made = wrapr.Wrap(PT{}) }

// SetupY is not verified.
func SetupY() { Made = wrapr.Wrap(QT{}) }

// @Requires i != nil
// @Ensures True
func X(i wrapr.I) {
	wrapq.F(i) // want `the contract of cycles/held/wrapq.F cannot be used: its verification failed`
}

// @Requires i != nil
// @Ensures True
func Y(i wrapr.I) {
	i.M() // want `this call may not end: Y calls i.M\(\) at p.go:\d+:\d+, which may run Y; a method M of a type of a package this one imports may be what i.M\(\) runs` `cannot verify Y: code that the call may run writes Made`
}

// QT calls back into Y.
type QT struct{}

// @Ensures True
func (QT) N() {
	if Made != nil {
		Y(Made) // want `this call may not end: QT.N calls Y at p.go:\d+:\d+, Y calls i.M\(\) at p.go:\d+:\d+, which may run QT.N`
	}
}
