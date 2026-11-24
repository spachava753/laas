// Package chainapp changes the state of chainstats through chainhandler,
// and does not import chainstats.
package chainapp

import "chainhandler"

// Run serves; the state of chainhandler covers that of chainstats.
//
// @Modifies chainhandler
// @Ensures True
func Run() {
	chainhandler.Serve()
}

// RunUnlisted does not list it.
//
// @Ensures True
func RunUnlisted() {
	chainhandler.Serve() // want `^vego: Serve may modify the state of package chainstats \(chainstats.requests\), which RunUnlisted may not modify; list chainhandler, whose state includes it, in a // @Modifies clause$`
}

// RunPath lists the path of the package whose state it changes.
//
// @Modifies "chainstats"
// @Ensures True
func RunPath() {
	chainhandler.Serve()
}

// RunOther changes nothing.
//
// @Ensures True
func RunOther() {}

// NotDependency names a package that chainapp does not depend on.
//
// @Modifies "chainreport" // want `^vego: in Modifies annotation: "chainreport" is not among the packages that package chainapp depends on, so what its state covers is not known here$`
// @Ensures True
func NotDependency() {}

// OwnState names the state of its own package.
//
// @Modifies "chainapp" // want `^vego: in Modifies annotation: "chainapp" is the package of OwnState, whose variables a Modifies clause names one by one$`
// @Ensures True
func OwnState() {}
