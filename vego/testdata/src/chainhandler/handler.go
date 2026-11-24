// Package chainhandler changes the state of chainstats.
package chainhandler

import "chainstats"

// Serve counts a request.
//
// @Modifies chainstats
// @Ensures True
func Serve() {
	chainstats.Hit()
}

// ServeUnlisted does not list what Hit changes.
//
// @Ensures True
func ServeUnlisted() {
	chainstats.Hit() // want `^vego: Hit may modify the state of package chainstats \(chainstats.requests\), which ServeUnlisted may not modify; list chainstats in a // @Modifies clause$`
}

// NamesHidden names a variable of another package that is not exported.
//
// @Modifies chainstats.requests // want `^vego: in Modifies annotation: chainstats.requests is not exported; list the state of package chainstats, as // @Modifies chainstats$`
// @Ensures True
func NamesHidden() {
	chainstats.Hit()
}

// SetExported names an exported variable of another package.
//
// @Modifies chainstats.Exported
// @Ensures chainstats.Exported' = 3
func SetExported() {
	chainstats.Exported = 3
}
