// Package unseenout converts what a package-level variable refers to to an
// interface whose methods nobody verified, which lets it out: code that is
// not verified may run those methods at any time after (F39, part A).
package unseenout

import "unseensdk"

var cached = &unseensdk.Text{Text: "a"}

var kept = &unseensdk.Text{Text: "a"}

// Cached relies on what cached refers to staying as initialised.
//
// @Ensures r = "a"
func Cached() (r string) {
	if cached == nil {
		return "a"
	}
	return cached.Text // want `postcondition may not hold: r = "a"; the contents of cached are not known to stay as initialised: the use at out.go:\d+ lets a reference to them out`
}

// Out hands what cached refers to out as a content.
//
// @Ensures True
func Out() (c unseensdk.Content) {
	return cached
}

// Kept relies on kept, which nothing lets out.
//
// @Ensures r = "a"
func Kept() (r string) {
	if kept == nil {
		return "a"
	}
	return kept.Text
}
