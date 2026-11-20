// Package badyaml has a trust file that is not valid YAML. No entry of it
// is read, so every call that goes through the trust file says so: one
// that found a shipped entry, which an entry of the file would replace,
// and one that found nothing, whose entry may be among what was not read.
package badyaml

import "strings"

func lookup(s string) int { return len(s) }

// @Requires |s| <= 100
// @Ensures True
func Upper(s string) (r string) {
	return strings.ToUpper(s) // want `the trust file vego-trusted.yaml has problems, the first at line 1 \(not valid YAML: .*\), so the contract used here for strings.ToUpper may not be the one the file means to give it: fix the file first`
}

// @Ensures True
func Looks(s string) (n int) {
	return lookup(s) // want `cannot verify Looks: it calls lookup, which has no contract; annotate lookup with // @ annotations so that it is verified, or, since the trust file vego-trusted.yaml has problems, the first at line 1 \(not valid YAML: .*\), fix the file first: an entry for badyaml.lookup there may not have been read`
}
