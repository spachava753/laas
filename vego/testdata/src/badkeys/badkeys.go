// Package badkeys has a trust file whose entry stands at the top level
// instead of under trusted.
package badkeys

func lookup(s string) int { return len(s) }

// @Ensures True
func Looks(s string) (n int) {
	return lookup(s) // want `cannot verify Looks: it calls lookup, which has no contract; annotate lookup with // @ annotations so that it is verified, or, since the trust file vego-trusted.yaml has problems, the first at line 1 \(unknown key "badkeys.lookup"; expected version, trusted, state, isolated, sizes, or inputs\), fix the file first: an entry for badkeys.lookup there may not have been read`
}
