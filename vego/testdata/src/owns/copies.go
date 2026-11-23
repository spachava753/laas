package owns

// Copied copies a stack, which would share what it owns.
//
// @Requires s != nil
// @Ensures True
func Copied(s *Stack) {
	c := *s // want `vego: cannot verify Copied: \*s copies a value of type Stack, which owns memory; use a pointer to it; a value that owns memory must not be copied or overwritten, since a copy would share what the original owns, which only the methods of each may write`
	_ = c
}
