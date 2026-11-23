package owns

func externalStack() *Stack { return &Stack{} }

func externalReset(s *Stack) { s.items = nil }

// FromTrusted takes a stack from a function the project trusts.
//
// @Ensures True
func FromTrusted() {
	s := externalStack() // want `vego: cannot verify FromTrusted: externalStack returns a \*Stack, which holds a Stack, which owns memory, and only a contract that comes with vego or a verified function says what such a value owns; verify externalStack`
	s.Push(1)
}

// ResetByTrusted hands a stack to a function the project trusts to write it.
//
// @Requires s != nil
// @Modifies s
// @Ensures True
func ResetByTrusted(s *Stack) {
	externalReset(s) // want `vego: cannot verify ResetByTrusted: externalReset may modify s, a \*Stack, which owns memory, and only a contract that comes with vego or a verified function says how what such a value owns may change`
}
