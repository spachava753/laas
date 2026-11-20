package guide

// Box holds a value of any type.
type Box struct{ Value any }

// @Requires b != nil
// @Ensures b.Value' = b // want `in Ensures annotation: an interface value can only be compared with nil or with another interface value`
func (b *Box) touch() (result *Box) {
	return b
}

// @Requires b != nil
// @Ensures True
func Touches(b *Box) {
	b.touch() // want `the contract of touch cannot be used: its Ensures annotation at unreadable.go:7:1 cannot be read \(an interface value can only be compared with nil or with another interface value\), so this call is verified without it`
}
