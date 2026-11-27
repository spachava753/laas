// Package getq calls N of what Get returns (gn of the review of the design
// of F43).
package getq

// I has N.
type I interface {
	// @Ensures True
	N() (n int)
}

// G has Get.
type G interface {
	// @Ensures True
	Get() (i I)
}

// F calls x.Get().N().
//
// @Ensures True
func F(x G) (n int) {
	if x == nil {
		return 0
	}
	i := x.Get()
	if i == nil {
		return 0
	}
	return i.N()
}
