//go:build debug

package addrignored

// N returns a pointer to s.n in debug builds.
func N(s *S) *int { return &s.n }
