// Package funcvalues holds programs that use function values: values of
// function type that are held, passed, stored, and called.
package funcvalues

// Values of a function type can be held, passed, stored, and compared with
// nil. Nothing else is known of a function value than whether it is nil.

type Server struct {
	name   string
	handle func(n int) int
}

// Either returns whichever of two function values is not nil.
//
// @Requires f != nil Or g != nil
// @Ensures h != nil
func Either(f, g func(int) int) (h func(int) int) {
	if f != nil {
		return f
	}
	return g
}

// Install stores a handler in a server.
//
// @Requires s != nil
// @Modifies s.handle
// @Ensures s.handle' != nil <-> h != nil
func Install(s *Server, h func(n int) int) {
	s.handle = h
}

// Clear removes the handler of a server.
//
// @Requires s != nil
// @Modifies s.handle
// @Ensures s.handle' = nil
func Clear(s *Server) {
	s.handle = nil
}

// Rename changes the name and keeps the handler, which is a field of its own.
//
// @Requires s != nil
// @Modifies s.name
// @Ensures (s.handle != nil) = (s.handle' != nil)
func Rename(s *Server, name string) {
	s.name = name
}

// CountSet counts the function values that are not nil.
//
// @Ensures 0 <= n <= |fs|
func CountSet(fs []func()) (n int) {
	// @Invariant 0 <= n <= i
	for i := range fs {
		if fs[i] != nil {
			n++
		}
	}
	return n
}

// Lookup reads a handler from a map; an absent key gives nil.
//
// @Requires ~has(m, k)
// @Ensures h = nil
func Lookup(m map[string]func(), k string) (h func()) {
	return m[k]
}

// Pick keeps a function value in a struct value.
//
// @Ensures (s.handle != nil) = (h != nil) And s.name = "x"
func Pick(h func(n int) int) (s Server) {
	return Server{name: "x", handle: h}
}

// ZeroServer has no handler.
//
// @Ensures s.handle = nil
func ZeroServer() (s Server) {
	var z Server
	return z
}
