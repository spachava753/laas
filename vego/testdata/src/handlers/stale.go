package handlers

import "net/http"

// A writer must not be used after the ServeHTTP call that received it
// returns, so verified code keeps none: each way of keeping one is refused,
// and each way of passing one on that keeps nothing verifies.

// Server remembers what it should not.
type Server struct {
	last http.ResponseWriter
	h    holder
	hs   []holder
	ws   []http.ResponseWriter
	m    map[string]http.ResponseWriter
	f    Callback
	a    any
}

type holder struct {
	w http.ResponseWriter
	n int
}

// Callback is code a server keeps.
//
// @Ensures True
type Callback func()

// KeepLast writes the writer of the last request, which is gone.
//
// @Requires s != nil And w != nil
// @Modifies s, s.last
// @Ensures True
func (s *Server) KeepLast(w http.ResponseWriter, req *http.Request) {
	if s.last != nil {
		s.last.WriteHeader(500)
	}
	s.last = w // want `w is or holds a net/http.ResponseWriter, which must not be used after the call that received it returns, and here it is stored into memory at stale.go:39:2, where a later call could use it; pass it on only to calls that keep nothing of it`
}

// KeepHolder stores a struct that holds the writer.
//
// @Requires s != nil
// @Modifies s
// @Ensures True
func (s *Server) KeepHolder(w http.ResponseWriter) {
	var h holder
	h.w = w
	s.h = h // want `h, which holds w, is or holds a net/http.ResponseWriter, which must not be used after the call that received it returns, and here it is stored into memory at stale.go:50:2`
}

// KeepSlice stores a new slice that holds a struct that holds it.
//
// @Requires s != nil
// @Modifies s
// @Ensures True
func (s *Server) KeepSlice(w http.ResponseWriter) {
	s.hs = []holder{{w: w}} // want `w is or holds a net/http.ResponseWriter, which must not be used after the call that received it returns, and here it is stored into what the literal at stale.go:59:9 makes` `\[\]holder\{…\} is or holds a net/http.ResponseWriter`
}

// KeepInMap stores it into a map.
//
// @Requires s != nil And s.m != nil
// @Modifies s.m
// @Ensures True
func (s *Server) KeepInMap(w http.ResponseWriter) {
	s.m["last"] = w // want `w is or holds a net/http.ResponseWriter, which must not be used after the call that received it returns, and here it is stored into memory at stale.go:68:2`
}

// Wrap returns a new struct that holds it.
//
// @Ensures r != nil
func Wrap(w http.ResponseWriter) (r *holder) {
	return &holder{w: w} // want `w is or holds a net/http.ResponseWriter, which must not be used after the call that received it returns, and here it is stored into what the literal at stale.go:75:10 makes` `&holder\{…\} is or holds a net/http.ResponseWriter, which must not be used after the call that received it returns, and here it is returned by Wrap`
}

// KeepCallback stores a literal that captures it.
//
// @Requires s != nil
// @Modifies s
// @Ensures True
func (s *Server) KeepCallback(w http.ResponseWriter) {
	s.f = Callback(func() { // want `w is or holds a net/http.ResponseWriter, which must not be used after the call that received it returns, and here it is captured by the function literal at stale.go:84:17, which may run after the call`
		_ = w
	})
}

// KeepAny stores it converted to any.
//
// @Requires s != nil
// @Modifies s
// @Ensures True
func (s *Server) KeepAny(w http.ResponseWriter) {
	var a any = w
	s.a = a // want `a, which holds w, is or holds a net/http.ResponseWriter, which must not be used after the call that received it returns, and here it is stored into memory at stale.go:96:2`
}

// Move moves writers that code that is not verified put into s.
//
// @Requires s != nil And t != nil And s.m != nil And t.m != nil And |t.ws| + |s.ws| <= 1000
// @Modifies t, t.m, t.ws
// @Ensures True
func Move(s, t *Server) {
	t.ws = append(t.ws, s.ws...) // want `s.ws is or holds a net/http.ResponseWriter` `append\(t.ws, s.ws...\), which holds t.ws, is or holds`
	t.h = s.h                    // want `s.h is or holds a net/http.ResponseWriter`
	t.ws = s.ws                  // want `s.ws is or holds a net/http.ResponseWriter`
	t.m["k"] = s.m["k"]          // want `s.m\["k"\] is or holds a net/http.ResponseWriter`
}

// Held returns a holder that s holds.
//
// @Requires s != nil
// @Ensures True
func Held(s *Server) (h holder) {
	return s.h // want `s.h is or holds a net/http.ResponseWriter, which must not be used after the call that received it returns, and here it is returned by Held`
}

// keeper stores what it is given.
//
// @Requires s != nil
// @Modifies s
// @Ensures True
func (s *Server) keeper(w http.ResponseWriter) {
	s.last = w // want `w is or holds a net/http.ResponseWriter`
}

// HandsToKeeper hands the writer to a function that keeps it.
//
// @Requires s != nil
// @Modifies s
// @Ensures True
func HandsToKeeper(s *Server, w http.ResponseWriter) {
	s.keeper(w) // want `w is or holds a net/http.ResponseWriter, which must not be used after the call that received it returns, and here it is handed to s.keeper as w \(it may keep what it is handed\)`
}

// Handler is a function type a writer may be handed to.
//
// @Requires w != nil
// @Modifies w
// @Ensures True
type Handler func(w http.ResponseWriter)

// HandsToValue hands it to a function value, which may keep it.
//
// @Requires h != nil And w != nil
// @Modifies w
// @Ensures True
func HandsToValue(h Handler, w http.ResponseWriter) {
	h(w) // want `w is or holds a net/http.ResponseWriter, which must not be used after the call that received it returns, and here it is handed to h as an argument \(a function value may keep what it is handed\)` `this call may not end: HandsToValue hands w to h\(w\)`
}

// answer writes a status and keeps nothing.
//
// @Requires w != nil
// @Modifies w
// @Ensures True
func answer(w http.ResponseWriter) {
	w.WriteHeader(http.StatusOK)
}

// HandsOn hands the writer to a helper that keeps nothing, defers a write,
// and writes in a literal called in place: none keeps it.
//
// @Requires w != nil
// @Modifies w
// @Ensures True
func HandsOn(w http.ResponseWriter) {
	defer http.Error(w, "done", http.StatusOK)
	answer(w)
	func() {
		w.Write(nil)
	}()
	var h holder
	h.w = w
	h.w.WriteHeader(http.StatusAccepted)
}

// FlushWriter is a writer that also flushes, which has the methods of
// http.ResponseWriter from its declarations.
type FlushWriter interface {
	http.ResponseWriter
	// @Receiver f
	// @Modifies f
	// @Ensures True
	Flush()
}

// Keeper keeps a FlushWriter.
type Keeper struct{ fw FlushWriter }

// KeepFlush stores it, which is keeping a ResponseWriter.
//
// @Requires k != nil
// @Modifies k
// @Ensures True
func (k *Keeper) KeepFlush(fw FlushWriter) {
	k.fw = fw // want `fw is or holds a net/http.ResponseWriter, which must not be used after the call that received it returns, and here it is stored into memory at stale.go:\d+:2`
}

// UseFlush uses one it is given, which keeps nothing.
//
// @Requires fw != nil
// @Modifies fw
// @Ensures True
func UseFlush(fw FlushWriter) {
	fw.WriteHeader(http.StatusOK)
	fw.Flush()
}

// wrapW is trusted to return a writer that keeps w.
func wrapW(w http.ResponseWriter) (r http.ResponseWriter) { return w }

// HandsToTrusted hands the writer to a trusted function that keeps it.
//
// @Requires w != nil
// @Ensures True
func HandsToTrusted(w http.ResponseWriter) {
	_ = wrapW(w) // want `w is or holds a net/http.ResponseWriter, which must not be used after the call that received it returns, and here it is handed to wrapW as w \(its entry keeps w in r\)`
}
