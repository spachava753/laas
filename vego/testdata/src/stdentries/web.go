package stdentries

import "net/http"

// ItemID returns the wildcard id of the pattern that matched a request.
//
// @Requires r != nil
// @Ensures True
func ItemID(r *http.Request) (id string) {
	return r.PathValue("id")
}

// ItemIDOfAny may be given a nil request.
//
// @Ensures True
func ItemIDOfAny(r *http.Request) (id string) {
	return r.PathValue("id") // want `precondition of PathValue may not hold: r != nil`
}

// ContentType reads a header of a request.
//
// @Requires r != nil
// @Ensures True
func ContentType(r *http.Request) (ct string) {
	return r.Header.Get("Content-Type")
}

// MarkJSON sets a header in hand.
//
// @Requires h != nil
// @Modifies h
// @Ensures True
func MarkJSON(h http.Header) {
	h.Set("Content-Type", "application/json")
}

// MarkQuietly sets a header without saying so.
//
// @Requires h != nil
// @Ensures True
func MarkQuietly(h http.Header) {
	h.Set("Content-Type", "application/json") // want `Set may modify h, which MarkQuietly may not modify`
}

// MarkAny may be given a nil header.
//
// @Modifies h
// @Ensures True
func MarkAny(h http.Header) {
	h.Set("Content-Type", "application/json") // want `precondition of Set may not hold: h != nil`
}

// Router makes a new router.
//
// @Ensures mux != nil
func Router() (mux *http.ServeMux) {
	return http.NewServeMux()
}
