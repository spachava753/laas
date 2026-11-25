package dynheld

import "net/http"

// A writer held in a field of type any is still the writer (F6 of the
// design review): a struct that holds an interface value refers to what
// it holds, so a callee that stores what it holds keeps it.

// Holder holds a value of any type.
type Holder struct{ W any }

// Slot is memory a caller hands over.
type Slot struct{ W any }

// @Requires dst != nil
// @Modifies dst
// @Ensures True
func keep(h Holder, dst *Slot) {
	dst.W = h.W
}

// @Requires w != nil And r != nil And dst != nil
// @Modifies dst
// @Ensures True
func HandsHolder(w http.ResponseWriter, r *http.Request, dst *Slot) {
	keep(Holder{W: w}, dst) // want `Holder\{…\}, which holds w, is or holds a net/http.ResponseWriter, which must not be used after the call that received it returns, and here it is handed to keep as h`
}

// A callee that keeps nothing of what it is handed can be given it.
//
// @Ensures r = (h.W = nil)
func isEmpty(h Holder) (r bool) {
	return h.W == nil
}

// @Requires w != nil And r != nil
// @Ensures True
func AsksHolder(w http.ResponseWriter, r *http.Request) {
	_ = isEmpty(Holder{W: w})
}
