package handlers

import (
	"errors"
	"fmt"
	"net/http"
	"strconv"
)

// lookup fails with an error of known origin.
//
// @Ensures id >= 0 -> err = nil
func lookup(id int) (n int, err error) {
	if id < 0 {
		return 0, fmt.Errorf("task with id=%d not found", id)
	}
	return id, nil
}

// NotFoundErr answers with the text of an error that a verified function
// made, the commonest call of http.Error there is.
//
// @Requires w != nil And req != nil
// @Modifies w
// @Ensures True
func NotFoundErr(w http.ResponseWriter, req *http.Request) {
	id, err := strconv.Atoi(req.PathValue("id"))
	if err != nil {
		http.Error(w, err.Error(), http.StatusBadRequest)
		return
	}
	if _, err := lookup(id); err != nil {
		http.Error(w, err.Error(), http.StatusNotFound)
	}
}

// Prefixed puts the text after a prefix, which the bound of the text still
// leaves room for.
//
// @Requires w != nil
// @Modifies w
// @Ensures True
func Prefixed(w http.ResponseWriter) {
	err := errors.New("gone")
	http.Error(w, "lookup: "+err.Error(), http.StatusNotFound)
}

// Twice puts the text in twice, for which there is no room.
//
// @Requires w != nil And err != nil
// @Modifies w
// @Ensures True
func Twice(w http.ResponseWriter, err error) {
	if err = check(true); err != nil {
		s := err.Error()
		http.Error(w, s+s, http.StatusNotFound) // want `precondition of Error may not hold: 2 \* \(\|error\| \+ 1\) \+ 65536 <= MaxAlloc`
	}
}

// check is verified and returns an error of known origin.
//
// @Ensures ~fail -> err = nil
func check(fail bool) (err error) {
	if fail {
		return errors.New("bad")
	}
	return nil
}

// Unknown asks an error of no known origin for its text.
//
// @Requires w != nil And err != nil
// @Modifies w
// @Ensures True
func Unknown(w http.ResponseWriter, err error) {
	http.Error(w, err.Error(), http.StatusNotFound) // want `cannot verify Unknown: calling Error on err would run the methods of an error whose origin is not known`
}

// NilText asks an error that may be nil.
//
// @Ensures True
func NilText(fail bool) (s string) {
	var err error
	if fail {
		err = errors.New("x")
	}
	return err.Error() // want `the error err may be nil`
}

// Long makes an error of a text whose length nothing bounds.
//
// @Ensures err != nil
func Long(s string) (err error) {
	return errors.New(s) // want `precondition of errors.New may not hold: 2 \* \(\|text\| \+ 4096\) \+ 65536 <= MaxAlloc, so that the text of the error can be printed; it holds when \|s\| <= `
}

// Short makes one of a bounded text.
//
// @Requires |s| <= 1000
// @Ensures ~fail -> err = nil
func Short(s string, fail bool) (err error) {
	if fail {
		return errors.New(s)
	}
	return nil
}
