// Package multiarg holds a call whose arguments are the results of another
// call, g(f()), which the ownership summary of an exported function met
// with no parameter for its operand and crashed on (F21 of the review of
// F41). It is refused where it stands, and nothing else of the run is
// lost.
package multiarg

// @Ensures True
func pair() (a int, err error) { return 1, nil } // want `the contract of pair may also be met by a function that always returns an error`

// @Ensures True
func Must(a int, err error) (r int) { return a }

// @Ensures True
func New() (r int) { return Must(pair()) } // want `cannot verify New: a call with several results as the arguments of another call is not supported yet`
