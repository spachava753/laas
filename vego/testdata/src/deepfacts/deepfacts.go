// Package deepfacts calls the functions of deepfactslib, whose entries
// promise what the types of strings, slices of strings, and maps of them
// rule out. Each must still be reported, also now that the questions about
// them are solved without the axiom of extensionality.
package deepfacts

import "deepfactslib"

// A reads the byte the entry promises.
//
// @Ensures code = 7
func A(url string) (code int) {
	r, _ := deepfactslib.GetByte(url) // want `the trusted contract of deepfactslib.GetByte \(trusted.yaml:\d+\) cannot be used: it contradicts itself` `cannot verify A: GetByte has a contract that could not be understood`
	_ = r.Status[0]
	return 5
}

// B reads the map value.
//
// @Ensures code = 7
func B(url string) (code int) {
	r, _ := deepfactslib.GetMap(url) // want `the trusted contract of deepfactslib.GetMap \(trusted.yaml:\d+\) cannot be used: it contradicts itself` `cannot verify B: GetMap has a contract that could not be understood`
	_ = len(r.Header["a"])
	return 5
}

// C reads the nested string.
//
// @Ensures code = 7
func C(url string) (code int) {
	r, _ := deepfactslib.GetSlice(url) // want `the trusted contract of deepfactslib.GetSlice \(trusted.yaml:\d+\) cannot be used: it contradicts itself` `cannot verify C: GetSlice has a contract that could not be understood`
	_ = r.TE[0][0]
	return 5
}

// Q reads under a quantified promise.
//
// @Ensures code = 7
func Q(url string) (code int) {
	r, _ := deepfactslib.GetQ(url) // want `the trusted contract of deepfactslib.GetQ \(trusted.yaml:\d+\) cannot be used: it contradicts itself` `cannot verify Q: GetQ has a contract that could not be understood`
	_ = r.Status[0]
	return 5
}

// P hands over a slice and reads it back.
//
// @Requires |s| > 0 And |s[0]| > 0
// @Ensures code = 7
func P(s []string) (code int) {
	deepfactslib.Put(s) // want `the trusted contract of Put cannot be true of this call: what it promises contradicts what is known here`
	_ = s[0][0]
	return 5
}

// M hands over a map and reads it back.
//
// @Ensures code = 7
func M(m map[string][]string) (code int) {
	deepfactslib.PutMap(m) // want `the trusted contract of deepfactslib.PutMap \(trusted.yaml:\d+\) cannot be used: it contradicts itself` `cannot verify M: PutMap has a contract that could not be understood`
	_ = len(m["a"])
	return 5
}

// Weak calls a function that always succeeds, so nothing excuses its
// contract, which says nothing about when it succeeds.
//
// @Ensures True
func Weak(url string) (n int, err error) { // want `the contract of Weak may also be met by a function that always returns an error: it requires success for no input`
	r, err := deepfactslib.Must(url)
	if err != nil {
		return 0, err
	}
	return len(r.Status), nil
}
