// Package deepfactslib holds trusted functions whose results and arguments
// hold strings, slices of strings, and maps of them, as an *http.Response
// does. The questions about them hold a region of strings, which vego
// solves without the axiom of extensionality; see The prover in the
// ROADMAP. Most entries in the trust file of the tests promise something
// that contradicts what the types guarantee of what these hold.
package deepfactslib

// R has fields of the types of the fields of http.Response that hold
// strings.
type R struct {
	Status string
	Code   int
	Header map[string][]string
	TE     []string
}

// GetByte, GetMap, GetSlice, and GetQ return a response; their entries
// contradict the types of what it holds.
func GetByte(url string) (r *R, err error) { return &R{}, nil }

func GetMap(url string) (r *R, err error) { return &R{}, nil }

func GetSlice(url string) (r *R, err error) { return &R{}, nil }

func GetQ(url string) (r *R, err error) { return &R{}, nil }

// Put and PutMap take strings; their entries contradict the types of what
// they are handed.
func Put(s []string) {}

func PutMap(m map[string][]string) {}

// Must always succeeds.
func Must(url string) (r *R, err error) { return &R{}, nil }
