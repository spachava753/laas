// Package slowresplib holds a trusted function returning a struct with the
// field types of http.Response that hold no pointer.
package slowresplib

// R has the fields of http.Response that are strings, slices of strings,
// maps of them, integers, and booleans.
type R struct {
	Status           string
	StatusCode       int
	Proto            string
	ProtoMajor       int
	ProtoMinor       int
	Header           map[string][]string
	ContentLength    int64
	TransferEncoding []string
	Close            bool
	Uncompressed     bool
	Trailer          map[string][]string
}

// Get is trusted.
func Get(url string) (r *R, err error) { return &R{}, nil }
