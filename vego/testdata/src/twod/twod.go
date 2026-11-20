// Package twod gives the sink an entry and relies on it for a sink that
// the verified code of twoc hands back.
package twod // want `the trust files of this build give \(twoentrieslib.Sink\).Put a contract at .*twod/vego-trusted.yaml:4, and the proofs of package twoc were made with none; what they let through can reach verified code that relies on the entry: add the same entry to the trust file of its module` `the trust files of this build give \(twoownlib.Gauge\).Read a contract at .*twod/vego-trusted.yaml:8, and the proofs of package twoownlib were made with none; .*: the type is declared in its module, so write the contract in source where the type is declared`

import (
	"twoc"
	"twoownlib"
)

// @Requires c != nil And c.N = 0
// @Ensures n = 0
func Use(c *twoc.Counter) (n int) {
	s := twoc.Make(c)
	if s != nil {
		_ = s.Put(1)
	}
	return c.N
}

// @Requires g != nil
// @Ensures n >= 0 Or n < 0
func Reads(g twoownlib.Gauge) (n int) {
	twoownlib.Keeps(g) // want `this call may not end: Reads hands g to twoownlib\.Keeps\(g\) at twod\.go:\d+:\d+, which may run Reads`
	return g.Read()
}
