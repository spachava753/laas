package vego

import (
	"path/filepath"
	"testing"
)

// TestInstancesAnswerAsTheirGenericFunction checks that what is derived
// from the body or the key of a generic function is the same asked of an
// instantiation that calleeAt made as of the function itself, and that a
// map of functions read with an instantiation panics.
func TestInstancesAnswerAsTheirGenericFunction(t *testing.T) {
	saved := observeVerifier
	defer func() { observeVerifier = saved }()
	seen := 0
	observeVerifier = func(pv *pkgVerifier) {
		if pv.pass.Pkg.Path() != "generics" {
			return
		}
		for origin, made := range pv.instances {
			for _, inst := range made {
				seen++
				if pv.originOf(inst.fn) != origin {
					t.Errorf("originOf an instantiation of %s is %s", origin.FullName(), pv.originOf(inst.fn).FullName())
				}
				if pv.mayCallValues(inst.fn) != pv.mayCallValues(origin) {
					t.Errorf("mayCallValues of an instantiation of %s differs from that of the function", origin.FullName())
				}
				if pv.mayCallValuesAtCall(inst.fn) != pv.mayCallValuesAtCall(origin) {
					t.Errorf("mayCallValuesAtCall of an instantiation of %s differs from that of the function", origin.FullName())
				}
				graph := pv.callGraph()
				if byFunc(graph.byObj, pv.originOf(inst.fn)) != byFunc(graph.byObj, origin) {
					t.Errorf("the call graph gives an instantiation of %s another node", origin.FullName())
				}
				func() {
					defer func() {
						if recover() == nil {
							t.Errorf("reading the call graph with an instantiation of %s does not panic", origin.FullName())
						}
					}()
					byFunc(graph.byObj, inst.fn)
				}()
			}
		}
	}
	analyzer := newAnalyzer()
	if err := analyzer.Flags.Set("trusted", filepath.Join("testdata", "trusted.yaml")); err != nil {
		t.Fatal(err)
	}
	runCorpus(t, analyzer, "generics", "genericslib")
	if seen < 10 {
		t.Errorf("only %d instantiations were made; the corpus generics should make more", seen)
	}
}
