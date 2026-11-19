package vego

import (
	"fmt"

	"github.com/spachava753/laas/vego/internal/logic"
)

// Terms share structure, so a term can be far larger as a tree than in
// memory, and printing or walking it costs its size as a tree. A rule of
// the verifier that puts an operand into what it builds more than once
// makes a chain of such operations double at every step. logic.MaxSize
// stops that in every run; the checks here, which the tests turn on, find
// such a rule as soon as a test program uses it twice in a row.

// joinSizeLimit, when it is not zero, is the size beyond which a term that
// goes into a join is a fault of the verifier: what a join makes must not
// grow with the joins before it. The tests set it, so that such growth is
// caught at once and not by the machine running out of memory.
var joinSizeLimit int

// checkJoinSize panics when a term that goes into a join has grown beyond
// joinSizeLimit, counted as a tree with shared parts counted again.
func checkJoinSize(terms []*logic.Term) {
	if joinSizeLimit == 0 {
		return
	}
	for _, t := range terms {
		budget := joinSizeLimit
		var count func(t *logic.Term)
		count = func(t *logic.Term) {
			budget--
			for _, arg := range t.Args {
				if budget < 0 {
					return
				}
				count(arg)
			}
		}
		if count(t); budget < 0 {
			panic(fmt.Sprintf("vego: internal error: a term that goes into a join has more than %d nodes", joinSizeLimit))
		}
	}
}

// growthRatio, when it is not zero, is how many times larger than its
// number of distinct nodes a value that is bound or stored may be as a
// tree. A larger value was built by a rule that doubles what it builds.
// The tests set it.
var growthRatio int64

// checkGrowth panics when a leaf of a value is larger as a tree than
// growthRatio times its number of distinct nodes. A small leaf is not
// looked at.
func checkGrowth(val value) {
	if growthRatio == 0 {
		return
	}
	for _, leaf := range val {
		if leaf == nil || leaf.Size() <= 256 {
			continue
		}
		seen := map[*logic.Term]bool{}
		var visit func(t *logic.Term)
		visit = func(t *logic.Term) {
			if seen[t] {
				return
			}
			seen[t] = true
			for _, arg := range t.Args {
				visit(arg)
			}
		}
		visit(leaf)
		if leaf.Size() > growthRatio*int64(len(seen)) {
			panic(fmt.Sprintf("vego: internal error: a value of %d distinct nodes has %d as a tree; some rule doubles what it builds: %.200s",
				len(seen), leaf.Size(), leaf.String()))
		}
	}
}
