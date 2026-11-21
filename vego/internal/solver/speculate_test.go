package solver

import (
	"sync"
	"testing"
	"time"

	"github.com/spachava753/laas/vego/internal/logic"
)

// TestSpeculation checks that a speculative problem never delays another:
// with every process busy, a question that is not speculative ends the
// process of a speculative one, whose asker gets no answer, and an asker
// that was waiting for that problem's answer solves it itself.
func TestSpeculation(t *testing.T) {
	saved := maxProcesses
	maxProcesses = 2
	defer func() { maxProcesses = saved }()
	s, err := start(fake(t, pinned, `sleep 1; echo unsat; echo '(:reason-unknown "")'; echo '(:rlimit 7)'`))
	if err != nil {
		t.Fatal(err)
	}
	defer endIdle(s)
	goal := func(n int64) *logic.Term {
		x := logic.Const("x", logic.Int)
		return logic.Le(x, logic.Add(x, logic.IntLit(n)))
	}
	type outcome struct {
		result Result
		took   time.Duration
	}
	ask := func(wg *sync.WaitGroup, out *outcome, n int64, speculative bool) {
		wg.Go(func() {
			began := time.Now()
			out.result = s.Prove(nil, goal(n), Options{Speculative: speculative})
			out.took = time.Since(began)
		})
	}
	var wg sync.WaitGroup
	var spec, busy, waiter, urgent outcome
	ask(&wg, &spec, 1, true)
	time.Sleep(150 * time.Millisecond)
	ask(&wg, &busy, 2, false)
	time.Sleep(150 * time.Millisecond)
	// The same problem as the speculative one: this asker waits for it.
	ask(&wg, &waiter, 1, false)
	time.Sleep(150 * time.Millisecond)
	// Both processes are busy, one with the speculative problem.
	ask(&wg, &urgent, 3, false)
	wg.Wait()
	if spec.result != Unknown {
		t.Errorf("the speculative problem, whose process was taken, got %v", spec.result)
	}
	if urgent.result != Proved || urgent.took > 1800*time.Millisecond {
		t.Errorf("the question that found every process busy got %v after %v, want proved within one answer's time", urgent.result, urgent.took)
	}
	if waiter.result != Proved || busy.result != Proved {
		t.Errorf("the other questions got %v and %v, want proved", waiter.result, busy.result)
	}
	// A speculative problem never takes the last place: with one process
	// free, a second speculative problem waits for the first.
	var first, second outcome
	var spec2 sync.WaitGroup
	ask(&spec2, &first, 4, true)
	time.Sleep(150 * time.Millisecond)
	ask(&spec2, &second, 5, true)
	spec2.Wait()
	if first.result != Proved || second.result != Proved || second.took < 1500*time.Millisecond {
		t.Errorf("two speculative problems got %v and %v, the second after %v; want both proved, one after the other", first.result, second.result, second.took)
	}
}
