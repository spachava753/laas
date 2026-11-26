package labels

import "testing"

// TestClaims checks what the contracts of labels say against Go.
func TestClaims(t *testing.T) {
	a := [][]int{{1, 2}, {3, 4, 5}, {6}}
	if i, j, found := Find(a, 5); !found || a[i][j] != 5 {
		t.Errorf("Find(5) = %d, %d, %v", i, j, found)
	}
	if _, _, found := Find(a, 7); found {
		t.Errorf("Find(7) found what is not there")
	}
	if n := RowsWithNegative([][]int{{1, -1, -2}, {2}, {-3}}); n != 2 {
		t.Errorf("RowsWithNegative = %d, not 2", n)
	}
	if Counted(5) != 5 || FirstZero([]int{3, 0, 0}) != 1 || FirstZero([]int{1}) != -1 {
		t.Errorf("Counted or FirstZero returned what its contract does not say")
	}
	if Sign([]int{0, 2}, true) != 1 || Sign([]int{2}, false) != 0 {
		t.Errorf("Sign returned what its contract does not say")
	}
	if Keys(map[string][]int{"a": {-1, -1}, "b": {1}}) != 1 {
		t.Errorf("Keys did not count one key")
	}
	if Fall(0) != 2 || Fall(1) != 1 || Fall(7) != 10 {
		t.Errorf("Fall returned what its contract does not say")
	}
	if FallIntoDefault(true, true) != 2 || FallIntoDefault(false, true) != 3 || FallIntoDefault(false, false) != 2 {
		t.Errorf("FallIntoDefault returned what its contract does not say")
	}
	if FallThenBreak(0) != 1 {
		t.Errorf("FallThenBreak(0) is proved to return 1")
	}
	if InnerMap(map[string]map[string]int{"a": {"x": -1}, "b": {"y": 1}}) != 1 {
		t.Errorf("InnerMap did not count one key")
	}
	m := map[string]int{"a": 1}
	BreakThenWrite(m, []int{1})
	if PerIteration() != 0 {
		t.Errorf("PerIteration is proved to return 0, the first iteration's value")
	}
}
