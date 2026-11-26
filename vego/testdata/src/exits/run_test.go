package exits

import "testing"

// TestReturns checks what the contracts of exits say where the functions
// return. Where they end the process, the shipped entries' harness shows
// what os.Exit and log.Fatal do.
func TestReturns(t *testing.T) {
	if got := Name([]string{"tool", "a"}); got != "a" {
		t.Errorf("Name is proved to return args[1], returned %q", got)
	}
	if got := NameExit([]string{"tool", "b", "c"}); got != "b" {
		t.Errorf("NameExit is proved to return args[1], returned %q", got)
	}
	if got := Between(4); got != 4 {
		t.Errorf("Between(4) is proved to be in (0, 10], returned %d", got)
	}
	if got := BetweenSwapped(10); got != 10 {
		t.Errorf("BetweenSwapped(10) returned %d", got)
	}
	if got := Run("abc"); got != 3 {
		t.Errorf("Run is proved to return |name|, returned %d", got)
	}
	if got := Dead(0); got != 1 {
		t.Errorf("Dead is proved to return 1, returned %d", got)
	}
	if got := InPlace(5); got != 5 {
		t.Errorf("InPlace is proved to return n, returned %d", got)
	}
	if got := Deferred(1); got != 1 {
		t.Errorf("Deferred is proved to return 1, returned %d", got)
	}
	if got := DeadExitDeferred(); got != 7 {
		t.Errorf("DeadExitDeferred is proved to return 7, returned %d", got)
	}
	if got := UnevaluatedExitDeferred(); got != 7 {
		t.Errorf("UnevaluatedExitDeferred is proved to return 7, returned %d", got)
	}
	if !Ready(true) {
		t.Errorf("Ready(true) is proved to return true")
	}
	Check(nil)
	RunFormatted("x")
	Loop([]int{0, 1, 2})
}
