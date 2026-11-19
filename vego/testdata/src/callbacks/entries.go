// Package callbacks hands functions to trusted functions that call them
// while they run.
package callbacks

// The trusted helpers of the entries below. Their bodies are not verified.

func each(n int, f func(i int)) {
	for i := 0; i < n; i++ {
		f(i)
	}
}

func notRun(n int, f func(i int))              {}
func notFunc(n int, f int)                     {}
func twice(n int, f func(i int))               {}
func wrongCount(n int, f func(i, j int))       {}
func sameName(n int, f func(i, j int))         {}
func clash(n int, f func(i int))               {}
func clashResult(n int, f func(i int)) (k int) { return 0 }
func reserved(n int, f func(i int))            {}
func badRequires(n int, f func(i int))         {}
func primed(xs []int, f func(i int))           {}
func takesError(f func(e error))               {}
func variadic(f func(xs ...int))               {}
func applied(is func(i int))                   {}
func withContract(n int, f Visit)              {}
func noParam(n int, f func(i int))             {}
func oldCall(n int, f func(i int))             {}
func oldPlain(n int)                           {}

// Visit has a contract of its own.
//
// @Requires 0 <= i
type Visit func(i int)

// UsesNotRun and the functions after it call the helpers whose entries
// have a defect.
//
// @Ensures True
func UsesNotRun() {
	notRun(1, nil) // want `the trusted contract of callbacks.notRun \(trusted.yaml:\d+\) cannot be used: its calls gives f a contract, so its runs must list f too: calls claims everything runs does` `cannot verify UsesNotRun: `
}

// @Ensures True
func UsesNotFunc() {
	notFunc(1, 2) // want `its runs lists f, whose type int can hold no` `its calls lists f, whose type int is not a function type` `cannot verify UsesNotFunc: `
}

// @Ensures True
func UsesTwice() {
	twice(1, nil) // want `its calls lists f twice` `cannot verify UsesTwice: `
}

// @Ensures True
func UsesWrongCount() {
	wrongCount(1, nil) // want `its calls names 1 parameters for f, whose type func\(i int, j int\) has 2` `cannot verify UsesWrongCount: `
}

// @Ensures True
func UsesSameName() {
	sameName(1, nil) // want `its calls names the parameter i of f twice` `cannot verify UsesSameName: `
}

// @Ensures True
func UsesClash() {
	clash(1, nil) // want `its calls names a parameter of f n, which is a parameter of clash already` `cannot verify UsesClash: `
}

// @Ensures True
func UsesClashResult() {
	_ = clashResult(1, nil) // want `its calls names a parameter of f k, which is a result of clashResult` `cannot verify UsesClashResult: `
}

// @Ensures True
func UsesReserved() {
	reserved(1, nil) // want `its calls names a parameter of f result, which means something else in a formula` `cannot verify UsesReserved: `
}

// @Ensures True
func UsesBadRequires() {
	badRequires(1, nil) // want `in its requires "0 <= i < m": .*m` `cannot verify UsesBadRequires: `
}

// @Ensures True
func UsesPrimed() {
	primed(nil, nil) // want `in its requires "xs'\[i\] > 0"` `cannot verify UsesPrimed: `
}

// @Ensures True
func UsesTakesError() {
	takesError(nil) // want `its calls lists f, whose type func\(e error\) takes or returns a error, which can hold code; that is not supported yet` `cannot verify UsesTakesError: `
}

// @Ensures True
func UsesVariadic() {
	variadic(nil) // want `its calls lists f, whose type func\(xs \.\.\.int\) is variadic or generic, which is not supported yet` `cannot verify UsesVariadic: `
}

// @Ensures True
func UsesIs() {
	applied(nil) // want `its calls lists is, which a formula reads as a word of its own when it is applied` `cannot verify UsesIs: `
}

// @Ensures True
func UsesWithContract() {
	withContract(1, nil) // want `its calls gives f a contract, but its type callbacks.Visit has a contract of its own` `cannot verify UsesWithContract: `
}

// @Ensures True
func UsesNoParam() {
	noParam(1, nil) // want `its calls g\(...\): g is not a parameter` `cannot verify UsesNoParam: `
}

// @Ensures True
func UsesOldCall() {
	oldCall(1, nil) // want `its calls requires "old\(i\) >= 0" for f uses old, which has no meaning there: it is read in the state at each call of f` `cannot verify UsesOldCall: `
}

// @Ensures True
func UsesOldPlain() {
	oldPlain(1) // want `its requires "old\(n\) > 0" uses old, which has no meaning there: a requires is read in the state of the call` `cannot verify UsesOldPlain: `
}

// UsesEach hands a function to a trusted function with a sound entry.
//
// @Ensures True
func UsesEach() {
	each(3, func(i int) {})
}

func runsOnly(n int, f func(i int)) {}

// HandsRunsOnly hands a literal to a parameter that the entry lists under
// runs with no contract under calls.
//
// @Ensures True
func HandsRunsOnly() {
	runsOnly(2, func(i int) {}) // want `cannot verify HandsRunsOnly: the function literal is handed to runsOnly as f, which its trusted contract lists under runs with no contract under calls; give f a contract under calls in the entry for callbacks.runsOnly`
}

// HandsRunsOnlyFunction hands it a function.
//
// @Ensures True
func HandsRunsOnlyFunction() {
	runsOnly(2, visitAny) // want `cannot verify HandsRunsOnlyFunction: visitAny is handed to runsOnly as f, which its trusted contract lists under runs with no contract under calls`
}

// Doubler maps a small number to a number at most twice as large.
//
// @Requires 0 <= x <= 10
// @Ensures 0 <= y <= 20
type Doubler func(x int) (y int)

func applyDoubler(f Doubler) int { return f(1) }

// same is a Doubler.
//
// @Requires 0 <= x <= 10
// @Ensures y = x
func same(x int) (y int) { return x }

// UsesNamed hands a function to a parameter under runs whose type has a
// contract: it is made into a value of the type.
//
// @Ensures 0 <= r <= 20
func UsesNamed() (r int) { return applyDoubler(same) }

// UsesLiteral does it with a literal.
//
// @Ensures 0 <= r <= 20
func UsesLiteral() (r int) { return applyDoubler(func(x int) int { return x }) }
