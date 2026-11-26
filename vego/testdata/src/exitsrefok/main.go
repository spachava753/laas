// Command exitsrefok calls its own main, which returns, as it did before
// functions that end the process were supported.
package main

// main returns.
//
// @Ensures True
func main() {
}

// Seven calls main twice and returns 7.
//
// @Ensures result = 7
func Seven() (result int) {
	main()
	main()
	return 7
}

// Runner is a function type with a contract.
//
// @Ensures True
type Runner func()

// AsValue makes a value of main.
//
// @Ensures r != nil
func AsValue() (r Runner) {
	return main
}
