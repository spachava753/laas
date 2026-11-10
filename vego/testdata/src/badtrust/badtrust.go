// Package badtrust calls functions whose trusted contracts come from a file
// with a defect.
package badtrust

func divide(x int) int { return 1 / x }

func fine() int { return 0 }

// Wrap would divide by zero if the second requires were taken as the
// contract.
func Wrap() int {
	return divide(0) // want `the trusted contract of badtrust.divide \(defective-trusted.yaml:6\) cannot be used: defective-trusted.yaml:9: "requires" occurs more than once` `cannot verify Wrap: divide has a contract that could not be understood`
}

//@ Ensures True

// UsesFine relies on an entry of the same file.
func UsesFine() int {
	return fine() // want `the trusted contract of badtrust.fine \(defective-trusted.yaml:11\) cannot be used: defective-trusted.yaml:9: "requires" occurs more than once` `cannot verify UsesFine: fine has a contract that could not be understood`
}

//@ Ensures True
