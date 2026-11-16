// Package badtrust calls functions whose trusted contracts come from a file
// with a defect.
package badtrust

func divide(x int) int { return 1 / x }

func fine() int { return 0 }

// Wrap would divide by zero if the second requires were taken as the
// contract.
//
// @ Ensures True
func Wrap() (result int) {
	return divide(0) // want `the trusted contract of badtrust.divide \(defective-trusted.yaml:6\) cannot be used: defective-trusted.yaml:9: "requires" occurs more than once` `cannot verify Wrap: divide has a contract that could not be understood`
}

// UsesFine relies on an entry of the same file.
//
// @ Ensures True
func UsesFine() (result int) {
	return fine() // want `the trusted contract of badtrust.fine \(defective-trusted.yaml:\d+\) cannot be used: defective-trusted.yaml:9: "requires" occurs more than once` `cannot verify UsesFine: fine has a contract that could not be understood`
}
