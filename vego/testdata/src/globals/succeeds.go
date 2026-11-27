package globals

// The always-fails check with assigned variables in a contract (found
// with F40, from the trial's digraph.allpaths): where the storage of an
// assigned variable lies is an input, not something a call produces, and
// a sample gives it an allocation of its own.

var attempts int

// SetAttempts assigns attempts, so that it is an assigned variable.
func SetAttempts(n int) { attempts = n }

// Retry succeeds whatever attempts holds.
//
// @Modifies attempts
// @Ensures err = nil
func Retry() (err error) {
	attempts = 0
	return nil
}

// RetryMaybe may fail for every input its contract allows.
//
// @Modifies attempts
// @Ensures True
func RetryMaybe() (err error) { // want `vego: the contract of RetryMaybe may also be met by a function that always returns an error`
	attempts = 0
	return nil
}
