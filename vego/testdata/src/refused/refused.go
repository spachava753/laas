// Package refused is analysed in the mode a caching driver must select.
package refused

// Double would verify, but nothing is verified in this mode.
//
// @Ensures y = 2 * x
func Double(x int) (y int) { // want `verification does not run under go vet`
	return x
}

// Plain has no annotations and draws no report.
func Plain(x int) int { return x }
