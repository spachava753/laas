package guide

import (
	"fmt"
	"log"
	"net/http"
	"os"
)

var digits = "0123456789abcdef"

var limits = map[string]int{"free": 10, "pro": 1000}

// Hex returns the digit for d.
//
// @Requires 0 <= d < 16
// @Ensures r = digits[d]
func Hex(d int) (r byte) {
	return digits[d]
}

// Limit returns the limit of a plan.
//
// @Ensures ok <-> (plan = "free" Or plan = "pro")
// @Ensures plan = "pro" -> n = 1000
func Limit(plan string) (n int, ok bool) {
	n, ok = limits[plan]
	return n, ok
}

var served int

// Serve counts requests, and is not verified.
func Serve() {
	served++
}

// Served reads the count.
//
// @Ensures True
func Served() (r int) {
	return served // want `vego: cannot verify Served: served is assigned at globals.go:35; package-level variables that are changed are not supported yet`
}

var sizes = []int{1, 2, 4}

// Grow writes the table, and is not verified.
func Grow() {
	sizes[0] = 8
}

// FirstSize reads the table.
//
// @Ensures r = 1
func FirstSize() (r int) {
	return sizes[0] // want `^vego: postcondition may not hold: r = 1; the contents of sizes are not known to stay as initialised: the use at globals.go:49 lets a reference to them out$`
}

var pageSize = os.Getpagesize()

// Pages counts the pages that n bytes take.
//
// @Requires pageSize > 0 // want `vego: the Requires clause pageSize > 0 reads only package-level variables, and their declarations do not show that it holds; test the value in the body instead`
// @Requires n >= 0
// @Ensures True
func Pages(n int) (r int) {
	return n / pageSize
}

// PagesChecked tests the value in the body.
//
// @Requires n >= 0
// @Ensures True
func PagesChecked(n int) (r int) {
	if pageSize <= 0 {
		return 0
	}
	return n / pageSize
}

var logger = log.New(os.Stderr, "app: ", 0)

// Notify writes to a package-level logger.
//
// @Requires |msg| <= 1000
// @Ensures True
func Notify(msg string) {
	if logger != nil { // want `vego: cannot verify Notify: logger has type \*log.Logger, which can hold a function value, an interface value, an error, a channel, or an unsafe.Pointer; package-level variables of such types are not supported yet`
		logger.Printf("report: %s", msg)
	}
}

// Warn writes to standard error.
//
// @Requires |msg| <= 1000
// @Ensures True
func Warn(msg string) {
	fmt.Fprintln(os.Stderr, "warning:", msg) // want `vego: cannot verify Warn: it uses Write as a method of io.Writer, and Write has no contract; annotate Write with // @ annotations so that it is verified, or add a trusted contract for \(\*os.File\).Write to vego-trusted.yaml`
}

// Client reads a variable whose type can hold code.
//
// @Ensures True
func Client() (r bool) {
	return http.DefaultClient != nil // want `vego: cannot verify Client: http.DefaultClient has type \*net/http.Client, which can hold a function value, an interface value, an error, a channel, or an unsafe.Pointer; package-level variables of such types are not supported yet`
}

// ResetServed assigns a variable.
//
// @Ensures True
func ResetServed() {
	served = 0 // want `vego: cannot verify ResetServed: served is a package-level variable, which a verified function cannot assign yet`
}

// SetSize writes what a variable refers to.
//
// @Ensures True
func SetSize() {
	sizes[1] = 3 // want `vego: cannot verify SetSize: sizes\[1\] writes memory that the package-level variable sizes refers to, which a Modifies clause cannot name yet`
}

// ListsSizes names a variable in Modifies.
//
// @Modifies sizes // want `vego: in Modifies annotation: sizes is a package-level variable, which a Modifies clause cannot name yet`
func ListsSizes() {}
