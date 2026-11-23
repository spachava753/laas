package guide

import (
	"fmt"
	"log"
	"math"
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
	return served
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
	return sizes[0] // want `^vego: postcondition may not hold: r = 1; the contents of sizes are not known to stay as initialised: the use at globals.go:50 lets a reference to them out$`
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
	fmt.Fprintln(os.Stderr, "warning:", msg)
}

// Client reads a variable whose type can hold code.
//
// @Ensures True
func Client() (r bool) {
	return http.DefaultClient != nil // want `vego: cannot verify Client: http.DefaultClient has type \*net/http.Client, which can hold a function value, an interface value, an error, a channel, or an unsafe.Pointer; package-level variables of such types are not supported yet`
}

// ResetServed sets the count to zero.
//
// @Modifies served
// @Ensures served' = 0
func ResetServed() {
	served = 0
}

// SetSize writes what a variable refers to.
//
// @Modifies sizes
// @Ensures sizes'[1] = 3
func SetSize() {
	sizes[1] = 3
}

// ResetAll calls ResetServed, and lists what it changes.
//
// @Modifies served
// @Ensures served' = 0
func ResetAll() {
	ResetServed()
}

// ResetUnlisted assigns a variable and does not list it.
//
// @Ensures True
func ResetUnlisted() {
	served = 0 // want `^vego: served is assigned, which ResetUnlisted may not modify; list it in a // @Modifies clause$`
}

// CallsReset calls ResetServed and does not list what it changes.
//
// @Ensures True
func CallsReset() {
	ResetServed() // want `^vego: ResetServed may modify what it calls served, which CallsReset may not modify; list it in a // @Modifies clause$`
}

// ListsSizes names a variable in Modifies.
//
// @Modifies sizes // want `^vego: Modifies lists sizes, but ListsSizes never needs to modify it; a Modifies clause must list exactly what the function may write$`
func ListsSizes() {}

var nextTicket int

// Ticket returns the next number, and asks too much of its callers.
//
// @Requires nextTicket < 1000 // want `^vego: the Requires clause nextTicket < 1000 reads nextTicket, a package-level variable that is not exported, and code of another package can call Ticket, where no caller can name the condition or see it fail; test the value in the body instead$`
// @Modifies nextTicket
// @Ensures n = nextTicket And nextTicket' = nextTicket + 1
func Ticket() (n int) {
	n = nextTicket
	nextTicket++
	return n
}

// TicketChecked tests the value in the body.
//
// @Modifies nextTicket
// @Ensures ok -> n = nextTicket And nextTicket' = nextTicket + 1
func TicketChecked() (n int, ok bool) {
	if nextTicket >= math.MaxInt {
		return 0, false
	}
	n = nextTicket
	nextTicket++
	return n, true
}
