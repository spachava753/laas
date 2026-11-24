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

// serve counts requests, and is not verified.
func serve() {
	served++
}

// Served reads the count.
//
// @Ensures True
func Served() (r int) {
	return served
}

var sizes = []int{1, 2, 4}

// growSizes writes the table, and is not verified.
func growSizes() {
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

// SetServed sets the count.
//
// @Modifies served
// @Ensures served' = n
func SetServed(n int) {
	served = n
}

// SetSize writes what a variable refers to.
//
// @Modifies sizes
// @Ensures sizes'[1] = n
func SetSize(n int) {
	sizes[1] = n
}

// resetAll calls SetServed, and lists what it changes.
//
// @Modifies served
// @Ensures served' = 0
func resetAll() {
	SetServed(0)
}

// ResetUnlisted assigns a variable and does not list it.
//
// @Ensures True
func ResetUnlisted() {
	served = 0 // want `^vego: served is assigned, which ResetUnlisted may not modify; list it in a // @Modifies clause$`
}

// CallsReset calls SetServed and does not list what it changes.
//
// @Ensures True
func CallsReset() {
	SetServed(0) // want `^vego: SetServed may modify served, which CallsReset may not modify; list it in a // @Modifies clause$`
}

// listsSizes names a variable in Modifies.
//
// @Modifies sizes // want `^vego: Modifies lists sizes, but listsSizes never needs to modify it; a Modifies clause must list exactly what the function may write$`
func listsSizes() {}

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

var routes = map[string]int{}

// resetRoutes gives routes a new map, and is not verified.
func resetRoutes() { routes = map[string]int{} }

// @Requires routes != nil
// @Modifies routes
// @Ensures routes'["/"] = 1
func addRoot() { routes["/"] = 1 }

// @Requires routes != nil
// @Modifies routes
// @Ensures True
func addTwo() {
	addRoot()
	routes["/a"] = 2 // want `^vego: routes\["/a"\] is assigned, which addTwo may not modify: nothing its // @Modifies clauses list is known to cover it; a clause covers what its path referred to when addTwo was called; routes may have been assigned since, by a statement or by a call that lists it, so it may no longer refer to that; a call that keeps it can say so in its contract with routes' = routes$`
}

// @Requires routes != nil
// @Modifies routes
// @Ensures routes' = routes And routes'["/"] = 1
func addRootKept() { routes["/"] = 1 }

// @Requires routes != nil
// @Modifies routes
// @Ensures True
func addTwoKept() {
	addRootKept()
	routes["/a"] = 2
}

var visits int

// CountVisit counts a visit, and is not verified.
func CountVisit(name string, depth int) {
	if visits < 1000 {
		visits++
	}
}

// Visit is called for each name a walk meets.
//
// @Ensures True
type Visit func(name string, depth int)

// Walk calls f once.
//
// @Requires f != nil
// @Ensures True
func Walk(f Visit) {
	f("a", 1) // want `^vego: f may modify visits, which Walk may not modify; code of this package that the call may run writes it; list it in a // @Modifies clause$`
}

// WalkListed lists what f may change.
//
// @Requires f != nil
// @Modifies visits
// @Ensures True
func WalkListed(f Visit) {
	f("a", 1)
}

var hits int

// countHit counts a request.
//
// @Modifies hits
// @Ensures hits < MaxInt -> hits' = hits + 1
func countHit() {
	if hits < math.MaxInt {
		hits++
	}
}
