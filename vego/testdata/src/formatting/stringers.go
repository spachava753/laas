package formatting

import (
	"errors"
	"fmt"
	"io"
	"log"
	"time"
)

// Formatting a value whose String or Error method has a contract calls
// that method, which is checked where the value is formatted.

type Coord struct{ X, Y int }

// @Ensures True
func (c Coord) String() (s string) { return "coord" }

// @Ensures True
func ShowsCoord(c Coord, cs []Coord) {
	log.Println("at", c)
	_, _ = fmt.Printf("%v %d %+v\n", c, c, c)
}

// Kelvin may only be shown when it is not below zero.
type Kelvin int

// @Requires k >= 0
// @Ensures True
func (k Kelvin) String() (s string) { return "K" }

// @Requires k >= 0
// @Ensures True
func ShowsKelvin(k Kelvin) {
	log.Print(k)
}

// @Ensures True
func ShowsAnyKelvin(k Kelvin) {
	log.Print(k) // want `vego:\ precondition\ of\ String\ may\ not\ hold\ where\ Print\ formats\ k:\ k\ >=\ 0`
}

// Both is an error and a Stringer; fmt calls Error, which has a contract.
type Both struct{ code int }

// @Ensures True
func (b Both) Error() (s string) { return "both" }

func (b Both) String() string { return "string" }

// @Ensures True
func ShowsBoth(b Both) (s string) {
	return fmt.Sprint(b)
}

// CodeError is an error that fmt.Errorf would wrap with %w, though its
// static type is not error.
type CodeError struct{ code int }

// @Ensures True
func (e CodeError) Error() (s string) { return "code" }

var ErrC error = errors.New("c")

// @Ensures r = False
func Found() (r bool) {
	err := fmt.Errorf("x: %w", CodeError{1}) // want `vego:\ cannot\ verify\ Found:\ fmt\.Errorf\ formats\ CodeError\{…\},\ a\ value\ of\ type\ formatting\.CodeError,\ which\ is\ an\ error\ that\ %w\ would\ wrap`
	return errors.Is(err, ErrC)
}

// A Stringer is not wrapped, so fmt.Errorf may format one.
//
// @Requires k >= 0
// @Ensures err = nil <-> ~fail
func WrapsKelvin(fail bool, k Kelvin) (err error) {
	if !fail {
		return nil
	}
	return fmt.Errorf("at %v: %w", k, io.EOF)
}

// Tally's String writes the slice it holds.
type Tally struct{ counts []int }

// @Requires |t.counts| > 0
// @Modifies t.counts
// @Ensures True
func (t Tally) String() (s string) {
	t.counts[0] = 0
	return "t"
}

// @Requires |t.counts| > 0
// @Modifies t.counts
// @Ensures True
func ShowsTally(t Tally) {
	log.Print(t) // want `vego:\ cannot\ verify\ ShowsTally:\ Print\ formats\ t,\ and\ fmt\ may\ call\ \(formatting\.Tally\)\.String\ any\ number\ of\ times,\ which\ modifies\ memory`
}

// Loop formats itself in its String, which never ends.
type Loop struct{ n int }

// @Ensures True
func (l Loop) String() (s string) {
	return fmt.Sprint(l) // want `vego:\ recursive\ call\ needs\ a\ .*\ annotation\ in\ the\ doc\ comment\ of\ String`
}

// Echo calls back into the function that formats it.
type Echo struct{ n int }

// @Ensures True
func (e Echo) String() (s string) {
	return Speak(e.n) // want `vego:\ recursive\ call\ needs\ a\ .*\ annotation\ in\ the\ doc\ comment\ of\ String`
}

// @Ensures True
func Speak(n int) (s string) {
	return fmt.Sprint(Echo{n}) // want `vego:\ recursive\ call\ needs\ a\ .*\ annotation\ in\ the\ doc\ comment\ of\ Speak`
}

// Ints may be shown only while its first element is positive.
type Ints []int

// @Requires |s| > 0 And s[0] > 0
// @Ensures True
func (s Ints) String() (r string) { return "ints" }

// A deferred call formats its values when the function returns.
//
// @Requires |xs| > 0 And |xs| <= 100
// @Modifies xs
// @Ensures True
func DeferredInts(xs []int) {
	xs[0] = 1
	defer fmt.Println(Ints(xs))
	xs[0] = 2
}

// @Requires |xs| > 0 And |xs| <= 100
// @Modifies xs
// @Ensures True
func DeferredIntsWrong(xs []int) {
	xs[0] = 1
	defer fmt.Println(Ints(xs)) // want `vego:\ precondition\ of\ String\ may\ not\ hold\ where\ Println\ formats\ Ints\(xs\):\ s\[0\]\ >\ 0`
	xs[0] = -1
}

// Server has its String on the pointer.
type Server struct{ Port int }

// @Requires s != nil
// @Ensures True
func (s *Server) String() (r string) { return "server" }

// @Requires s != nil
// @Ensures True
func ShowsServer(s *Server) {
	log.Println(s)
}

// @Ensures True
func ShowsNilServer(s *Server) {
	log.Println(s) // want `vego:\ precondition\ of\ String\ may\ not\ hold\ where\ Println\ formats\ s:\ s\ !=\ nil`
}

// fmt calls Coord's String on what a *Coord points to.
//
// @Requires c != nil
// @Ensures True
func ShowsCoordPointer(c *Coord) {
	log.Println(c)
}

// @Ensures True
func ShowsNilCoordPointer(c *Coord) {
	log.Println(c) // want `vego:\ Println\ formats\ c\ and\ calls\ String\ on\ what\ it\ points\ to,\ and\ c\ may\ be\ nil`
}

// Framed holds a Coord, whose String fmt would call at depth.
type Framed struct{ C Coord }

// @Ensures True
func ShowsFramed(f Framed) {
	log.Println(f) // want `vego:\ cannot\ verify\ ShowsFramed:\ Println\ formats\ f,\ a\ value\ of\ type\ formatting\.Framed,\ and\ that\ may\ run\ code\ nobody\ has\ checked:\ formatting\.Coord\ has\ a\ method\ String`
}

// Custom formats itself.
type Custom struct{ n int }

// @Ensures True
func (c Custom) String() (s string) { return "c" }

func (c Custom) Format(f fmt.State, verb rune) {}

// @Ensures True
func ShowsCustom(c Custom) {
	log.Println(c) // want `vego:\ cannot\ verify\ ShowsCustom:\ Println\ formats\ c,\ a\ value\ of\ type\ formatting\.Custom,\ and\ that\ may\ run\ code\ nobody\ has\ checked:\ formatting\.Custom\ has\ a\ method\ Format`
}

// time.Duration's String has an entry in the trust file.
//
// @Ensures True
func ShowsDuration(d time.Duration) {
	log.Println("took", d)
}

// Show is a function type with a contract.
//
// @Ensures True
type Show func() (s string)

// Calls has a String that calls through a function value.
type Calls struct{ n int }

// @Ensures True
func (c Calls) String() (s string) {
	f := makeShow()
	return f() // want `this call may not end: Calls.String calls f\(\) at stringers.go:\d+:\d+, which may run Calls.String`
}

// @Ensures r != nil
func makeShow() (r Show) {
	return func() (s string) { return "x" }
}

// A value made by verified code may not run code that calls through a
// value, and formatting a Calls runs its String.
//
// @Ensures True
func MakesShow() (r Show) {
	return func() (s string) { return fmt.Sprint(Calls{1}) } // want `vego:\ cannot\ verify\ MakesShow:\ the\ function\ literal\ used\ as\ a\ value\ calls\ Sprint,\ which\ formats\ a\ value\ whose\ \(formatting\.Calls\)\.String\ may\ call\ through\ a\ function\ value`
}

// showCalls formats a Calls, so it may call through a value too, and that
// value may be showCalls itself, which MakesShowNamed makes.
//
// @Ensures True
func showCalls() (s string) {
	return fmt.Sprint(Calls{2}) // want `this call may not end: showCalls calls Calls.String at stringers.go:\d+:\d+, Calls.String calls f\(\) at stringers.go:\d+:\d+, which may run showCalls`
}

// @Ensures True
func MakesShowNamed() (r Show) {
	return showCalls // want `vego:\ cannot\ verify\ MakesShowNamed:\ showCalls\ may\ call\ through\ a\ function\ value.*showCalls\ calls\ String,\ which\ calls\ through`
}
