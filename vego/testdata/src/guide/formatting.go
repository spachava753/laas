package guide

import (
	"fmt"
	"io"
	"log"
	"os"
)

// The programs of the section on formatting and logging.

// @Requires |host| <= 1000
// @Ensures True
func Announce(host string, port int, done, total int) (addr string) {
	addr = fmt.Sprintf("%s:%d", host, port)
	log.Printf("processed %d of %d", done, total)
	_, _ = fmt.Println("listening on", addr)
	return addr
}

// @Ensures True
func Display(v any) {
	_, _ = fmt.Println(v) // want `vego:\ cannot\ verify\ Display:\ Println\ formats\ v,\ a\ value\ of\ type\ any,\ and\ that\ may\ run\ code\ nobody\ has\ checked:\ any\ is\ an\ interface,\ which\ can\ hold\ a\ value\ with\ methods\ that\ fmt\ would\ call;\ only\ numbers,\ booleans,\ strings,\ and\ slices\ and\ structs\ of\ them,\ pointers\ to\ such\ structs,\ errors\ of\ known\ origin,\ and\ values\ whose\ String\ or\ Error\ method\ has\ a\ contract\ that\ modifies\ nothing\ can\ be\ formatted`
}

// @Ensures True
func ShowAll(values []any) {
	_, _ = fmt.Println(values...) // want `vego:\ cannot\ verify\ ShowAll:\ Println\ formats\ what\ the\ slice\ values\ holds`
}

// @Requires w != nil And l != nil And ready(l)
// @Ensures True
func Inventory(w io.Writer, l *log.Logger, n int) (err error) {
	l.Printf("%d items", n)
	_, err = fmt.Fprintf(w, "%d items\n", n)
	return err
}

// @Ensures True
func ToStderr(n int) {
	_, _ = fmt.Fprintf(os.Stderr, "%d\n", n)
}

// Logf is trusted, with formats.
func Logf(format string, args ...any) {
	log.Printf("app: "+format, args...)
}

// @Ensures True
func UsesLogf(n int) {
	Logf("%d items", n)
}

// LogfVerified cannot be verified: it formats what args holds.
//
// @Ensures True
func LogfVerified(format string, args ...any) {
	log.Printf("app: "+format, args...) // want `vego:\ cannot\ verify\ LogfVerified:\ Printf\ formats\ what\ the\ slice\ args\ holds`
}

// @Ensures True
func Fails(err error) {
	if err != nil {
		log.Fatal("failed") // want `vego:\ cannot\ verify\ Fails:\ it\ calls\ Fatal,\ which\ has\ no\ contract`
	}
}

// @Ensures True
func Greet(name string) {
	log.Println("hello", name) // want `vego:\ what\ Println\ builds\ from\ what\ it\ formats\ may\ be\ more\ than\ can\ be\ allocated;\ bound\ what\ it\ formats,\ as\ in\ .*Requires\ \|name\|\ <=\ 70368744159185`
}

type Temperature int

// @Requires t >= -273
// @Ensures True
func (t Temperature) String() (s string) {
	if t < 0 {
		return "below zero"
	}
	return "zero or above"
}

// @Requires t >= -273
// @Ensures True
func ShowTemperature(t Temperature) {
	log.Println("temperature", t)
}

// @Ensures True
func ShowAnyTemperature(t Temperature) {
	log.Println("temperature", t) // want `vego:\ precondition\ of\ String\ may\ not\ hold\ where\ Println\ formats\ t:\ t\ >=\ -273`
}

// @Ensures True
func LogsToZero() {
	l := &log.Logger{}
	l.Printf("x") // want `vego:\ precondition\ of\ Printf\ may\ not\ hold:\ ready\(l\)`
}

// @Requires w != nil
// @Ensures True
func LogsTo(w io.Writer, n int) {
	l := log.New(w, "app: ", log.LstdFlags)
	l.Printf("%d items", n)
}
