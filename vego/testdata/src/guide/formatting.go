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
	_, _ = fmt.Println(v) // want `vego:\ cannot\ verify\ Display:\ Println\ formats\ v,\ a\ value\ of\ type\ any,\ and\ that\ may\ run\ code\ nobody\ has\ checked:\ any\ is\ an\ interface,\ which\ can\ hold\ a\ value\ with\ methods\ that\ fmt\ would\ call;\ only\ numbers,\ booleans,\ strings,\ and\ slices\ and\ structs\ of\ them\ without\ such\ methods,\ and\ errors\ of\ known\ origin,\ can\ be\ formatted`
}

// @Ensures True
func ShowAll(values []any) {
	_, _ = fmt.Println(values...) // want `vego:\ cannot\ verify\ ShowAll:\ Println\ formats\ what\ the\ slice\ values\ holds`
}

// @Requires w != nil And l != nil
// @Ensures True
func Inventory(w io.Writer, l *log.Logger, n int) (err error) {
	l.Printf("%d items", n)
	_, err = fmt.Fprintf(w, "%d items\n", n)
	return err
}

// @Ensures True
func ToStderr(n int) {
	_, _ = fmt.Fprintf(os.Stderr, "%d\n", n) // want `vego:\ cannot\ verify\ ToStderr:\ `
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
	log.Println("hello", name) // want `vego:\ what\ Println\ builds\ from\ what\ it\ formats\ may\ be\ more\ than\ can\ be\ allocated;\ bound\ the\ lengths\ of\ the\ strings\ and\ slices\ it\ formats,\ and\ of\ a\ format\ that\ is\ not\ a\ constant`
}
