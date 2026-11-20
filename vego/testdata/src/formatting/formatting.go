// Package formatting holds calls of the functions that format their
// operands: those of fmt and log, which ship with entries under formats,
// fmt.Errorf, and a project's own logging function.
package formatting

import (
	"errors"
	"fmt"
	"io"
	"log"
	"path"
	"path/filepath"
)

type Point struct {
	X, Y int
}

// Probe has its methods on the pointer, which fmt never calls for a value.
type Probe struct{ n int }

func (p *Probe) String() string { return "probe" }

// Held holds a Probe in an exported field.
type Held struct {
	P     Probe
	Label string
}

type Name string

// @Ensures True
func Formats(host string, port int, p Point, ps []Point, h Held, n Name) (s string) {
	s = fmt.Sprintf("%s:%d", host, port)
	s = fmt.Sprint(s, p, ps, h, n, nil, 2.5, true, []byte("x"))
	return fmt.Sprintln(s, errors.New("made"), io.EOF)
}

// @Ensures True
func Prints(done, total int, name string) {
	_, _ = fmt.Printf("processed %d of %d\n", done, total)
	_, _ = fmt.Println("starting", name)
	_, _ = fmt.Print()
	log.Printf("processed %d of %d", done, total)
	log.Println("starting", name)
	log.Print(name)
}

// @Requires w != nil
// @Ensures True
func Writes(w io.Writer, n int) (err error) {
	_, err = fmt.Fprintf(w, "%d items\n", n)
	return err
}

// @Ensures True
func WritesNil(w io.Writer, n int) {
	_, _ = fmt.Fprintln(w, n) // want `vego:\ precondition\ of\ Fprintln\ may\ not\ hold:\ w\ !=\ nil`
}

// @Requires l != nil
// @Ensures True
func Logs(l *log.Logger, n int) {
	l.Printf("%d", n)
	l.Println(n)
	l.Print(n)
}

// @Ensures True
func LogsNil(l *log.Logger, n int) {
	l.Print(n) // want `vego:\ precondition\ of\ Print\ may\ not\ hold:\ l\ !=\ nil`
}

// @Ensures |p| = 0
func Joins() (p string) {
	return path.Join("", "") + filepath.Join()
}

// @Ensures |p| = 0
func JoinsWrong(a string) (p string) {
	return path.Join(a, "") // want `vego:\ postcondition\ may\ not\ hold:\ \|p\|\ =\ 0`
}

// @Ensures err = nil <-> ~fail
func Wraps(fail bool, p Point, n Name) (err error) {
	if !fail {
		return nil
	}
	return fmt.Errorf("at %v (%s): %w", p, n, io.EOF)
}

// @Ensures True
func FormatsAny(v any) {
	_, _ = fmt.Println(v) // want `vego:\ cannot\ verify\ FormatsAny:\ Println\ formats\ v,\ a\ value\ of\ type\ any,\ and\ that\ may\ run\ code\ nobody\ has\ checked:\ any\ is\ an\ interface`
}

// @Ensures True
func FormatsPointer(p *Point) {
	log.Print(p) // want `vego:\ cannot\ verify\ FormatsPointer:\ Print\ formats\ p,\ a\ value\ of\ type\ \*formatting\.Point,\ and\ that\ may\ run\ code\ nobody\ has\ checked:\ \*formatting\.Point\ is\ a\ pointer`
}

// @Ensures True
func FormatsSpread(vs []any) {
	_, _ = fmt.Println(vs...) // want `vego:\ cannot\ verify\ FormatsSpread:\ Println\ formats\ what\ the\ slice\ vs\ holds,\ which\ can\ be\ anything`
}

// @Ensures True
func FormatsUnknownError(err error) {
	log.Println("failed:", err) // want `vego:\ cannot\ verify\ FormatsUnknownError:\ formatting\ err\ would\ run\ the\ methods\ of\ an\ error\ whose\ origin\ is\ not\ known`
}

type Nest []Nest

// @Ensures True
func FormatsNest(n Nest) (s string) {
	return fmt.Sprint(n) // want `vego:\ cannot\ verify\ FormatsNest:\ Sprint\ formats\ n,\ a\ value\ of\ type\ formatting\.Nest,\ and\ that\ may\ run\ code\ nobody\ has\ checked:\ formatting\.Nest\ holds\ itself`
}

// @Ensures True
func FormatsMap(m map[string]int) (s string) {
	return fmt.Sprint(m) // want `vego:\ cannot\ verify\ FormatsMap:\ Sprint\ formats\ m,\ a\ value\ of\ type\ map\[string\]int`
}

// Celsius has a String method of its own.
type Celsius int

func (c Celsius) String() string { return "C" }

// @Ensures True
func FormatsStringer(c Celsius) (s string) {
	return fmt.Sprint(c) // want `vego:\ cannot\ verify\ FormatsStringer:\ Sprint\ formats\ c,\ a\ value\ of\ type\ formatting\.Celsius,\ and\ that\ may\ run\ code\ nobody\ has\ checked:\ formatting\.Celsius\ has\ a\ method\ String`
}

// The error that Println returns is not known, so the contract may leave
// success open.
//
// @Ensures True
func Greets(name string) (err error) {
	_, err = fmt.Println("hello", name)
	return err
}
