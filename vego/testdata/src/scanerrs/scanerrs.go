// Package scanerrs is a module without a trust file of its own, so the
// shipped entries of bufio and io are the ones it uses: nothing vouches for
// what the error of a Scanner holds.
package scanerrs

import (
	"bufio"
	"fmt"
	"io"
)

// WrapsErr wraps the error of a Scanner, which may be one that the reader
// returned, of which nothing is known.
//
// @Requires r != nil
// @Ensures True
func WrapsErr(r io.Reader) (err error) {
	sc := bufio.NewScanner(r)
	if err := sc.Err(); err != nil {
		return fmt.Errorf("scan: %w", err) // want `vego: cannot verify WrapsErr: formatting err would run the methods of an error whose origin is not known`
	}
	return nil
}

// ReturnsErr returns the error of a Scanner as it is, which needs nothing
// to be known of it.
//
// @Requires r != nil
// @Ensures True
func ReturnsErr(r io.Reader) (err error) {
	sc := bufio.NewScanner(r)
	return sc.Err()
}

// ReadLines is the guide's program, which wraps the error of a Scanner;
// without the entries the guide shows, it cannot.
//
// @Requires r != nil And limit >= 0
// @Modifies r
// @Ensures 0 <= n And n <= limit
func ReadLines(r io.Reader, limit int) (n int, err error) {
	sc := bufio.NewScanner(r)
	// @Invariant 0 <= n And n <= limit And ready(sc)
	// @Variant limit - n
	for n < limit && sc.Scan() {
		fmt.Println(sc.Text())
		n++
	}
	if err := sc.Err(); err != nil {
		return n, fmt.Errorf("read lines: %w", err) // want `^vego: cannot verify ReadLines: formatting err would run the methods of an error whose origin is not known; only an error made by errors.New or fmt.Errorf, here or in a verified function, one that a contract vouches for, or one that holds a value of a type whose errors have a known origin, can be formatted; err is assigned sc.Err\(\) at scanerrs.go:49:12, a call whose errors nothing vouches for$`
	}
	return n, nil
}

// PrintLines is the guide's first program on reading lines, which returns
// the error of the Scanner as it is and verifies under the shipped entries.
//
// @Requires r != nil And limit >= 0
// @Modifies r
// @Ensures 0 <= n And n <= limit
func PrintLines(r io.Reader, limit int) (n int, err error) {
	sc := bufio.NewScanner(r)
	// @Invariant 0 <= n And n <= limit And ready(sc)
	// @Variant limit - n
	for n < limit && sc.Scan() {
		fmt.Println(sc.Text())
		n++
	}
	return n, sc.Err()
}
