// Package uses calls the methods of lib's interfaces on what it is handed.
// lib's implementations of them, which are not verified, are what the calls
// may run, and what they run is part of what these functions run (F3 of
// the review of the design of F43).
package uses

import (
	"cycles/runs/lib"
	"cycles/runs/libg"
	"cycles/runs/libr"
)

// Next calls Next of what it is handed; lib's wrap runs Read of what it
// wraps.
//
// @Requires x != nil
// @Ensures True
func Next(x lib.Source) (c byte) { return x.Next() }

// Name calls Name of what it is handed; lib's Encoded encodes what it
// holds.
//
// @Requires x != nil
// @Ensures True
func Name(x lib.Namer) (s string) { return x.Name() }

// Run calls Run of what it is handed; lib's Valued calls a method value
// of the *bufio.Reader it holds.
//
// @Requires x != nil
// @Ensures True
func Run(x lib.Runner) { x.Run() }

// Time calls Time of what it is handed; lib's Timed calls a function of
// the runtime by its symbol.
//
// @Requires x != nil
// @Ensures True
func Time(x lib.Timer) (n int64) { return x.Time() }

// Label calls Label of what it is handed; lib's Printed formats what it
// holds.
//
// @Requires x != nil
// @Ensures True
func Label(x lib.Labeler) (s string) { return x.Label() }

// @Requires x != nil
// @Ensures True
func Range(x lib.Ranger) { x.Range() }

// @Requires x != nil
// @Ensures True
func Val(x lib.Valuer) { x.Val() }

// @Requires x != nil
// @Ensures True
func Gen(x libg.Genner) { x.Gen() }

// @Requires x != nil
// @Ensures True
func Show(x libr.Shower) { x.Show() }
