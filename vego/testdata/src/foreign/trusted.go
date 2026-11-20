package foreign

import "foreignlib"

// Takes takes a sink.
//
// @Requires s != nil
type Takes func(s foreignlib.Sink)

// A sink can be handed to a function value: every method of Sink has a
// contract.
//
// @Requires f != nil And s != nil
// @Ensures True
func HandsSink(f Takes, s foreignlib.Sink) {
	f(s) // want `this\ call\ may\ not\ end:\ HandsSink\ hands\ s\ to\ f\(s\)\ at\ trusted\.go:\d+:\d+,\ which\ may\ run\ HandsSink`
}

// TakesCtx takes a context of foreignlib.
//
// @Ensures True
type TakesCtx func(c foreignlib.Ctx)

// A Ctx cannot: Done has no contract.
//
// @Requires f != nil
// @Ensures True
func HandsCtx(f TakesCtx, c foreignlib.Ctx) {
	f(c) // want `cannot verify HandsCtx: c is passed to the function value f and is a value of type foreignlib.Ctx, which can hold an interface value with a method that has no contract`
}

// Job is made of what calls trusted functions.
//
// @Requires 0 <= n <= 100
// @Ensures m = n
type Job func(n int) (m int)

func pingCtx(c foreignlib.Ctx) {}

// Verified code can make no Ctx, since Done has no contract, so a trusted
// function that runs one runs no code that verified code made.
//
// @Ensures j != nil
func WithCtx(c foreignlib.Ctx) (j Job) {
	return func(n int) int {
		pingCtx(c)
		return n
	}
}

func passSink(s foreignlib.Sink) {}

// Verified code can make a Sink, so a trusted function that runs one may
// run code that verified code made, which could call back.
//
// @Ensures j != nil
func WithSink(s foreignlib.Sink) (j Job) {
	return func(n int) int {
		passSink(s) // want `cannot verify WithSink: the function literal used as a value calls passSink, which may call through a function value`
		return n
	}
}

func sinkOf() (s foreignlib.Sink) { return nil }

// A trusted function that returns a value of a type with an entry vouches
// for it in its own entry.
//
// @Ensures True
func Unvouched() (s foreignlib.Sink) {
	return sinkOf() // want `the trusted contract of foreign.sinkOf \(trusted.yaml:\d+\) cannot be used: its result s can hold a function value or an interface value of a type with a contract; list it under vouches`
}

func vouchedSink() (s foreignlib.Sink) { return Doubler{} }

// @Ensures err = nil -> 0 <= y <= 2
func Vouched() (y int, err error) {
	s := vouchedSink()
	if s == nil {
		return 0, nil
	}
	return s.Put(1)
}
