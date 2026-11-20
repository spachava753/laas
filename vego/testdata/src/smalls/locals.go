package smalls

// string(x) of an integer is its UTF-8 encoding.

// @Requires 0 <= r < 128
// @Ensures |s| = 1 And s[0] = r
func ASCII(r rune) (s string) {
	return string(r)
}

// @Ensures 1 <= |s| <= 4
func AnyRune(r rune) (s string) {
	return string(r)
}

// @Ensures |s| = 1
func OneByte(r rune) (s string) {
	return string(r) // want `postcondition may not hold: \|s\| = 1`
}

// @Requires 2048 <= r < 55296
// @Ensures |s| = 3 And s[0] = 224 + r / 4096
func ThreeBytes(r rune) (s string) {
	return string(r)
}

// @Ensures s = "\xef\xbf\xbd"
func Invalid(r rune) (s string) {
	if r >= 0 {
		return string(rune(-1))
	}
	return string(r)
}

// @Requires 0 <= b < 128
// @Ensures s = "x" And |t| = 2 And t[1] = b
func Bytes(b byte) (s, t string) {
	return string(rune('x')), string(rune('x')) + string(b)
}

// Local type declarations run nothing.

// @Requires |names| <= 100
// @Ensures n = |names|
func Chain(names []string) (n int) {
	type link struct {
		name string
		next *link
	}
	var head *link
	// @Invariant n = i
	for i := range names {
		head = &link{name: names[i], next: head}
		n++
	}
	_ = head
	return n
}

// @Requires 0 <= n < 100
// @Ensures r = n + 1
func Celsius(n int) (r int) {
	type celsius int
	type degrees = celsius
	var c degrees = celsius(n)
	return int(c) + 1
}

// Two local types of one name in two functions are two types.

// @Ensures r = 1
func FirstT() (r int) {
	type T struct{ x int8 }
	t := T{x: 1}
	return int(t.x)
}

// @Ensures r
func SecondT() (r bool) {
	type T struct{ x bool }
	t := &T{x: true}
	return t.x
}

// A local type with the fields of a type of the package converts to it,
// and the two pointers then share their memory.

type P struct{ x int }

// @Ensures r = 2
func Converted() (r int) {
	type pt struct{ x int }
	a := &pt{x: 1}
	b := (*P)(a)
	b.x = 2
	return a.x
}

// @Ensures r = 1
func ConvertedWrong() (r int) {
	type pt struct{ x int }
	a := &pt{x: 1}
	b := (*P)(a)
	b.x = 2
	return a.x // want `postcondition may not hold: r = 1`
}

// A type declared inside a function cannot have annotations.

// @Ensures True
func Annotated() {
	// @Invariant x > 0 // want `Invariant annotation stands on a type declared inside Annotated; a type declared inside a function cannot have annotations, so declare it at package level to give it an invariant or a contract`
	type positive struct {
		// @Requires x > 0 // want `Requires annotation stands on a type declared inside Annotated`
		x int
	}
	// @Ensures r > 0 // want `Ensures annotation stands on a type declared inside Annotated`
	type maker func() (r int)
	type getter interface {
		// @Ensures r > 0 // want `Ensures annotation stands on a type declared inside Annotated`
		Get() (r int)
	}
	_ = positive{}
	var m maker
	var g getter
	_, _ = m, g
}

// An Assert or a Snapshot directly above a local type is read in the body.

// @Requires n > 1
// @Ensures True
func AboveType(n int) {
	// @Snapshot n0 = n
	// @Assert n > 1
	type pair struct{ a, b int }
	n--
	// @Assert n0 = n + 1
	// @Assert n > 1 // want `assertion may not hold: n > 1`
	type other struct{ c int }
	_, _ = pair{}, other{}
}
