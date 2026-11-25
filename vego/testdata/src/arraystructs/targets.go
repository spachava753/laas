package arraystructs

// A Modifies entry that names a field holding an array, a struct that holds
// one, or an element of a slice of such structs covers every element of the
// array, its last one included (F16 of the review of S2 of F36).

// set15 writes the last element of the array under Modifies b.out.
//
// @Requires b != nil
// @Modifies b.out
// @Ensures b.out'[15] = 9
func set15(b *buffer) {
	b.out[15] = 9
}

// @Requires b != nil
// @Modifies b
// @Ensures b.out'[15] = 9
func CallSet15(b *buffer) {
	set15(b)
}

// @Requires b != nil And b.out[15] = 1
// @Modifies b
// @Ensures b.out'[15] = 1
func CallSet15Wrong(b *buffer) {
	set15(b)
} // want `postcondition may not hold: b.out'\[15\] = 1`

// setLast is trusted; its entry lists b.out.
func setLast(b *buffer) { b.out[15] = 7 }

// @Requires b != nil And b.out[15] = 1
// @Modifies b
// @Ensures b.out'[15] = 1
func CallSetLastWrong(b *buffer) {
	setLast(b)
} // want `postcondition may not hold: b.out'\[15\] = 1`

// @Requires b != nil And b.out[15] = 1
// @Modifies b
// @Ensures b.n' = b.n
func CallSetLast(b *buffer) {
	setLast(b)
}

// holder holds a buffer.
type holder struct {
	tag int
	in  buffer
}

// setInner writes the last element of the array of a struct in a field.
//
// @Requires o != nil
// @Modifies o.in
// @Ensures o.in.out'[15] = 9
func setInner(o *holder) {
	o.in.out[15] = 9
}

// @Requires o != nil And o.in.out[15] = 1
// @Modifies o
// @Ensures o.in.out'[15] = 1
func CallSetInnerWrong(o *holder) {
	setInner(o)
} // want `postcondition may not hold: o.in.out'\[15\] = 1`

// @Requires o != nil
// @Modifies o
// @Ensures o.in.out'[15] = 9 And o.tag' = o.tag
func CallSetInner(o *holder) {
	setInner(o)
}

// setInnerTrusted is trusted; its entry lists o.in.
func setInnerTrusted(o *holder) { o.in.out[15] = 7 }

// @Requires o != nil And o.in.out[15] = 1
// @Modifies o
// @Ensures o.in.out'[15] = 1
func CallSetInnerTrustedWrong(o *holder) {
	setInnerTrusted(o)
} // want `postcondition may not hold: o.in.out'\[15\] = 1`

// setElement writes the last element of the array of an element of a slice.
//
// @Requires 0 <= i < |bs|
// @Modifies bs[i]
// @Ensures bs'[i].out[15] = 9
func setElement(bs []buffer, i int) {
	bs[i].out[15] = 9
}

// @Requires |bs| > 0 And bs[0].out[15] = 1
// @Modifies bs
// @Ensures bs'[0].out[15] = 1
func CallSetElementWrong(bs []buffer) {
	setElement(bs, 0)
} // want `postcondition may not hold: bs'\[0\].out\[15\] = 1`

// @Requires |bs| > 1
// @Modifies bs
// @Ensures bs'[0].out[15] = 9 And bs'[1].n = bs[1].n
func CallSetElement(bs []buffer) {
	setElement(bs, 0)
}

// setElementTrusted is trusted; its entry lists xs[i].
func setElementTrusted(bs []buffer, i int) { bs[i].out[15] = 7 }

// @Requires |bs| > 0 And bs[0].out[15] = 1
// @Modifies bs
// @Ensures bs'[0].out[15] = 1
func CallSetElementTrustedWrong(bs []buffer) {
	setElementTrusted(bs, 0)
} // want `postcondition may not hold: bs'\[0\].out\[15\] = 1`
