package guide

// The programs of the section When a proof fails of docs/verification.md,
// on a postcondition whose Forall is false at a return.

// @Predicate digit(c) ::= 48 <= c <= 57

// @Requires |src| / 2 <= |dst|
// @Modifies dst
// @Ensures ok <-> (|src| % 2 = 0 And Forall k in [0, |src|) : digit(src[k]))
func Pairs(dst, src []byte) (ok bool) {
	i, j := 0, 0
	// @Invariant 0 <= i And j = 2 * i And j <= |src|
	// @Invariant Forall k in [0, j) : digit(src[k])
	// @Variant |src| - j
	for ; j < len(src)-1; j += 2 {
		a, b := src[j], src[j+1]
		if a < '0' || a > '9' {
			return false
		}
		if b < '0' || b > '9' {
			return false // want `postcondition may not hold: ok <-> \(\|src\| % 2 = 0 And Forall k in \[0, \|src\|\) : digit\(src\[k\]\)\)`
		}
		dst[i] = (a-'0')*10 + (b - '0')
		i++
	}
	if len(src)%2 == 1 {
		return false
	}
	return true
}

// @Requires |src| / 2 <= |dst|
// @Modifies dst
// @Ensures ok <-> (|src| % 2 = 0 And Forall k in [0, |src|) : digit(src[k]))
func PairsAsserted(dst, src []byte) (ok bool) {
	i, j := 0, 0
	// @Invariant 0 <= i And j = 2 * i And j <= |src|
	// @Invariant Forall k in [0, j) : digit(src[k])
	// @Variant |src| - j
	for ; j < len(src)-1; j += 2 {
		a, b := src[j], src[j+1]
		if a < '0' || a > '9' {
			return false
		}
		if b < '0' || b > '9' {
			// @Assert ~(Forall k in [0, |src|) : digit(src[k]))
			return false
		}
		dst[i] = (a-'0')*10 + (b - '0')
		i++
	}
	if len(src)%2 == 1 {
		return false
	}
	return true
}
