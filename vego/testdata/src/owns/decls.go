package owns

// Exported owns a field that other packages could assign.
//
// @Owns Items // want `vego: Items cannot be owned: it is exported, and a field can be owned only when it is unexported, so that only package owns can change what it refers to; unexport it, or leave it unowned`
type Exported struct {
	Items []int
}

// Counted owns a number.
//
// @Owns n // want `vego: n cannot be owned: it holds an int, and a field can be owned when it holds a pointer to a struct, a slice, a map, or an interface value`
type Counted struct {
	n int
}

// Absent names a field it does not have.
//
// @Owns itms // want `vego: Absent has no field itms to own`
type Absent struct {
	items []int
}

// Twice names one field twice.
//
// @Owns items, items // want `vego: items is owned twice`
type Twice struct {
	items []int
}

// Generic has a type parameter.
//
// @Owns items // want `vego: an Owns can only be declared on a struct type without type parameters`
type Generic[T any] struct {
	items []T
}

// Node would own itself through next.
//
// @Owns next // want `vego: Node cannot own next: next points to a Node, so a Node would own itself; a linked structure cannot be declared with Owns; leave next unowned`
type Node struct {
	next *Node
}

// Edge and Vertex own each other.
//
// @Owns to // want `vego: Edge would own itself: Edge owns Vertex through to, and Vertex owns Edge through from; a linked structure cannot be declared with Owns; leave one of these fields unowned`
type Edge struct {
	to *Vertex
}

// Vertex is the other half. Once Edge is refused, Vertex owns an Edge
// that owns nothing, which is no cycle.
//
// @Owns from
type Vertex struct {
	from *Edge
}

// @Owns items // want `vego: an Owns annotation belongs in the doc comment of a struct type`
//
// @Ensures True
func Misplaced() {}
