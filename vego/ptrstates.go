package vego

import (
	"fmt"
	"go/types"
	"math/big"
	"slices"

	"github.com/spachava753/laas/vego/internal/logic"
)

// States of pointers (S0b of F34).
//
// A state that an interface declares, such as closed of io.Closer, is about
// what an interface value holds. When that is a pointer, the state is about
// the object the pointer points to: every interface value that holds the
// pointer has it, and a call of a method on the pointer, statically or
// through any of them, changes it. So the states of an interface value that
// holds a pointer lie at the key of the pointer (pkey), and every interface
// value made from it has that key (skey(held) = pkey(p)).
//
// The key of a pointer to the start of an allocation is the allocation
// itself, so that the states of a new object are new, and those of an
// object that existed on entry are a row that existed on entry, with no
// fact needed. The key of a pointer inside an allocation is read from a
// table that nothing writes, at the allocation and the position, with the
// fact that it existed on entry exactly when the allocation did. A nil
// pointer has the key 0.
//
// A pointer has states when its type implements an interface with
// declared states that the package can name: one declared in the package
// or in a package it is built with, in source, in the trust file, or in
// the shipped files. A state the package cannot name, it cannot read.
//
// Who changes the states: a call whose frame covers the struct the pointer
// points to forgets the row of its key (A5), and a method that implements
// a method whose contract lists its receiver must list its receiver too,
// which every conversion checks, so that a static call of it in any package
// covers the struct. Ghost states, of a type whose methods that change them
// are verified code, start False where the struct is allocated, by their
// definition: they are what calls of those methods on the object did.
// States declared by an entry for a type whose method is trusted are facts
// about what the method acts on, which verified code cannot see, so they
// are known only from a contract: an allocation of such a type has states
// that nothing says (F10 of the design review).

// pkeys is the table of the keys of pointers inside an allocation.
var pkeys = logic.Const("pointer key", logic.SeqOf(logic.SeqOf(logic.Ref)))

// pkey returns the key of the states of a pointer.
func pkey(ptr value) *logic.Term {
	alloc, pos := ptr[0], ptr[1]
	if pos.Op == logic.OpIntLit && pos.Val == 0 {
		// Where the nil pointer is, its key is 0 too.
		return alloc
	}
	// The cases, a nil pointer and one to the start of an allocation, are
	// facts that notePointerKey states where the key is read, rather than
	// a choice inside every term that reads it.
	return logic.Select(logic.Select(pkeys, alloc), pos)
}

// notePointerKey states what is known of the key of a pointer: that two
// pointers the function keys are apart have keys of their own, since a
// state is about one object; and, for a pointer inside an allocation, that
// its key existed on entry exactly when the allocation did.
func (v *fnVerifier) notePointerKey(sink *state, ptr value) {
	if sink == nil || hasBound(ptr[0]) || hasBound(ptr[1]) {
		return
	}
	if note := "keyed " + ptr[0].String() + " " + ptr[1].String(); !sink.noted[note] {
		sink.noted[note] = true
		for _, other := range v.keyedPointers {
			same := logic.And(logic.Eq(ptr[0], other[0]), logic.Or(logic.Eq(ptr[0], logic.RefLit(0)), logic.Eq(ptr[1], other[1])))
			sink.assume(logic.Implies(logic.Not(same), logic.Ne(pkey(ptr), pkey(other))))
		}
		v.keyedPointers = append(v.keyedPointers, ptr)
	}
	if ptr[1].Op == logic.OpIntLit && ptr[1].Val == 0 {
		return
	}
	inside := pkey(ptr)
	zero := logic.RefLit(0)
	existed := logic.Lt(ptr[0], v.entryBrk)
	// The key of an object that exists exists too, as its allocation
	// does: below the bound where it is read, so that memory a later call
	// creates is not it (O1 of the checkpoint of S0b of F34). Every fact
	// about the states of what a pointer points to comes from a read of
	// its key, which states this with the bound of that moment, and every
	// later call creates memory above it.
	exists := logic.Implies(logic.And(logic.Ne(ptr[0], zero), logic.Lt(ptr[0], sink.brk)),
		logic.And(logic.Lt(logic.IntLit(0), inside), logic.Lt(inside, sink.brk)))
	fact := logic.And(
		logic.Implies(logic.Eq(ptr[0], zero), logic.Eq(inside, zero)),
		logic.Implies(logic.And(logic.Ne(ptr[0], zero), logic.Eq(ptr[1], logic.IntLit(0))), logic.Eq(inside, ptr[0])),
		logic.Implies(logic.And(logic.Ne(ptr[0], zero), existed), logic.And(logic.Lt(logic.IntLit(0), inside), logic.Lt(inside, v.entryBrk))),
		logic.Implies(logic.Not(existed), logic.Le(v.entryBrk, inside)),
		exists)
	if note := "pointer key " + fact.String(); !sink.noted[note] {
		sink.noted[note] = true
		sink.assume(fact)
	}
}

// stateInterfaces returns the interface types with declared states that
// the package can name: those of the package and of every package it is
// built with.
func (pv *pkgVerifier) stateInterfaces() []*types.TypeName {
	if pv.stateIfaces != nil {
		return *pv.stateIfaces
	}
	var found []*types.TypeName
	seen := map[*types.Package]bool{}
	var walk func(pkg *types.Package)
	walk = func(pkg *types.Package) {
		if pkg == nil || seen[pkg] {
			return
		}
		seen[pkg] = true
		for _, name := range pkg.Scope().Names() {
			owner, ok := pkg.Scope().Lookup(name).(*types.TypeName)
			if !ok || owner.IsAlias() || !types.IsInterface(owner.Type()) || !declaresMethod(owner) {
				continue
			}
			if pv.mayDeclareStates(owner) {
				found = append(found, owner)
				// A struct's cells are told apart from the states of an
				// object at the same row by position: no cell of memory lies
				// above twice MaxAlloc, and every state does.
				for _, s := range pv.declaredStates(owner) {
					if s.position().Value().Cmp(new(big.Int).Lsh(pv.maxAlloc(), 1)) <= 0 {
						panic("internal error: the position of the state " + s.title() + " lies within memory")
					}
				}
			}
		}
		for _, imported := range pkg.Imports() {
			walk(imported)
		}
	}
	walk(pv.pass.Pkg)
	pv.stateIfaces = &found
	return found
}

// mayDeclareStates reports whether an interface type has a declaration of
// states, without recording a use of it: in the package, as a fact of its
// package, or in a trust file.
func (pv *pkgVerifier) mayDeclareStates(owner *types.TypeName) bool {
	if owner.Pkg() == pv.pass.Pkg {
		return len(pv.ownStates[owner]) > 0
	}
	if fact := (&stateFact{}); pv.pass.ImportObjectFact != nil && pv.pass.ImportObjectFact(owner, fact) {
		return len(fact.Names) > 0
	}
	key := stateKey(owner.Pkg().Path(), owner.Name())
	for _, shipped := range shippedContracts() {
		if len(shipped.states[key]) > 0 {
			return true
		}
	}
	return pv.projectTrust != nil && len(pv.projectTrust.states[key]) > 0
}

// pointerStateOwners returns the interfaces with states that a pointer
// type implements, or nil for any other type.
func (pv *pkgVerifier) pointerStateOwners(t types.Type) []*types.TypeName {
	pointer, isPointer := t.Underlying().(*types.Pointer)
	if !isPointer || types.IsInterface(t) {
		return nil
	}
	// Cached by what it points to, for an unnamed pointer type: a named
	// type is one object.
	if _, named := t.(*types.Named); named {
		return pv.pointerStateOwnersOf(t)
	}
	if owners, done := pv.pointerOwners[pointer.Elem()]; done {
		return owners
	}
	if pv.pointerOwners == nil {
		pv.pointerOwners = map[types.Type][]*types.TypeName{}
	}
	owners := pv.pointerStateOwnersOf(t)
	pv.pointerOwners[pointer.Elem()] = owners
	return owners
}

// pointerStateOwnersOf computes pointerStateOwners.
func (pv *pkgVerifier) pointerStateOwnersOf(t types.Type) []*types.TypeName {
	var owners []*types.TypeName
	for _, owner := range pv.stateInterfaces() {
		if types.Implements(t, owner.Type().Underlying().(*types.Interface)) && len(pv.declaredStates(owner)) > 0 {
			owners = append(owners, owner)
		}
	}
	return owners
}

// pointerStates returns the states of what a pointer of type t points to.
func (pv *pkgVerifier) pointerStates(t types.Type) []ifaceState {
	var states []ifaceState
	for _, owner := range pv.pointerStateOwners(t) {
		states = append(states, pv.declaredStates(owner)...)
	}
	return states
}

// stateChangers returns the methods of a pointer type that implement a
// method of an interface with states whose contract lists its receiver,
// which change the states of the object.
func (pv *pkgVerifier) stateChangers(t types.Type) []*types.Func {
	var changers []*types.Func
	for _, owner := range pv.pointerStateOwners(t) {
		for method := range owner.Type().Underlying().(*types.Interface).Methods() {
			fn := pv.methodContract(method)
			if fn == nil || fn.receiver == nil || !slices.ContainsFunc(fn.modifies, func(m *modTarget) bool { return m.name == fn.receiver.Name() }) {
				continue
			}
			if selection := types.NewMethodSet(t).Lookup(method.Pkg(), method.Name()); selection != nil {
				if concrete, ok := selection.Obj().(*types.Func); ok && !slices.Contains(changers, concrete) {
					changers = append(changers, concrete)
				}
			}
		}
	}
	return changers
}

// pointerReceiverChanger reports whether one of the methods of a pointer
// type that change states has a pointer receiver, so that the states would
// be those of the object it points to. When none has, each conversion has
// states of its own, as a value does (checkStateChangers).
func (pv *pkgVerifier) pointerReceiverChanger(t types.Type) bool {
	return slices.ContainsFunc(pv.stateChangers(t), func(method *types.Func) bool {
		_, pointer := method.Type().(*types.Signature).Recv().Type().(*types.Pointer)
		return pointer
	})
}

// pointerKeyed reports whether a pointer type has states, those of the
// object it points to: one of its methods that change them has a pointer
// receiver, and the model can keep them (pointerStatesWhy). It is the one
// predicate wherever the states of a pointer are read, written, or assumed
// (F12 of the review of S0b).
func (pv *pkgVerifier) pointerKeyed(t types.Type) bool {
	return pv.pointerReceiverChanger(t) && pv.pointerStatesWhy(t) == ""
}

// pointerStatesWhy says why the states of what a pointer of type t points
// to cannot be kept, for a type whose method that changes them has a
// pointer receiver, or returns "": every such method must have a pointer
// receiver and list it in Modifies, so that a call of it in any package
// covers the struct and forgets the states; the object must not have size
// zero, since two pointers to one may or may not be one; and it must not
// start with a field whose type has states of its own, at the same address.
func (pv *pkgVerifier) pointerStatesWhy(t types.Type) string {
	shown := func(t types.Type) string { return types.TypeString(t, types.RelativeTo(pv.pass.Pkg)) }
	object, isPointer := pointee(t)
	if !isPointer {
		return ""
	}
	if pv.pass.TypesSizes.Sizeof(object) == 0 {
		return "it points to a value of size zero, and two such pointers may or may not be one, so nothing tells their states apart"
	}
	if inner := pv.sharesAddress(t); inner != nil {
		return fmt.Sprintf("its first field holds %s %s, whose states are its own and lie at the same address, so nothing tells the states of the two apart; put another field first",
			article(shown(inner)), shown(inner))
	}
	for _, method := range pv.stateChangers(t) {
		recv := method.Type().(*types.Signature).Recv()
		title := methodOf(recv.Type(), method, pv.pass.Pkg)
		if _, pointer := recv.Type().(*types.Pointer); !pointer {
			return fmt.Sprintf("%s changes its states and has a value receiver, so a call of it would not be known to change the states of what the pointer points to; give it a pointer receiver", title)
		}
		fn := pv.contractOf(method)
		if fn == nil {
			return fmt.Sprintf("%s changes its states and has no contract", title)
		}
		if !slices.ContainsFunc(fn.modifies, func(m *modTarget) bool { return m.name == recv.Name() && len(m.steps) == 0 }) {
			return fmt.Sprintf("%s changes its states, and its contract does not list its receiver %s in Modifies, so a call of it would not be known to change them; list %s in its Modifies",
				title, recv.Name(), recv.Name())
		}
	}
	return ""
}

// sharesAddress returns a type with states of its own that lies at the
// start of what a pointer of type t points to, a first field at any depth,
// or nil. A pointer to it is the same pointer as one of t, so the key of
// their states would be one, while they are two objects.
func (pv *pkgVerifier) sharesAddress(t types.Type) types.Type {
	object, isPointer := pointee(t)
	if !isPointer {
		return nil
	}
	for {
		u, isStruct := object.Underlying().(*types.Struct)
		if !isStruct || u.NumFields() == 0 {
			return nil
		}
		first := u.Field(0).Type()
		if _, isInner := first.Underlying().(*types.Struct); !isInner {
			return nil
		}
		if pv.pointerKeyed(types.NewPointer(first)) {
			return first
		}
		object = first
	}
}

// ghostPointer reports whether the states of what a pointer of type t
// points to are ghost: every method that changes them is verified code of
// the project, so that they are what calls of those methods did.
func (pv *pkgVerifier) ghostPointer(t types.Type) bool {
	for _, method := range pv.stateChangers(t) {
		if fn := pv.contractOf(method); fn == nil || fn.trust != nil {
			return false
		}
	}
	return true
}

// pointerStatesTarget returns, for a target that is one struct value a
// pointer of a type with states points to, the target of the row of its
// states, and whether there is one: a call whose frame covers the struct
// changes them (A5).
func (pv *pkgVerifier) pointerStatesTarget(t target) (target, bool) {
	if !t.single || t.base == nil || t.fp || t.row || !pv.pointerKeyed(types.NewPointer(t.base.t)) {
		return target{}, false
	}
	states := t
	states.single, states.base, states.lo, states.hi, states.owned, states.also = false, nil, nil, nil, nil, nil
	states.cells, states.row, states.ref, states.besideStruct = []cell{stateCell}, true, pkey(value{t.base.ref, t.base.at}), true
	return states, true
}

// newPointerStates gives a struct the function allocates, whose pointer
// has states, a key of its own: the allocation, which is new. Ghost states
// start False there; states that an entry declares for a type whose method
// is trusted are left unknown (F10 of the design review).
func (v *fnVerifier) newPointerStates(st *state, t types.Type, ptr value) {
	pointer := types.NewPointer(t)
	states := v.pointerStates(pointer)
	if len(states) == 0 || !v.pointerKeyed(pointer) || !v.ghostPointer(pointer) {
		return
	}
	row := v.fresh("states", logic.BoolSeq)
	for _, s := range states {
		st.assume(logic.Not(logic.Select(row, s.position())))
	}
	st.storeRow(stateRegion, logic.Bool, ptr[0], row)
}
