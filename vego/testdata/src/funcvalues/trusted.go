package funcvalues

// A function value that a trusted function hands back is code that its
// author may not have seen. Verified code calls it only when the entry
// vouches for it, and no entry can yet claim anything of a value that the
// function writes into memory.

func loadMapper() (m Mapper)        { return nil }
func loadMapperVouched() (m Mapper) { return nil }

// Chain links mappers.
type Chain struct {
	next *Link
}

type Link struct {
	f Mapper
}

func (c *Chain) grow() {}

// UsesLoaded calls a mapper a trusted function returned without vouching
// for it.
//
// @Ensures True
func UsesLoaded() (y int) {
	m := loadMapper() // want `vego: the trusted contract of funcvalues.loadMapper \(trusted.yaml:\d+\) cannot be used: its result m can hold a function value or an interface value of a type with a contract; list it under vouches to claim that every such value meets the contract of its type`
	return m(1)
}

// UsesVouched calls a mapper whose entry vouches for it.
//
// @Ensures 0 <= y <= 2000
func UsesVouched() (y int) {
	m := loadMapperVouched()
	return m(1)
}

// Grows lets a trusted function change a chain whose links hold mappers.
//
// @Requires c != nil
// @Modifies c
// @Ensures True
func Grows(c *Chain) {
	c.grow() // want `vego: the trusted contract of \(\*funcvalues.Chain\).grow \(trusted.yaml:\d+\) cannot be used: its modifies "c" covers memory that can hold a function value or an interface value of a type with a contract; list c under vouches to claim that every such value the function writes there meets the contract of its type`
}

func loadUnnamed() Mapper { return nil }

// UsesUnnamed calls a mapper from an unnamed result that the entry does not
// vouch for. The message names the result as the entry spells it.
//
// @Ensures True
func UsesUnnamed() (y int) {
	m := loadUnnamed() // want `vego: the trusted contract of funcvalues.loadUnnamed \(trusted.yaml:\d+\) cannot be used: its result result can hold a function value`
	return m(1)
}
