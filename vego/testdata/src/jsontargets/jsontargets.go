// Package jsontargets decodes JSON into a field, a slice variable, and a
// map variable, through the pointers steps 1 and 2 of F42 made possible.
package jsontargets

import "encoding/json"

// Config holds items.
type Config struct {
	Items []string
	N     int
}

// IntoField decodes into a field, which it first sets to nil, so that the
// decoder makes every slice it stores.
//
// @Requires c != nil And |data| < 1000
// @Modifies c
// @Ensures c.N' = c.N
func IntoField(c *Config, data []byte) (err error) {
	c.Items = nil
	return json.Unmarshal(data, &c.Items)
}

// IntoSlice decodes into a slice variable.
//
// @Requires |data| < 1000
// @Ensures True
func IntoSlice(data []byte) (xs []string, err error) {
	err = json.Unmarshal(data, &xs)
	return xs, err
}

// IntoMap decodes into a map variable.
//
// @Requires |data| < 1000
// @Ensures True
func IntoMap(data []byte) (m map[string]int, err error) {
	err = json.Unmarshal(data, &m)
	return m, err
}

// IntoHeld decodes into a field that may hold a slice of the caller's,
// whose array the decoder would append into.
//
// @Requires c != nil And |data| < 1000
// @Modifies c
// @Ensures True
func IntoHeld(c *Config, data []byte) (err error) {
	return json.Unmarshal(data, &c.Items) // want `vego: Unmarshal may decode into memory that c.Items refers to, which the caller may hold`
}
