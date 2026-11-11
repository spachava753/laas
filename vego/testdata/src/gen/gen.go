// Package gen calls a method of whatever type it is instantiated with.
package gen

// Call runs the Ready method of the zero value of T.
func Call[T interface{ Ready() bool }]() bool {
	var t T
	return t.Ready()
}
