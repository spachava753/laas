package singleuse

import "errors"

func one() int /* want `function one has 1 statement and is called once; consider inlining it at its call site` */ {
	return 1
}

func two(value int) int /* want `function two has 2 statements and is called once; consider inlining it at its call site` */ {
	value++
	return value
}

func checked() error /* want `function checked has 4 statements and is called once; consider inlining it at its call site` */ {
	if err := errors.New("failure"); err != nil {
		return err
	}
	return nil
}

func large(value int) int {
	value++
	value++
	value++
	value++
	return value
}

func repeated() int {
	return 1
}

func unused() int {
	return 1
}

func asValue() int {
	return 1
}

func recurse(value int) int {
	if value == 0 {
		return 0
	}
	return recurse(value - 1)
}

type worker struct{}

func (worker) value() int /* want `method value has 1 statement and is called once; consider inlining it at its call site` */ {
	return 1
}

func identity[T any](value T) T /* want `function identity has 1 statement and is called once; consider inlining it at its call site` */ {
	return value
}

func withClosure() func() int {
	return func() int {
		value := 1
		value++
		value++
		return value
	}
}

func Use() {
	_ = one()
	_ = two(1)
	_ = checked()
	_ = large(1)
	_ = repeated()
	_ = repeated()
	callback := asValue
	_ = callback()
	var item worker
	_ = item.value()
	_ = identity(1)
	_ = withClosure()
}
