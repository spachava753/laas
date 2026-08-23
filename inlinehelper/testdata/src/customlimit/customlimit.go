package customlimit

func one() int /* want `function one has 1 statement and is called once; consider inlining it at its call site` */ {
	return 1
}

func two(value int) int {
	value++
	return value
}

func Use() {
	_ = one()
	_ = two(1)
}
