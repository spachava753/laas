package defaultlimit

func atLimit(values []int, input <-chan int, left, right, ready bool) {
	if left && right || ready {
	}
	for false {
	}
	for range values {
	}
	switch {
	case left:
	case right:
	default:
	}
	select {
	case <-input:
	case <-input:
	default:
	}
}

func aboveLimit(values []int, input <-chan int, left, right, ready bool) /* want `function aboveLimit has cyclomatic complexity 11 \(limit 10\); add a leading comment starting with "aboveLimit" that explains its logic` */ {
	if left && right || ready {
	}
	for false {
	}
	for range values {
	}
	switch {
	case left:
	case right:
	default:
	}
	select {
	case <-input:
	case <-input:
	default:
	}
	if ready {
	}
}
