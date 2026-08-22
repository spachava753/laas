package customlimit

func undocumented(value int) /* want `function undocumented has cyclomatic complexity 3 \(limit 2\); add a leading comment explaining its logic` */ {
	if value > 0 {
	}
	if value > 1 {
	}
}

type worker struct{}

func (worker) run(value int) /* want `method run has cyclomatic complexity 3 \(limit 2\); add a leading comment explaining its logic` */ {
	if value > 0 {
	}
	if value > 1 {
	}
}

func documented(value int) {
	// Reject negative values, then handle values that need special processing.
	if value > 0 {
	}
	if value > 1 {
	}
}

// apiDocumented is documented for callers but lacks an implementation overview.
func apiDocumented(value int) /* want `function apiDocumented has cyclomatic complexity 3 \(limit 2\); add a leading comment explaining its logic` */ {
	if value > 0 {
	}
	if value > 1 {
	}
}

func lateComment(value int) /* want `function lateComment has cyclomatic complexity 3 \(limit 2\); add a leading comment explaining its logic` */ {
	if value > 0 {
	}
	// Handle the remaining special case.
	if value > 1 {
	}
}
