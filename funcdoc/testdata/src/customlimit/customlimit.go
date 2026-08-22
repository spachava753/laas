package customlimit

func undocumented(value int) /* want `function undocumented has cyclomatic complexity 3 \(limit 2\); add a leading comment starting with "undocumented" that explains its logic` */ {
	if value > 0 {
	}
	if value > 1 {
	}
}

type worker struct{}

func (worker) run(value int) /* want `method run has cyclomatic complexity 3 \(limit 2\); add a leading comment starting with "run" that explains its logic` */ {
	if value > 0 {
	}
	if value > 1 {
	}
}

func documented(value int) {
	// documented rejects negative values, then handles values that need special processing.
	if value > 0 {
	}
	if value > 1 {
	}
}

// apiDocumented is documented for callers but lacks an implementation overview.
func apiDocumented(value int) /* want `function apiDocumented has cyclomatic complexity 3 \(limit 2\); add a leading comment starting with "apiDocumented" that explains its logic` */ {
	if value > 0 {
	}
	if value > 1 {
	}
}

func lateComment(value int) /* want `function lateComment has cyclomatic complexity 3 \(limit 2\); add a leading comment starting with "lateComment" that explains its logic` */ {
	if value > 0 {
	}
	// Handle the remaining special case.
	if value > 1 {
	}
}

func misnamedComment(value int) {
	// Explain the two special cases. // want `function misnamedComment has cyclomatic complexity 3 \(limit 2\); its leading comment should start with "misnamedComment"`
	if value > 0 {
	}
	if value > 1 {
	}
}

func (worker) commentedRun(value int) {
	// Run the two special cases. // want `method commentedRun has cyclomatic complexity 3 \(limit 2\); its leading comment should start with "commentedRun"`
	if value > 0 {
	}
	if value > 1 {
	}
}
