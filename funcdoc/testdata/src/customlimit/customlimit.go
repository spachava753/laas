package customlimit

func undocumented(value int) /* want `function undocumented has cyclomatic complexity 3 \(limit 2\); add a doc comment immediately above it starting with "undocumented" that explains its logic` */ {
	if value > 0 {
	}
	if value > 1 {
	}
}

type worker struct{}

func (worker) run(value int) /* want `method run has cyclomatic complexity 3 \(limit 2\); add a doc comment immediately above it starting with "run" that explains its logic` */ {
	if value > 0 {
	}
	if value > 1 {
	}
}

// documented rejects negative values, then handles values that need special processing.
func documented(value int) {
	if value > 0 {
	}
	if value > 1 {
	}
}

// apiDocumented checks the first threshold before handling the second.
func apiDocumented(value int) {
	if value > 0 {
	}
	if value > 1 {
	}
}

func bodyComment(value int) /* want `function bodyComment has cyclomatic complexity 3 \(limit 2\); add a doc comment immediately above it starting with "bodyComment" that explains its logic` */ {
	// bodyComment handles two special cases.
	if value > 0 {
	}
	if value > 1 {
	}
}

// Explain the two special cases. // want `function misnamedComment has cyclomatic complexity 3 \(limit 2\); its doc comment should start with "misnamedComment"`
func misnamedComment(value int) {
	if value > 0 {
	}
	if value > 1 {
	}
}

// Run the two special cases. // want `method commentedRun has cyclomatic complexity 3 \(limit 2\); its doc comment should start with "commentedRun"`
func (worker) commentedRun(value int) {
	if value > 0 {
	}
	if value > 1 {
	}
}

// detachedComment handles two special cases.

func detachedComment(value int) /* want `function detachedComment has cyclomatic complexity 3 \(limit 2\); add a doc comment immediately above it starting with "detachedComment" that explains its logic` */ {
	if value > 0 {
	}
	if value > 1 {
	}
}
