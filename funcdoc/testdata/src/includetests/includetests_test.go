package includetests

func testHelper(value int) /* want `function testHelper has cyclomatic complexity 3 \(limit 2\); add a doc comment immediately above it starting with "testHelper" that explains its logic` */ {
	if value > 0 {
	}
	if value > 1 {
	}
}
