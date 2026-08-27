package structured

import stdtesting "testing"

func TestNested(t *stdtesting.T) {
	t.Run("scenario", func(t *stdtesting.T) {})
}

func delegatedSubtest(t *stdtesting.T) {
	Subject()
}

type callbackSuite struct{}

func (callbackSuite) delegated(t *stdtesting.T) {
	Subject()
}

type unrelatedRunner struct{}

func (unrelatedRunner) Run(name string, callback func(*stdtesting.T)) {
	callback(nil)
}

func TestCallbacks(t *stdtesting.T) {
	t.Run("inline", func(t *stdtesting.T) {
		t.Run("nested", func(t *stdtesting.T) {
			Subject()
		})
	})
	t.Run("named", delegatedSubtest) // want `testing\.T\.Run callback must be an inline function literal; move the subtest body into the Run call`

	callback := func(t *stdtesting.T) {
		Subject()
	}
	t.Run("variable", callback) // want `testing\.T\.Run callback must be an inline function literal; move the subtest body into the Run call`

	var callbacks callbackSuite
	t.Run("method", callbacks.delegated) // want `testing\.T\.Run callback must be an inline function literal; move the subtest body into the Run call`

	var unrelated unrelatedRunner
	unrelated.Run("unrelated", delegatedSubtest)
}

func TestTable(t *stdtesting.T) {
	cases := []struct {
		name string
	}{
		{name: "first"},
		{name: "second"},
	}
	for range cases {
	}
}

func TestFlat(t *stdtesting.T) {
	Subject()
}

func TestExampleSuccess(t *stdtesting.T) /* want `tests TestExampleSuccess and TestExampleFailure share prefix TestExample; consolidate scenarios into one test using a table or t\.Run subtests` */ {
	t.Run("success", func(t *stdtesting.T) {
		Subject()
	})
}

func TestExampleFailure(t *stdtesting.T) {
	cases := []int{1, 2}
	for range cases {
		Subject()
	}
}

func TestParser_valid(t *stdtesting.T) /* want `tests TestParser_valid and TestParser_invalid share prefix TestParser; consolidate scenarios into one test using a table or t\.Run subtests` */ {
	Subject()
}

func TestParser_invalid(t *stdtesting.T) {
	Subject()
}

func TestAlphaFirst(t *stdtesting.T) /* want `tests TestAlphaFirst, TestAlphaSecond, and TestAlphaThird share prefix TestAlpha; consolidate scenarios into one test using a table or t\.Run subtests` */ {
	Subject()
}

func TestAlphaSecond(t *stdtesting.T) {
	Subject()
}

func TestAlphaThird(t *stdtesting.T) {
	Subject()
}

func testHelper(t *stdtesting.T) {
	Subject()
}

func BenchmarkFlat(b *stdtesting.B) {
	Subject()
}

func FuzzFlat(f *stdtesting.F) {
	f.Fuzz(func(t *stdtesting.T, value int) {})
}

func TestMain(m *stdtesting.M) {
	m.Run()
}

type suite struct{}

func (suite) TestMethod(t *stdtesting.T) {
	Subject()
}
