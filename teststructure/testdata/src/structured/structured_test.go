package structured

import stdtesting "testing"

func TestNested(t *stdtesting.T) {
	t.Run("scenario", func(t *stdtesting.T) {})
}

func TestRenamedParameter(test *stdtesting.T) {
	test.Run("scenario", func(t *stdtesting.T) {})
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

func TestDeclaredTable(t *stdtesting.T) {
	var cases = map[string]int{
		"first":  1,
		"second": 2,
	}
	for range cases {
	}
}

func TestDirectTable(t *stdtesting.T) {
	for range [...]int{1, 2} {
	}
}

func TestFlat(t *stdtesting.T) /* want `test TestFlat should use t\.Run subtests or range over a local table of test cases` */ {
	Subject()
}

func TestExampleSuccess(t *stdtesting.T) /* want `test TestExampleSuccess should use t\.Run subtests or range over a local table of test cases` */ {
	Subject()
}

func TestExampleFailure(t *stdtesting.T) /* want `test TestExampleFailure should use t\.Run subtests or range over a local table of test cases` */ {
	Subject()
}

type runner struct{}

func (runner) Run(name string, test func()) {
	test()
}

func TestUnrelatedRun(t *stdtesting.T) /* want `test TestUnrelatedRun should use t\.Run subtests or range over a local table of test cases` */ {
	var other runner
	other.Run("scenario", func() {})
}

func Testhelper(t *stdtesting.T) {
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
