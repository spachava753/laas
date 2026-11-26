package vego

import (
	"bufio"
	"fmt"
	"maps"
	"os"
	"path/filepath"
	"regexp"
	"slices"
	"strings"
	"testing"

	"github.com/spachava753/laas/vego/internal/solver"
	"golang.org/x/tools/go/analysis"
	"golang.org/x/tools/go/analysis/checker"
	"golang.org/x/tools/go/packages"
)

var wantPattern = regexp.MustCompile("`([^`]*)`")

// runCorpus analyses packages under testdata/src and compares the
// diagnostics with the expectations in their sources. A line expects the
// diagnostics listed after "// want", each as a regular expression between
// backquotes; every diagnostic must be expected and every expectation met.
//
// This is the contract of analysistest.Run, which is not used here because
// it would also demand an expectation for every fact, and the analyzer
// exports one for each verified function.
func runCorpus(t *testing.T, analyzer *analysis.Analyzer, patterns ...string) *checker.Graph {
	t.Helper()
	defer heavy()()
	testdata, err := filepath.Abs("testdata")
	if err != nil {
		t.Fatal(err)
	}
	config := &packages.Config{
		Mode: packages.LoadAllSyntax,
		Dir:  filepath.Join(testdata, "src"),
		Env:  append(os.Environ(), "GOPATH="+testdata, "GO111MODULE=off", "GOPROXY=off", "GOWORK=off"),
	}
	loaded, err := packages.Load(config, patterns...)
	if err != nil {
		t.Fatalf("load packages: %v", err)
	}
	if packages.PrintErrors(loaded) > 0 {
		t.Fatal("the test packages do not compile")
	}
	graph, err := checker.Analyze([]*analysis.Analyzer{analyzer}, loaded, nil)
	if err != nil {
		t.Fatalf("analyze: %v", err)
	}
	type place struct {
		file string
		line int
	}
	wants := map[place][]*regexp.Regexp{}
	shown := func(file string) string {
		if rel, err := filepath.Rel(config.Dir, file); err == nil {
			return rel
		}
		return file
	}
	for _, action := range graph.Roots {
		if action.Err != nil {
			t.Fatalf("analysis of %s failed: %v", action.Package.PkgPath, action.Err)
		}
		for _, file := range action.Package.CompiledGoFiles {
			source, err := os.Open(file)
			if err != nil {
				t.Fatal(err)
			}
			lines := bufio.NewScanner(source)
			lines.Buffer(nil, 1<<20)
			for number := 1; lines.Scan(); number++ {
				_, expectations, found := strings.Cut(lines.Text(), "// want ")
				if !found {
					continue
				}
				for _, match := range wantPattern.FindAllStringSubmatch(expectations, -1) {
					wants[place{file, number}] = append(wants[place{file, number}], regexp.MustCompile(match[1]))
				}
			}
			source.Close()
		}
	}
	scanned := map[string]bool{}
	for _, action := range graph.Roots {
		for _, file := range action.Package.CompiledGoFiles {
			scanned[file] = true
		}
	}
	for _, action := range graph.Roots {
		for _, diagnostic := range action.Diagnostics {
			position := action.Package.Fset.Position(diagnostic.Pos)
			// A diagnostic may point into a trust file, which states its
			// expectations in the same way inside a YAML comment.
			if !scanned[position.Filename] {
				scanned[position.Filename] = true
				content, _ := os.ReadFile(position.Filename)
				for number, line := range strings.Split(string(content), "\n") {
					if _, expectations, found := strings.Cut(line, "// want "); found {
						for _, match := range wantPattern.FindAllStringSubmatch(expectations, -1) {
							at := place{position.Filename, number + 1}
							wants[at] = append(wants[at], regexp.MustCompile(match[1]))
						}
					}
				}
			}
			at := place{position.Filename, position.Line}
			index := slices.IndexFunc(wants[at], func(want *regexp.Regexp) bool { return want.MatchString(diagnostic.Message) })
			if index < 0 {
				t.Errorf("%s:%d:%d: unexpected diagnostic: %s", shown(position.Filename), position.Line, position.Column, diagnostic.Message)
				continue
			}
			wants[at] = slices.Delete(wants[at], index, index+1)
		}
	}
	var missing []string
	for at, remaining := range wants {
		for _, want := range remaining {
			missing = append(missing, fmt.Sprintf("%s:%d: no diagnostic was reported matching `%s`", shown(at.file), at.line, want))
		}
	}
	slices.Sort(missing)
	for _, message := range missing {
		t.Error(message)
	}
	return graph
}

// mainCorpus is the packages of the main corpus run of TestAnalyzer.
var mainCorpus = []string{
	"paper", "algorithms", "defects", "variadic", "formatting", "rejected", "leetcode", "semantics", "effects", "ordering", "integers", "values", "trust",
	"lib", "client", "memory", "shapes", "badshapes", "invariants", "mapping", "badpred", "usesbadpred", "early", "settled", "gen", "earlytype", "earlyrange", "earlybox", "earlyloop", "earlycarrier", "earlypanic", "guide", "wrapped", "unread", "usesunread", "twovariants", "usestwovariants", "lonecr", "errorsid", "errorsvars", "errorsvarsclient", "vouched", "vouchedclient", "vouchedcapture", "earlyalias", "earlyaliasok", "sentinellib", "sentinelclient", "usesearly", "sentinelfar", "sentinelfarther", "closures", "funcvalues", "funcvalueslib", "funcvaluesclient", "funcvaluesunread", "funcvaluesinit", "funcvaluesinitdefer", "funcvaluesinitok", "funcvaluesinitmethod", "funcvaluesoldloop", "funcvaluesinitlit", "callbacks", "callbacksinit", "interfaces", "interfaceslib", "interfacesunread", "interfacesinitok", "interfacesinithand", "interfacesinitcall", "foreign", "stdtypes", "locks", "lockspred", "lockslib", "locksclient", "layers", "ifacestate", "footprints", "buffers", "distinct", "ensuresentry", "manywrites", "slowresp", "slowhttp", "deepfacts",
	"globals", "globalslib", "globalsclient", "globalsembed", "globalsearly", "unsafelib", "unsafeuse", "keeps", "keepslib", "plog", "buffered", "iowrap", "globalsleak", "globalsleakclient", "trialfaults", "smalls", "vouchsrc", "vouchsrcclient", "vouchsrcbad", "stdentries", "originpath", "originpathclient", "generics", "genericslib", "deletes", "cycles/...", "owns", "ownslib", "ownstore", "ownserver", "frames", "guidestore", "handlers", "ghost", "jsonenc", "jsondec",
	"chainstats", "chainhandler", "chainapp", "chainreport", "chainclash", "assignedlib", "assignedclient", "globalsvalues", "trustedwrites", "trustedwritesclient", "reachlib", "reachclient", "guidestats", "guidehandler", "dynlib", "dynhook", "dyniface", "varinv", "varinvbad", "letoutq", "letoutp", "letoutmain", "exportedp", "exportedmain", "exportedp2", "exportedmain2", "closedq", "isolatedq", "isolatedg", "lockgroup", "lockgroupbad", "lockgrouprw", "mustcompile", "initvalues", "loggervar", "hiddenlookq", "hiddenlook", "typeonlylib", "typeonlyclient", "keepsvars", "guidelocks", "initcallslib", "initcallsclient", "initcalls", "readerbad", "pathstore", "madehere", "varcodelib", "varcode", "boxed", "boxedlib", "boxedclient", "closed", "typederrors", "typederrorsclient", "typederrorsbad", "typedowns", "runsclaims", "typederrorspos", "ptrstates", "ptrlib", "dynheld", "dynifaces", "dyneq", "optional", "optionalio", "arrays", "arraystructs", "copies", "tables", "tablesclient",
	"exits", "exitsmain", "exitsbad", "exitslib", "exitsref", "exitsrefok", "guidemain", "ownstorage", "exitsinit", "ptrbase", "ptrvals", "ptrvalsbad", "ptrvalslib", "ptrvalsclient", "labels", "labelsbad",
}

func TestAnalyzer(t *testing.T) {
	parallel(t)
	t.Run("verifies annotated functions", func(t *testing.T) {
		parallel(t)
		analyzer := newAnalyzer()
		if err := analyzer.Flags.Set("trusted", filepath.Join("testdata", "trusted.yaml")); err != nil {
			t.Fatalf("set trusted: %v", err)
		}
		// The rejected corpus has tags of another tool, some declared here
		// and some not.
		if err := analyzer.Flags.Set("other-tags", "Summary, Param,x-order"); err != nil {
			t.Fatalf("set other-tags: %v", err)
		}

		costs := collectCosts(analyzer)
		compared := solver.Compared()
		runCorpus(t, analyzer, mainCorpus...)
		// The comparison that init turns on ran on the checks of the
		// corpus; tests beside this one can only add to the count.
		if solver.Compared() == compared {
			t.Error("no contradiction check of the corpus was compared with its first attempt")
		}
		recorded, quoted := costs()
		// The checks for a contradiction of the shipped entries of
		// slices.Delete, slices.DeleteFunc, and slices.Compact, and after
		// each call of them, conclude; they ran to the limit at every use
		// before they were asked first without e-matching.
		for key, line := range recorded {
			if strings.HasPrefix(key, "deletes\t") && line.limits > 0 {
				t.Errorf("%s left %d problems open", strings.ReplaceAll(key, "\t", " "), line.limits)
			}
		}
		checkCosts(t, recorded)
		checkGuideCost(t, quoted)
	})

	// Each of these is the only package analysed, as when laas is run on
	// it alone: a dependency that changes an error variable is reported in
	// every package built with both it and a proof that relies on the
	// variable.
	for _, root := range []string{"gonelib", "gonemid", "goneroot", "gonereader", "wrapsp", "wrapsmid", "wrapsroot", "linkedlib", "linkedpull", "linkedroot", "linkedasm", "linkedpullnear"} {
		t.Run("reports a changed error variable in "+root, func(t *testing.T) {
			parallel(t)
			runCorpus(t, newAnalyzer(), root)
		})
	}

	// The same for a package-level variable that is not an error: a
	// package in the build that assigns it, or that gives its storage to a
	// variable of its own, against a proof that relies on its value.
	for _, root := range []string{"globalsmid", "globalspull", "globalsroot"} {
		t.Run("reports a changed package-level variable in "+root, func(t *testing.T) {
			parallel(t)
			runCorpus(t, newAnalyzer(), root)
		})
	}

	// Two modules give one type two entries. The packages that use them are
	// only dependencies here, as when laas is run on the main package, and
	// each alone is analysed without a report.
	t.Run("reports two entries for one type in a build", func(t *testing.T) {
		parallel(t)
		runCorpus(t, newAnalyzer(), "tworoot")
	})
	// A module whose proofs were made with no entry for a type, and one
	// that declares the type and has proofs that rest on it having none,
	// against a module that gives it an entry.
	t.Run("reports an entry against none in a build", func(t *testing.T) {
		parallel(t)
		runCorpus(t, newAnalyzer(), "twod")
	})
	// Two modules count different interfaces of O for one static type
	// (D5 of F35).
	t.Run("reports two sets of interfaces checked at conversions in a build", func(t *testing.T) {
		parallel(t)
		runCorpus(t, newAnalyzer(), "optroot")
	})
	// A module that declares states of an interface of another module, and
	// one whose proofs were made with none.
	t.Run("reports two declarations of states in a build", func(t *testing.T) {
		parallel(t)
		runCorpus(t, newAnalyzer(), "stateroot")
	})
	t.Run("refuses states of io.Closer in a project file", func(t *testing.T) {
		parallel(t)
		runCorpus(t, newAnalyzer(), "stateover")
	})
	for _, root := range []string{"statea", "stateb"} {
		t.Run("uses the states of its own module in "+root, func(t *testing.T) {
			parallel(t)
			runCorpus(t, newAnalyzer(), root)
		})
	}
	// A module with no trust file, which uses the shipped entries of bufio.
	t.Run("uses the shipped entries of bufio", func(t *testing.T) {
		parallel(t)
		runCorpus(t, newAnalyzer(), "scanerrs")
	})
	// A module that gives (io.Closer).Close an entry of its own, which
	// shipped entries rest on (S0 of F35).
	t.Run("refuses a replacement of Close", func(t *testing.T) {
		parallel(t)
		runCorpus(t, newAnalyzer(), "closer")
	})
	// Modules that replace shipped entries other shipped entries rest on,
	// by the same entry and by ones that differ (S0 of F35).
	for _, root := range []string{"replaceda", "replacedb", "replacedc"} {
		t.Run("replaces rested-on entries in "+root, func(t *testing.T) {
			parallel(t)
			runCorpus(t, newAnalyzer(), root)
		})
	}
	// A module whose entry of a method of an interface claims that it ends
	// the process (F5 of the design review of F37).
	t.Run("refuses exits in an entry of a method", func(t *testing.T) {
		parallel(t)
		runCorpus(t, newAnalyzer(), "exitsentry")
	})
	// A module with entries of its own for methods of sync's mutexes.
	t.Run("reads states in project entries", func(t *testing.T) {
		parallel(t)
		runCorpus(t, newAnalyzer(), "lockentries")
	})
	// Programs under a declared memory and the same without it (F38).
	for _, root := range []string{"sizes", "nosizes", "sizesbad"} {
		t.Run("proves what fits under a declared memory in "+root, func(t *testing.T) {
			parallel(t)
			runCorpus(t, newAnalyzer(), root)
		})
	}
	// Verified packages built together declare one memory (F13 of the
	// review of F38), in both directions, and the same verifies.
	for _, root := range []string{"memnone", "memdecl", "memsame"} {
		t.Run("compares the declared memories in "+root, func(t *testing.T) {
			parallel(t)
			runCorpus(t, newAnalyzer(), root)
		})
	}
	for _, root := range []string{"twoa", "twob", "twoc"} {
		t.Run("uses one entry for a type in "+root, func(t *testing.T) {
			parallel(t)
			runCorpus(t, newAnalyzer(), root)
		})
	}

	// Code of the package handed to another package through an
	// unsafe.Pointer.
	t.Run("follows an unsafe.Pointer handed to another package", func(t *testing.T) {
		parallel(t)
		runCorpus(t, newAnalyzer(), "unsafecycle")
	})

	// Values that hold a sync/atomic.Pointer, handed to trusted functions.
	t.Run("counts an atomic pointer as a pointer to its type argument", func(t *testing.T) {
		parallel(t)
		runCorpus(t, newAnalyzer(), "heldcode")
	})

	// Formulas written with Go's operators, in source and in a trust file.
	t.Run("refuses the operators of Go in formulas", func(t *testing.T) {
		parallel(t)
		runCorpus(t, newAnalyzer(), "gospellings")
	})

	// A project trust file with a problem is named at every call that
	// went through the trust file, since an entry it means to give may be
	// among what was not read.
	for _, root := range []string{"badyaml", "badkeys"} {
		t.Run("names the problems of the trust file in "+root, func(t *testing.T) {
			parallel(t)
			runCorpus(t, newAnalyzer(), root)
		})
	}

	t.Run("refuses a trust file with a defect", func(t *testing.T) {
		parallel(t)
		analyzer := newAnalyzer()
		if err := analyzer.Flags.Set("trusted", filepath.Join("testdata", "defective-trusted.yaml")); err != nil {
			t.Fatalf("set trusted: %v", err)
		}

		runCorpus(t, analyzer, "badtrust")
	})

	t.Run("audits specifications on request", func(t *testing.T) {
		parallel(t)
		analyzer := newAnalyzer()
		if err := analyzer.Flags.Set("audit", "true"); err != nil {
			t.Fatalf("set audit: %v", err)
		}

		runCorpus(t, analyzer, "audit")
	})
}

// TestPackageSettings runs the corpus programs that need a setting of the
// whole package changed, while no other test runs.
func TestPackageSettings(t *testing.T) {
	// The bound on the size of a formula stops a program whose formulas
	// grow faster than its text. That growth is what the program is for, so
	// the check that fails on it is off.
	t.Run("refuses a formula that grows beyond the limit", func(t *testing.T) {
		alone(t)
		saved := growthRatio
		growthRatio = 0
		defer func() { growthRatio = saved }()
		runCorpus(t, newAnalyzer(), "toolarge")
	})

	t.Run("refuses to verify for a caching driver", func(t *testing.T) {
		alone(t)
		RefuseCachedRuns()
		defer func() { refuseCache = false }()

		runCorpus(t, newAnalyzer(), "refused")
	})
}

func TestOtherTagsFlag(t *testing.T) {
	parallel(t)
	tests := []struct {
		name, list string
		want       []string
		wantErr    string
	}{
		{name: "nothing declared", list: ""},
		{name: "several words with spaces around them", list: "Summary, Param ,x-order", want: []string{"Param", "Summary", "x-order"}},
		{name: "a keyword", list: "Summary,Ensures", wantErr: "too close"},
		{name: "a keyword but for a letter", list: "Ensure", wantErr: "too close"},
		{name: "a keyword but for its case", list: "requires", wantErr: "too close"},
		{name: "a retired keyword", list: "Measure", wantErr: "too close"},
		{name: "a retired keyword in another case", list: "measure", wantErr: "too close"},
		{name: "a planned keyword in another case", list: "cost", wantErr: "too close"},
		{name: "a keyword with its formula glued to it", list: "Ensures(1=2)", wantErr: "too close"},
		{name: "an assertion with its formula glued to it", list: "Assert(False)", wantErr: "too close"},
		{name: "a retired keyword with signs after it", list: "Measure(0)", wantErr: "too close"},
		{name: "a keyword behind signs", list: "(((Ensures", wantErr: "does not start with a letter"},
		{name: "an assertion behind signs", list: "###Assert", wantErr: "does not start with a letter"},
		{name: "an assertion behind digits", list: "123Assert", wantErr: "does not start with a letter"},
		{name: "a snapshot", list: "Snapshot", wantErr: "too close"},
		{name: "a snapshot with its formula glued to it", list: "Snapshot(x=1)", wantErr: "too close"},
		{name: "a snapshot but for two letters", list: "Snapsot", wantErr: "too close"},
		{name: "a snapshot in another case", list: "snapshot", wantErr: "too close"},
		{name: "the tags of swag beside the snapshot", list: "host,Post,title", want: []string{"Post", "host", "title"}},
		{name: "a vouch", list: "Vouches", wantErr: "too close"},
		{name: "a vouch in another case", list: "vouches", wantErr: "too close"},
		{name: "a vouch with its names glued to it", list: "Vouches(err)", wantErr: "too close"},
		{name: "a retired keyword behind a sign", list: "-Measure", wantErr: "does not start with a letter"},
		{name: "a keyword after other letters and a sign", list: "x-Ensures", wantErr: "too close"},
		{name: "two words in one", list: "Summary Param", wantErr: "not a single word"},
	}
	for _, test := range tests {
		t.Run(test.name, func(t *testing.T) {
			got, err := parseOtherTags(test.list)
			switch {
			case test.wantErr != "" && (err == nil || !strings.Contains(err.Error(), test.wantErr)):
				t.Fatalf("got error %v, want one containing %q", err, test.wantErr)
			case test.wantErr == "" && err != nil:
				t.Fatalf("unexpected error: %v", err)
			}
			if tags := slices.Sorted(maps.Keys(got)); test.wantErr == "" && !slices.Equal(tags, test.want) {
				t.Fatalf("got %v, want %v", tags, test.want)
			}
		})
	}
}

// TestShownAnnotationsScan checks the pass that takes shown annotations out
// of a comment on inputs that would take minutes if it looked again from
// every slash of a long run of them.
func TestShownAnnotationsScan(t *testing.T) {
	parallel(t)
	slashes := strings.Repeat("/", 1<<20)
	tests := []struct {
		name, text, want string
	}{
		{name: "a run of slashes", text: " " + slashes, want: " " + slashes},
		{name: "a run of slashes in a string after a shown annotation", text: ` // @Ensures s = "` + slashes + `" and more`, want: "   s =   and more"},
		{name: "an empty string between two words after a shown annotation", text: ` // @Requires x @Ensures""Extra`, want: "   x @Ensures Extra"},
		{name: "a string inside a word after a shown annotation", text: ` // @Requires x @En"text"sures`, want: "   x @En sures"},
		{name: "a run of slashes in a string with nothing shown", text: ` see "` + slashes + `"`, want: ` see "` + slashes + `"`},
	}
	for _, test := range tests {
		t.Run(test.name, func(t *testing.T) {
			if got := withoutShown(test.text); got != test.want {
				t.Fatalf("got %d bytes starting %.40q, want %d bytes starting %.40q", len(got), got, len(test.want), test.want)
			}
		})
	}
}

// What the verifier builds must not grow faster than the program: a term
// that goes into a join of the ends of a function literal must not grow
// with the joins before it, and a value bound or stored must not be much
// larger as a tree than in memory. The tests catch either at once.
func init() {
	joinSizeLimit = 1 << 12
	growthRatio = 8
	// The numbers in the keys of regions start at 7, so that the types of
	// a package cross from one digit to two at another place than they do
	// in a run of laas, and the keys sort in another order; the table of
	// costs, recorded at 0, must still be exact.
	typeKeyBase = 7
	// VEGO_CACHE names a cache of answers for the tests to use; see
	// -vego.cache. Without it every test asks Z3.
	testCache = os.Getenv("VEGO_CACHE")
	// Every contradiction check that its first attempt settles is also
	// asked in full, and the two answers must agree; see
	// solver.CompareModelFirst.
	solver.CompareModelFirst()
}
