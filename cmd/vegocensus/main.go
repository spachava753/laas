// Command vegocensus summarises what a census of vego found.
//
// A census is a run of laas with -vego.census=FILE and
// -vego.census-scope=MODULE, which looks at every function of a module with
// the weakest contract, proves nothing, and writes one JSON line per
// function with what stopped the verifier there. This command reads such
// files and writes the tables of docs/verification.md's census and of
// vego/ROADMAP.md.
//
// Usage:
//
//	vegocensus summary [-tsv FILE] NAME=FILE...
//	vegocensus notloaded -module PATH -dir DIR -have FILE [-skip REGEXP]
//
// summary reads each FILE as the corpus NAME and writes a summary in
// Markdown to standard output: per corpus, per module of a corpus with
// several, and merged, both by functions and with each module weighted
// equally. With -tsv it also writes one row per function and cause.
//
// notloaded writes a line of class package:not-loaded for every function
// with a body of the module in DIR that FILE has no line for, as for the
// packages of a module that did not load; files that the build constraints
// of the host leave out are skipped, and so are the packages -skip matches.
// The module std names the standard library in GOROOT/src.
package main

import (
	"bufio"
	"encoding/json"
	"flag"
	"fmt"
	"go/ast"
	"go/build"
	"go/parser"
	"go/token"
	"go/types"
	"io"
	"io/fs"
	"maps"
	"os"
	"path/filepath"
	"regexp"
	"slices"
	"sort"
	"strings"
)

// line is one line of a census file.
type line struct {
	Module     string   `json:"module"`
	Package    string   `json:"package"`
	Function   string   `json:"function"`
	Pos        string   `json:"pos"`
	Statements int      `json:"statements"`
	Unseen     int      `json:"unseen"`
	UnseenAt   []string `json:"unseen_at,omitempty"`
	Stopped    bool     `json:"stopped,omitempty"`
	Events     []event  `json:"events,omitempty"`
}

// event is a refusal or another event the census met in a function.
type event struct {
	Class   string `json:"class"`
	Detail  string `json:"detail,omitempty"`
	Pos     string `json:"pos"`
	Message string `json:"message,omitempty"`
	Kind    string `json:"kind"`
}

func main() {
	if len(os.Args) < 2 {
		fmt.Fprintln(os.Stderr, "usage: vegocensus summary [-tsv FILE] NAME=FILE... | vegocensus notloaded -module PATH -dir DIR -have FILE")
		os.Exit(2)
	}
	var err error
	switch os.Args[1] {
	case "summary":
		err = summary(os.Args[2:], os.Stdout)
	case "notloaded":
		err = notLoaded(os.Args[2:], os.Stdout)
	default:
		err = fmt.Errorf("unknown command %q", os.Args[1])
	}
	if err != nil {
		fmt.Fprintln(os.Stderr, "vegocensus:", err)
		os.Exit(1)
	}
}

// read reads the lines of a census file.
func read(path string) ([]line, error) {
	f, err := os.Open(path)
	if err != nil {
		return nil, err
	}
	defer f.Close()
	var lines []line
	scanner := bufio.NewScanner(f)
	scanner.Buffer(nil, 1<<24)
	for scanner.Scan() {
		var l line
		if err := json.Unmarshal(scanner.Bytes(), &l); err != nil {
			return nil, fmt.Errorf("%s: %v", path, err)
		}
		lines = append(lines, l)
	}
	return lines, scanner.Err()
}

// fn is what the summary knows of one function.
type fn struct {
	corpus, module string
	line           line
	// causes holds the classes of its causes, details the class and detail
	// of each, and proof those of the refusals made only when a proof
	// fails, which no count of what a class stops reads.
	causes, proof map[string]bool
	details       map[string]bool
	first         string
	// partial is set for a function not looked at in full: some statement
	// was not entered, or the census stopped in it.
	partial  bool
	assumed  []string
	declared bool
}

// analyse reads what the summary needs of a line.
func analyse(corpus string, l line) *fn {
	f := &fn{corpus: corpus, module: l.Module, line: l, causes: map[string]bool{}, proof: map[string]bool{}, details: map[string]bool{},
		partial: l.Unseen > 0 || l.Stopped}
	for _, e := range l.Events {
		switch e.Kind {
		case "cause":
			f.causes[e.Class] = true
			f.details[e.Class+"\x00"+e.Detail] = true
			if f.first == "" {
				f.first = e.Class
			}
		case "proof":
			f.proof[e.Class] = true
		case "stop":
			f.partial = true
			f.causes[e.Class] = true
			if f.first == "" {
				f.first = e.Class
			}
		case "assumed", "annotate":
			f.assumed = append(f.assumed, e.Class+"|"+e.Detail)
		case "declared":
			f.declared = true
		}
	}
	return f
}

// group returns the group of a class.
func group(class string) string {
	g, _, _ := strings.Cut(class, ":")
	return g
}

// through reports whether a function gets through: no cause, and looked
// at in full.
func (f *fn) through() bool { return len(f.causes) == 0 && !f.partial }

// alone returns the one class that stops a function looked at in full, or
// "", by the classes or by their groups.
func (f *fn) alone(groups bool) string {
	if f.partial {
		return ""
	}
	keys := f.keys(groups, nil)
	if len(keys) != 1 {
		return ""
	}
	return keys[0]
}

// keys returns the classes, or the groups, of a function's causes, without
// those left out.
func (f *fn) keys(groups bool, without map[string]bool) []string {
	seen := map[string]bool{}
	var keys []string
	for class := range f.causes {
		key := class
		if groups {
			key = group(class)
		}
		if !seen[key] && !without[class] && !without[key] {
			seen[key] = true
			keys = append(keys, key)
		}
	}
	sort.Strings(keys)
	return keys
}

// summary reads the census files named, each as a corpus, writes the TSV
// when asked, and writes the summary: first the sentence that says what
// getting through means, then for each corpus its report, and for a corpus
// of several modules a table of the modules and its report with each module
// weighted equally; then, for several corpora, the report of all of them,
// by functions and by modules.
func summary(args []string, w io.Writer) error {
	flags := flag.NewFlagSet("summary", flag.ContinueOnError)
	tsv := flags.String("tsv", "", "write one row per function and cause to this file")
	if err := flags.Parse(args); err != nil {
		return err
	}
	var corpora []string
	byCorpus := map[string][]*fn{}
	for _, arg := range flags.Args() {
		name, path, ok := strings.Cut(arg, "=")
		if !ok {
			return fmt.Errorf("%q is not NAME=FILE", arg)
		}
		lines, err := read(path)
		if err != nil {
			return err
		}
		if _, dup := byCorpus[name]; !dup {
			corpora = append(corpora, name)
		}
		for _, l := range lines {
			byCorpus[name] = append(byCorpus[name], analyse(name, l))
		}
	}
	if *tsv != "" {
		if err := writeTSV(*tsv, corpora, byCorpus); err != nil {
			return err
		}
	}
	fmt.Fprintln(w, "A function that gets through met no refusal of vego on the weakest contract, `// @Ensures True`; it is not verified. "+
		"The census ran as a project that declares `sizes` and `inputs` in its trust file, and proved nothing.")
	fmt.Fprintln(w)
	var all []*fn
	for _, name := range corpora {
		fns := byCorpus[name]
		all = append(all, fns...)
		report(w, "Corpus "+name, fns, nil)
		modules := map[string][]*fn{}
		for _, f := range fns {
			modules[f.module] = append(modules[f.module], f)
		}
		if len(modules) > 1 {
			moduleTable(w, name, modules)
			report(w, "Corpus "+name+", each module weighted equally", fns, moduleWeights(fns))
		}
	}
	if len(corpora) > 1 {
		report(w, "All corpora", all, nil)
		report(w, "All corpora, each module weighted equally", all, moduleWeights(all))
	}
	return nil
}

// moduleWeights gives each function the weight that makes every module
// count as one.
func moduleWeights(fns []*fn) map[*fn]float64 {
	weights := map[*fn]float64{}
	modules := map[string]int{}
	for _, f := range fns {
		modules[f.corpus+"\x00"+f.module]++
	}
	for _, f := range fns {
		weights[f] = 1 / float64(modules[f.corpus+"\x00"+f.module])
	}
	return weights
}

// weight returns what a function counts for.
func weight(weights map[*fn]float64, f *fn) float64 {
	if weights == nil {
		return 1
	}
	return weights[f]
}

// number writes a count, with a fraction only when weighted.
func number(weights map[*fn]float64, n float64) string {
	if weights == nil {
		return fmt.Sprintf("%d", int(n+0.5))
	}
	return fmt.Sprintf("%.1f", n)
}

// report writes the summary of a set of functions.
func report(w io.Writer, title string, fns []*fn, weights map[*fn]float64) {
	var total, notLoaded, through, partial, proofOnly, declared, assumed, unseen float64
	for _, f := range fns {
		wt := weight(weights, f)
		total += wt
		switch {
		case f.causes["package:not-loaded"]:
			notLoaded += wt
		case f.through():
			through += wt
			if len(f.proof) > 0 {
				proofOnly += wt
			}
		}
		if f.partial && !f.causes["package:not-loaded"] {
			partial += wt
			unseen += float64(f.line.Unseen) * wt
		}
		if f.declared {
			declared += wt
		}
		if len(f.assumed) > 0 {
			assumed += wt
		}
	}
	n := func(x float64) string { return number(weights, x) }
	fmt.Fprintf(w, "## %s\n\n", title)
	fmt.Fprintf(w, "- functions with a body: %s, of which not loaded: %s\n", n(total), n(notLoaded))
	fmt.Fprintf(w, "- get through: %s (%.1f%%), of which %s only past refusals made when a proof fails\n", n(through), 100*through/max(total, 1), n(proofOnly))
	fmt.Fprintf(w, "- not looked at in full (a statement no attempt entered, or the census stopped): %s, with %s statements not entered\n", n(partial), n(unseen))
	fmt.Fprintf(w, "- reach what only a declaration of the trust file allows: %s\n", n(declared))
	fmt.Fprintf(w, "- assume a callee, method, or function type of the module with the weakest contract: %s\n\n", n(assumed))
	for _, groups := range []bool{false, true} {
		classTable(w, fns, weights, groups)
	}
	for _, without := range []func(string) bool{nil, projectWrites} {
		for _, groups := range []bool{false, true} {
			greedy(w, fns, weights, groups, without)
		}
	}
	callees(w, fns, weights)
	proofs(w, fns, weights)
	stops(w, fns)
}

// classTable writes, for each class or group, the functions it stops,
// alone, first, and in functions not looked at in full.
func classTable(w io.Writer, fns []*fn, weights map[*fn]float64, groups bool) {
	type row struct {
		key                          string
		stopped, alone, first, part float64
		details                      map[string][2]float64
	}
	rows := map[string]*row{}
	get := func(key string) *row {
		if rows[key] == nil {
			rows[key] = &row{key: key, details: map[string][2]float64{}}
		}
		return rows[key]
	}
	for _, f := range fns {
		wt := weight(weights, f)
		alone := f.alone(groups)
		for _, key := range f.keys(groups, nil) {
			r := get(key)
			r.stopped += wt
			if f.partial {
				r.part += wt
			}
			if key == alone {
				r.alone += wt
			}
		}
		if f.first != "" {
			first := f.first
			if groups {
				first = group(first)
			}
			get(first).first += wt
		}
		if groups {
			continue
		}
		// Details: the function counts for each detail of a class once,
		// and alone when that detail is its only cause.
		var only string
		if !f.partial && len(f.details) == 1 {
			for d := range f.details {
				only = d
			}
		}
		for d := range f.details {
			class, detail, _ := strings.Cut(d, "\x00")
			if detail == "" {
				continue
			}
			c := get(class).details[detail]
			c[0] += wt
			if d == only {
				c[1] += wt
			}
			get(class).details[detail] = c
		}
	}
	var list []*row
	for _, r := range rows {
		list = append(list, r)
	}
	sort.Slice(list, func(i, j int) bool {
		if list[i].stopped != list[j].stopped {
			return list[i].stopped > list[j].stopped
		}
		return list[i].key < list[j].key
	})
	what := "class"
	if groups {
		what = "group"
	}
	n := func(x float64) string { return number(weights, x) }
	fmt.Fprintf(w, "### Refusals by %s\n\n| %s | functions stopped | stopped alone | first cause | not looked at in full | top details (stopped, alone) |\n| --- | --- | --- | --- | --- | --- |\n", what, what)
	for _, r := range list {
		var top []string
		if !groups {
			var details []string
			for d := range r.details {
				details = append(details, d)
			}
			sort.Slice(details, func(i, j int) bool {
				if a, b := r.details[details[i]][0], r.details[details[j]][0]; a != b {
					return a > b
				}
				return details[i] < details[j]
			})
			for _, d := range details[:min(len(details), 3)] {
				top = append(top, fmt.Sprintf("`%s` (%s, %s)", d, n(r.details[d][0]), n(r.details[d][1])))
			}
		}
		fmt.Fprintf(w, "| `%s` | %s | %s | %s | %s | %s |\n", r.key, n(r.stopped), n(r.alone), n(r.first), n(r.part), strings.Join(top, "; "))
	}
	fmt.Fprintln(w)
}

// greedy writes the first twenty classes or groups in the order that lets
// the most functions through: each step takes the one whose fixing lets
// the most more through, with those before it taken as fixed. A function
// not looked at in full is never let through, and the refusals made only
// when a proof fails are left out of it.
func greedy(w io.Writer, fns []*fn, weights map[*fn]float64, groups bool, without func(string) bool) {
	fixed := map[string]bool{}
	for _, f := range fns {
		for class := range f.causes {
			if without != nil && without(class) {
				fixed[class] = true
			}
		}
	}
	let := 0.0
	for _, f := range fns {
		if !f.partial && len(f.keys(groups, fixed)) == 0 {
			let += weight(weights, f)
		}
	}
	what := "classes"
	if groups {
		what = "groups"
	}
	left := ""
	if without != nil {
		left = ", with what the project writes for other modules (no-entry:other and the classes ending in -other) left out of the causes"
	}
	n := func(x float64) string { return number(weights, x) }
	fmt.Fprintf(w, "### Greedy order of %s%s\n\nGet through with nothing fixed: %s.\n\n| step | fixed | let through by it | let through in all |\n| --- | --- | --- | --- |\n", what, left, n(let))
	for step := 1; step <= 20; step++ {
		gain := map[string]float64{}
		for _, f := range fns {
			if f.partial {
				continue
			}
			if keys := f.keys(groups, fixed); len(keys) == 1 {
				gain[keys[0]] += weight(weights, f)
			}
		}
		best, most := "", 0.0
		for key, g := range gain {
			if g > most || g == most && key < best {
				best, most = key, g
			}
		}
		if best == "" {
			break
		}
		fixed[best] = true
		let += most
		fmt.Fprintf(w, "| %d | `%s` | %s | %s |\n", step, best, n(most), n(let))
	}
	fmt.Fprintln(w)
}

// proofs writes the classes of refusals made only when a proof fails,
// which the counts of causes and the greedy orders leave out: for each, the
// functions it is met in, those it is the only thing in, and the top
// details.
func proofs(w io.Writer, fns []*fn, weights map[*fn]float64) {
	type row struct {
		met, only float64
		details   map[string]float64
	}
	rows := map[string]*row{}
	for _, f := range fns {
		wt := weight(weights, f)
		for class := range f.proof {
			r := rows[class]
			if r == nil {
				r = &row{details: map[string]float64{}}
				rows[class] = r
			}
			r.met += wt
			if len(f.causes) == 0 && len(f.proof) == 1 && !f.partial {
				r.only += wt
			}
		}
		for _, e := range f.line.Events {
			if e.Kind == "proof" && e.Detail != "" {
				rows[e.Class].details[e.Detail] += wt
			}
		}
	}
	if len(rows) == 0 {
		return
	}
	n := func(x float64) string { return number(weights, x) }
	fmt.Fprintf(w, "### Refusals made only when a proof fails\n\nA census proves nothing, so it makes these wherever they are reached; the prover would often prove what they ask.\n\n"+
		"| class | functions met in | the only thing met | top details |\n| --- | --- | --- | --- |\n")
	for _, class := range slices.Sorted(maps.Keys(rows)) {
		r := rows[class]
		details := slices.Sorted(maps.Keys(r.details))
		sort.SliceStable(details, func(i, j int) bool { return r.details[details[i]] > r.details[details[j]] })
		var top []string
		for _, d := range details[:min(len(details), 3)] {
			top = append(top, fmt.Sprintf("`%s` (%s)", d, n(r.details[d])))
		}
		fmt.Fprintf(w, "| `%s` | %s | %s | %s |\n", class, n(r.met), n(r.only), strings.Join(top, "; "))
	}
	fmt.Fprintln(w)
}

// projectWrites reports whether a class is one the project lifts by
// writing an entry for another module: no-entry:other, and the classes of
// interfaces, types, and function types of other modules.
func projectWrites(class string) bool {
	return strings.HasSuffix(class, ":other") || strings.HasSuffix(class, "-other")
}

// callees writes the fifty callees without an entry that stop the most
// functions, alone and not.
func callees(w io.Writer, fns []*fn, weights map[*fn]float64) {
	counts := map[string][2]float64{}
	for _, f := range fns {
		wt := weight(weights, f)
		for d := range f.details {
			class, detail, _ := strings.Cut(d, "\x00")
			if group(class) != "no-entry" || detail == "" {
				continue
			}
			key := class + " " + detail
			c := counts[key]
			c[0] += wt
			if !f.partial && len(f.details) == 1 {
				c[1] += wt
			}
			counts[key] = c
		}
	}
	var keys []string
	for k := range counts {
		keys = append(keys, k)
	}
	sort.Slice(keys, func(i, j int) bool {
		if a, b := counts[keys[i]][0], counts[keys[j]][0]; a != b {
			return a > b
		}
		return keys[i] < keys[j]
	})
	n := func(x float64) string { return number(weights, x) }
	fmt.Fprintf(w, "### Callees without an entry\n\n| callee | class | functions stopped | stopped alone |\n| --- | --- | --- | --- |\n")
	for _, k := range keys[:min(len(keys), 50)] {
		class, callee, _ := strings.Cut(k, " ")
		fmt.Fprintf(w, "| `%s` | `%s` | %s | %s |\n", callee, class, n(counts[k][0]), n(counts[k][1]))
	}
	fmt.Fprintln(w)
}

// stops lists the functions in which the census stopped for a panic of
// the verifier, which come first.
func stops(w io.Writer, fns []*fn) {
	var internal []string
	for _, f := range fns {
		for _, e := range f.line.Events {
			if e.Class == "limit:internal" {
				internal = append(internal, fmt.Sprintf("- `%s.%s`: %s", f.line.Package, f.line.Function, strings.SplitN(e.Message, "\n", 2)[0]))
			}
		}
	}
	if len(internal) == 0 {
		return
	}
	fmt.Fprintf(w, "### Panics of the verifier (limit:internal)\n\n%s\n\n", strings.Join(internal, "\n"))
}

// moduleTable writes, for each module of a corpus, its functions, those
// that get through, and its first three classes.
func moduleTable(w io.Writer, corpus string, modules map[string][]*fn) {
	names := slices.Sorted(func(yield func(string) bool) {
		for m := range modules {
			if !yield(m) {
				return
			}
		}
	})
	fmt.Fprintf(w, "### Modules of %s\n\n| module | functions | get through | not looked at in full | first three classes (functions stopped) |\n| --- | --- | --- | --- | --- |\n", corpus)
	for _, m := range names {
		fns := modules[m]
		through, partial := 0, 0
		counts := map[string]int{}
		for _, f := range fns {
			if f.through() {
				through++
			}
			if f.partial {
				partial++
			}
			for class := range f.causes {
				counts[class]++
			}
		}
		var classes []string
		for c := range counts {
			classes = append(classes, c)
		}
		sort.Slice(classes, func(i, j int) bool {
			if counts[classes[i]] != counts[classes[j]] {
				return counts[classes[i]] > counts[classes[j]]
			}
			return classes[i] < classes[j]
		})
		var top []string
		for _, c := range classes[:min(len(classes), 3)] {
			top = append(top, fmt.Sprintf("`%s` (%d)", c, counts[c]))
		}
		fmt.Fprintf(w, "| `%s` | %d | %d | %d | %s |\n", m, len(fns), through, partial, strings.Join(top, ", "))
	}
	fmt.Fprintln(w)
}

// writeTSV writes one row per function and cause, and one per function
// that gets through.
func writeTSV(path string, corpora []string, byCorpus map[string][]*fn) error {
	f, err := os.Create(path)
	if err != nil {
		return err
	}
	b := bufio.NewWriter(f)
	fmt.Fprintln(b, "corpus\tmodule\tpackage\tfunction\tclass\tdetail\tposition\tkind")
	for _, name := range corpora {
		for _, fn := range byCorpus[name] {
			l := fn.line
			wrote := false
			for _, e := range l.Events {
				fmt.Fprintf(b, "%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n", name, l.Module, l.Package, l.Function, e.Class, e.Detail, e.Pos, e.Kind)
				wrote = true
			}
			if !wrote {
				fmt.Fprintf(b, "%s\t%s\t%s\t%s\t\t\t%s\tthrough\n", name, l.Module, l.Package, l.Function, l.Pos)
			}
		}
	}
	if err := b.Flush(); err != nil {
		f.Close()
		return err
	}
	return f.Close()
}

// notLoaded writes a line for every function with a body of a module that
// a census file has none for.
func notLoaded(args []string, w io.Writer) error {
	flags := flag.NewFlagSet("notloaded", flag.ContinueOnError)
	module := flags.String("module", "", "the module path")
	dir := flags.String("dir", "", "the directory of the module")
	have := flags.String("have", "", "the census file of the module")
	skip := new(*regexp.Regexp)
	flags.Func("skip", "leave out the packages whose path matches this expression; empty leaves out none", func(text string) (err error) {
		if text == "" {
			return nil
		}
		*skip, err = regexp.Compile(text)
		return err
	})
	if err := flags.Parse(args); err != nil {
		return err
	}
	lines, err := read(*have)
	if err != nil && !os.IsNotExist(err) {
		return err
	}
	seen := map[string]bool{}
	for _, l := range lines {
		seen[l.Package+"\x00"+l.Function] = true
	}
	ctx := build.Default
	return filepath.WalkDir(*dir, func(path string, d fs.DirEntry, err error) error {
		if err != nil {
			return err
		}
		name := d.Name()
		if d.IsDir() {
			if path != *dir && (name == "testdata" || name == "vendor" || strings.HasPrefix(name, ".") || strings.HasPrefix(name, "_")) {
				return filepath.SkipDir
			}
			// A nested module is not part of this one.
			if path != *dir {
				if _, err := os.Stat(filepath.Join(path, "go.mod")); err == nil {
					return filepath.SkipDir
				}
			}
			return nil
		}
		if !strings.HasSuffix(name, ".go") || strings.HasSuffix(name, "_test.go") {
			return nil
		}
		if ok, err := ctx.MatchFile(filepath.Dir(path), name); err != nil || !ok {
			return nil
		}
		rel, err := filepath.Rel(*dir, filepath.Dir(path))
		if err != nil {
			return err
		}
		// The packages of the standard library are named by their
		// directories under GOROOT/src.
		pkg := *module
		switch {
		case *module == "std":
			pkg = filepath.ToSlash(rel)
		case rel != ".":
			pkg += "/" + filepath.ToSlash(rel)
		}
		if *skip != nil && (*skip).MatchString(pkg) {
			return nil
		}
		fset := token.NewFileSet()
		file, err := parser.ParseFile(fset, path, nil, parser.SkipObjectResolution)
		if err != nil {
			return nil
		}
		for _, decl := range file.Decls {
			fd, ok := decl.(*ast.FuncDecl)
			if !ok || fd.Body == nil {
				continue
			}
			fname := fd.Name.Name
			if fd.Recv != nil && len(fd.Recv.List) > 0 {
				fname = "(" + types.ExprString(fd.Recv.List[0].Type) + ")." + fname
			}
			if seen[pkg+"\x00"+fname] {
				continue
			}
			at := fset.Position(fd.Name.Pos())
			b, err := json.Marshal(line{Module: *module, Package: pkg, Function: fname,
				Pos:     fmt.Sprintf("%s/%s:%d", pkg, filepath.Base(at.Filename), at.Line),
				Stopped: true, Events: []event{{Class: "package:not-loaded", Pos: fmt.Sprintf("%s/%s:%d", pkg, filepath.Base(at.Filename), at.Line), Kind: "stop"}}})
			if err != nil {
				return err
			}
			fmt.Fprintf(w, "%s\n", b)
		}
		return nil
	})
}
