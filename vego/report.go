package vego

import (
	"fmt"
	"go/token"
	"maps"
	"path/filepath"
	"slices"
	"strings"
)

// TrustReport renders what the proofs of the analysed packages take on
// trust: the project's trusted contracts, the shipped contracts in use, the
// project entries no proof uses, and the calls to the error constructors
// whose behaviour vego knows without a contract. Paths are shown relative to
// dir.
func TrustReport(usages []*Usage, dir string) string {
	total := &Usage{}
	for _, usage := range usages {
		if usage != nil {
			total.add(usage)
		}
	}
	entries, constructors := total.Entries, total.Constructors
	slices.SortFunc(entries, func(a, b *EntryUse) int { return strings.Compare(a.Key+"\x00"+a.File, b.Key+"\x00"+b.File) })
	relative := func(path string) string {
		if rel, err := filepath.Rel(dir, path); err == nil && !strings.HasPrefix(rel, "..") {
			return rel
		}
		return path
	}
	places := func(positions []token.Position) string {
		var list []string
		for _, position := range positions {
			list = append(list, fmt.Sprintf("%s:%d", relative(position.Filename), position.Line))
		}
		slices.Sort(list)
		return strings.Join(slices.Compact(list), ", ")
	}
	var b strings.Builder
	section := func(title string, shipped bool) {
		var listed []*EntryUse
		for _, use := range entries {
			if use.Shipped == shipped {
				listed = append(listed, use)
			}
		}
		fmt.Fprintf(&b, "%s: %d\n", title, len(listed))
		for _, use := range listed {
			note := ""
			if use.Unpredictable {
				note = "  [may fail unpredictably]"
			}
			fmt.Fprintf(&b, "  %s%s\n", use.Key, note)
			fmt.Fprintf(&b, "    reason:  %s\n", use.Reason)
			if len(use.Runs) > 0 {
				fmt.Fprintf(&b, "    runs code held by: %s\n", strings.Join(use.Runs, ", "))
			}
			switch {
			case use.Never:
				fmt.Fprintf(&b, "    exits: a claim that the function ends the process as os.Exit does, without returning and without running deferred calls; "+
					"nothing after a call of it is checked\n")
			case use.Exits:
				fmt.Fprintf(&b, "    exits: a claim that the function may end the process as os.Exit does, without returning and without running deferred calls; "+
					"nothing is checked on the path where it does, and where it returns its ensures hold\n")
			}
			if use.Isolated {
				fmt.Fprintf(&b, "    isolated: a claim that it runs no code but what the call hands it through its arguments and receiver, and reaches no code "+
					"through memory that another call set, also not through any function it calls\n")
				if use.IsolatedReason != "" {
					fmt.Fprintf(&b, "    isolated, for the whole package: %s\n", use.IsolatedReason)
				}
			}
			if len(use.Keeps) > 0 {
				fmt.Fprintf(&b, "    keeps code held by: %s; a claim that the function runs none of it while the call lasts unless runs lists it, "+
					"holds it afterwards only in what it is kept in, and starts or registers nothing that runs it later\n", strings.Join(use.Keeps, "; "))
			}
			if len(use.Asserts) > 0 {
				fmt.Fprintf(&b, "    asserts what it is handed to: %s; a claim that it calls through an interface value or a function value nothing these parameters hold, "+
					"or that a call of what they hold returns, but the methods of the interfaces and the function types that their types reach and those of the types listed, "+
					"and uses no reflection on them; a parameter under runs or keeps that asserts does not list makes the same claim with an empty list\n",
					strings.Join(use.Asserts, "; "))
			}
			if len(use.Formats) > 0 {
				fmt.Fprintf(&b, "    formats as package fmt does: %s; a claim that it runs only the Format, GoString, Error, and String methods "+
					"that fmt runs, while the call lasts and on the goroutine that called it, keeps none of the values, and builds from them "+
					"at most 4096 bytes more than fmt prints for them, apart from what a logger adds from its own settings\n", strings.Join(use.Formats, ", "))
			}
			if len(use.Encodes) > 0 {
				fmt.Fprintf(&b, "    encodes as package encoding/json does: %s; a claim that it runs no method of what it is handed but those of time.Time, "+
					"json.RawMessage, and json.Number that encoding/json runs, while the call lasts and on the goroutine that called it, keeps nothing "+
					"of it, and allocates within the bound vego proves at each call\n", strings.Join(use.Encodes, ", "))
			}
			if len(use.Decodes) > 0 {
				fmt.Fprintf(&b, "    decodes as package encoding/json does into: %s; a claim that it writes only the exported fields encoding/json writes, "+
					"stores into them only memory it makes, runs no method of what it decodes into but those of time.Time, json.RawMessage, and json.Number, "+
					"keeps nothing of what it is handed, and allocates within the bound vego proves at each call\n", strings.Join(use.Decodes, ", "))
			}
			for _, callback := range use.Callbacks {
				fmt.Fprintf(&b, "    calls %s\n", callback)
			}
			// An entry for a method of an interface is a claim about the
			// method of every value of every interface that has it from
			// that declaration. What a trusted function returns or writes
			// is claimed by that function's vouches instead.
			reach := "that verified code gets from code that is not verified: from a caller, directly or in memory an argument reaches, " +
				"or from a call through a value; a value that a trusted function returns or writes is claimed by that function's vouches"
			if strings.HasPrefix(use.Key, "states of ") {
				// A declaration of states claims what every method that
				// does not list its receiver leaves alone.
				fmt.Fprintf(&b, "    a claim about every value of %s, or of an interface that has a method from it: each of its methods "+
					"whose contract does not list the receiver under modifies leaves these states unchanged\n", use.Every)
			} else if _, method, ok := strings.Cut(use.Key, ")."); ok && use.Every != "" && strings.HasPrefix(use.Key, "(") {
				fmt.Fprintf(&b, "    a claim about %s of every value of %s, or of an interface that has %s from it, %s\n", method, use.Every, method, reach)
			} else if use.Every != "" {
				fmt.Fprintf(&b, "    a claim about every value of %s %s\n", use.Every, reach)
			}
			if len(use.Vouches) > 0 {
				fmt.Fprintf(&b, "    vouches for the errors and function values in: %s\n", strings.Join(use.Vouches, ", "))
			}
			fmt.Fprintf(&b, "    defined: %s:%d\n", relative(use.File), use.Line)
			if len(use.Calls) > 0 {
				fmt.Fprintf(&b, "    used at: %s\n", places(use.Calls))
			} else {
				relied := slices.Clone(use.Relied)
				slices.Sort(relied)
				fmt.Fprintf(&b, "    relied on in: %s\n", strings.Join(relied, ", "))
			}
		}
		b.WriteString("\n")
	}
	b.WriteString("vego trust report\n\n")
	b.WriteString("Every proof vego reports as successful holds only if the contracts below are true.\n")
	b.WriteString("None of them is checked against the code of the function it describes.\n\n")
	if len(total.AnswerCaches) > 0 {
		caches := slices.Sorted(slices.Values(total.AnswerCaches))
		fmt.Fprintf(&b, "Answers of Z3 read from the answer cache: %s\n", strings.Join(caches, ", "))
		b.WriteString("  A proof that rests on them holds only if nothing but vego wrote there; run without -vego.cache to prove\n" +
			"  without them.\n\n")
	}
	b.WriteString(sizesReport(total.Sizes, relative))
	b.WriteString(inputsReport(total.Inputs, relative))
	section("Project contracts in use", false)
	section("Shipped contracts in use", true)
	// A state means what its declaration says; every entry that speaks of
	// it rests on that.
	var states []string
	for _, use := range entries {
		states = append(states, use.States...)
	}
	slices.Sort(states)
	states = slices.Compact(states)
	if len(states) > 0 {
		fmt.Fprintf(&b, "States the contracts in use speak of: %d\n", len(states))
		b.WriteString("  Each is about the goroutine that runs a verified function. A proof that reads one holds only if no other\n" +
			"  goroutine writes the memory the function uses while it runs, also while it waits in Lock, RLock, or Do,\n" +
			"  except to lock and unlock a mutex this goroutine does not hold or to call Do on a Once this goroutine is not\n" +
			"  inside Do on (what the function handed to that Do writes is not excepted); if nobody unlocks a mutex this\n" +
			"  goroutine holds; and if every call that waits for another goroutine returns.\n")
		for _, state := range states {
			name, reason, _ := strings.Cut(state, ": ")
			fmt.Fprintf(&b, "  %s\n    means:   %s\n", name, reason)
		}
		b.WriteString("\n")
	}
	var unused []string
	for _, file := range slices.Sorted(maps.Keys(total.ProjectKeys)) {
		for _, key := range total.ProjectKeys[file] {
			if !slices.ContainsFunc(entries, func(use *EntryUse) bool { return use.Key == key && use.File == file }) {
				unused = append(unused, fmt.Sprintf("  %s  (%s)", key, relative(file)))
			}
		}
	}
	fmt.Fprintf(&b, "Project contracts no proof uses: %d\n%s", len(unused), strings.Join(unused, "\n"))
	if len(unused) > 0 {
		b.WriteString("\n")
	}
	fmt.Fprintf(&b, "\nBuilt-in: errors.New and fmt.Errorf return a non-nil error.\n")
	if len(constructors) > 0 {
		fmt.Fprintf(&b, "    used at: %s\n", places(constructors))
	}
	return b.String()
}
