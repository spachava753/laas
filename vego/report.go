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
			if len(use.Formats) > 0 {
				fmt.Fprintf(&b, "    formats as package fmt does: %s; a claim that it runs only the Format, GoString, Error, and String methods "+
					"that fmt runs, while the call lasts and on the goroutine that called it, keeps none of the values, and builds from them "+
					"at most 4096 bytes more than fmt prints for them, apart from what a logger adds from its own settings\n", strings.Join(use.Formats, ", "))
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
