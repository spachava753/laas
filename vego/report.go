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
			if len(use.Vouches) > 0 {
				fmt.Fprintf(&b, "    vouches for the errors in: %s\n", strings.Join(use.Vouches, ", "))
			}
			fmt.Fprintf(&b, "    defined: %s:%d\n", relative(use.File), use.Line)
			fmt.Fprintf(&b, "    used at: %s\n", places(use.Calls))
		}
		b.WriteString("\n")
	}
	b.WriteString("vego trust report\n\n")
	b.WriteString("Every proof vego reports as successful holds only if the contracts below are true.\n")
	b.WriteString("None of them is checked against the code of the function it describes.\n\n")
	section("Project contracts in use", false)
	section("Shipped contracts in use", true)
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
