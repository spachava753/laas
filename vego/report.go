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
	entries := map[string]*EntryUse{}
	projectKeys := map[string]string{} // entry -> the project file it is in
	var constructors []token.Position
	for _, usage := range usages {
		if usage == nil {
			continue
		}
		for _, key := range usage.ProjectKeys {
			projectKeys[key] = usage.ProjectFile
		}
		constructors = append(constructors, usage.Constructors...)
		for key, use := range usage.Entries {
			merged := entries[key]
			if merged == nil {
				copied := *use
				copied.Calls = nil
				merged = &copied
				entries[key] = merged
			}
			merged.Unpredictable = merged.Unpredictable || use.Unpredictable
			for _, call := range use.Calls {
				if !slices.Contains(merged.Calls, call) {
					merged.Calls = append(merged.Calls, call)
				}
			}
		}
	}
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
		var keys []string
		for _, key := range slices.Sorted(maps.Keys(entries)) {
			if entries[key].Shipped == shipped {
				keys = append(keys, key)
			}
		}
		fmt.Fprintf(&b, "%s: %d\n", title, len(keys))
		for _, key := range keys {
			use := entries[key]
			note := ""
			if use.Unpredictable {
				note = "  [may fail unpredictably]"
			}
			fmt.Fprintf(&b, "  %s%s\n", key, note)
			fmt.Fprintf(&b, "    reason:  %s\n", use.Reason)
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
	for _, key := range slices.Sorted(maps.Keys(projectKeys)) {
		if use := entries[key]; use == nil || use.Shipped {
			unused = append(unused, fmt.Sprintf("  %s  (%s)", key, relative(projectKeys[key])))
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
