package stdentries

import (
	"fmt"
	"os"
	"path"
	"path/filepath"
	"regexp"
	"strings"
)

// WriteFile writes a file, making its directory first.
//
// @Requires |name| <= 4096 And |data| <= 1000000
// @Ensures True
func WriteFile(name string, data []byte) (err error) {
	if err := os.MkdirAll(filepath.Dir(name), 0o755); err != nil {
		return fmt.Errorf("make the directory of %s: %w", name, err)
	}
	return os.WriteFile(name, data, 0o644)
}

// Leaf returns the last element of a slash-separated path.
//
// @Ensures 1 <= |leaf| And (|leaf| <= |p| Or leaf = ".")
func Leaf(p string) (leaf string) {
	return path.Base(p)
}

// IsHidden reports whether a file name starts with a dot. The base of an
// empty name is ".", so an empty name counts.
//
// @Ensures |name| = 0 -> result
func IsHidden(name string) (result bool) {
	base := filepath.Base(name)
	return len(base) > 0 && base[0] == '.'
}

// Kind returns the extension of a name, without its dot.
//
// @Ensures |kind| < |name| Or |name| = 0
func Kind(name string) (kind string) {
	ext := filepath.Ext(name)
	if ext == "" {
		return ""
	}
	return ext[1:]
}

// Rooted reports whether a slash-separated path is absolute.
//
// @Ensures result -> p[0] = '/'
func Rooted(p string) (result bool) {
	return path.IsAbs(p)
}

// Shorter claims that a cleaned path is no longer, which on Windows it can
// be.
//
// @Ensures |c| <= |p| Or c = "."
func Shorter(p string) (c string) {
	return filepath.Clean(p) // want `postcondition may not hold: \|c\| <= \|p\| Or c = "\."`
}

// Relative returns where target lies from base.
//
// @Requires |base| <= 4096 And |target| <= 4096
// @Ensures True
func Relative(base, target string) (rel string, err error) {
	rel, err = filepath.Rel(base, target)
	if err != nil {
		return "", fmt.Errorf("relative: %w", err)
	}
	return rel, nil
}

// Unquoted drops the quotes around a word.
//
// @Ensures |w| <= |s|
func Unquoted(s string) (w string) {
	return strings.TrimRight(strings.TrimLeft(s, `"`), `"`)
}

// Lines splits text after each newline.
//
// @Requires |text| <= 1000
// @Ensures |text| > 0 -> |lines| >= 1
func Lines(text string) (lines []string) {
	return strings.SplitAfter(text, "\n")
}

// Matches compiles a pattern and matches a line against it.
//
// @Requires |pattern| <= 1000
// @Ensures True
func Matches(pattern, line string) (ok bool, err error) {
	re, err := regexp.Compile(pattern)
	if err != nil {
		return false, fmt.Errorf("pattern %q: %w", pattern, err)
	}
	return re.MatchString(line), nil
}

// FirstWord finds the first word of a line.
//
// @Requires re != nil
// @Ensures |w| <= |line|
func FirstWord(re *regexp.Regexp, line string) (w string) {
	return re.FindString(line)
}

// Groups returns the groups of the first match.
//
// @Requires re != nil
// @Ensures Forall i in [0, |groups|) : |groups[i]| <= |line|
func Groups(re *regexp.Regexp, line string) (groups []string) {
	return re.FindStringSubmatch(line)
}

// MatchAny may be given a nil expression.
//
// @Ensures True
func MatchAny(re *regexp.Regexp, line string) (ok bool) {
	return re.MatchString(line) // want `precondition of MatchString may not hold: re != nil`
}

// Parent splits a slash-separated path into its directory and its last
// element.
//
// @Ensures |dir| + |file| = |p|
// @Ensures Forall k in [0, |file|) : file[k] != '/'
func Parent(p string) (dir, file string) {
	return path.Split(p)
}

// ParentClaimsTooMuch says the directory is never empty.
//
// @Ensures |dir| > 0
func ParentClaimsTooMuch(p string) (dir, file string) {
	return filepath.Split(p) // want `postcondition may not hold: \|dir\| > 0`
}
