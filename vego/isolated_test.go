package vego

import (
	"bytes"
	"errors"
	"go/importer"
	"go/token"
	"go/types"
	"slices"
	"strconv"
	"strings"
	"testing"
	"unicode"
	"unicode/utf8"
)

// isolatedHooks lists, for each package with a shipped entry that claims to
// be isolated, every hook the package exposes: an exported package-level
// variable whose type can hold code, and an exported function whose name
// says that it sets or registers something. Nothing else that the package
// exports can be set by another call. TestIsolatedHooks holds the lists
// against the toolchain, and runs each isolated function with every hook
// set to a value whose methods fail the test.
var isolatedHooks = map[string][]string{
	"bytes":        {"ErrTooLarge"},
	"fmt":          nil,
	"math":         nil,
	"strconv":      {"ErrRange", "ErrSyntax"},
	"strings":      nil,
	"sync":         nil,
	"unicode":      nil,
	"unicode/utf8": nil,
}

// hookError is an error whose methods fail the test that set it as a hook.
type hookError struct{ t *testing.T }

// Error fails the test: an isolated function ran a hook.
func (e hookError) Error() string {
	e.t.Error("an isolated function ran the Error method of a hook")
	return "hook"
}

// TestIsolatedHooks checks the claim of the shipped entries marked
// isolated, that the function runs no code but what the call hands it, as
// far as a run can (F11 of the review of the design of F32). It lists the
// hooks each such package exposes, and fails when the list differs from
// isolatedHooks, so that a new hook is read before the claim stays. Then
// it sets each hook to a value whose methods fail the test, and runs the
// functions that could reach it, also on the inputs that return those
// errors. It changes package-level variables of the standard library, so
// it runs alone.
func TestIsolatedHooks(t *testing.T) {
	alone(t)
	imports := importer.ForCompiler(token.NewFileSet(), "source", nil)
	marked := map[string]bool{}
	for _, file := range shippedContracts() {
		for key, entry := range file.entries {
			if !entry.isIsolated() {
				continue
			}
			// The package of strings.Contains or of (*sync.Mutex).Lock.
			name := key
			if strings.HasPrefix(key, "(") {
				name = strings.TrimPrefix(key[1:strings.Index(key, ")")], "*")
			}
			marked[name[:strings.LastIndex(name, ".")]] = true
		}
	}
	for path := range marked {
		want, listed := isolatedHooks[path]
		if !listed {
			t.Errorf("package %s has entries marked isolated, and isolatedHooks does not list its hooks", path)
			continue
		}
		pkg, err := imports.Import(path)
		if err != nil {
			t.Fatalf("import %s: %v", path, err)
		}
		var hooks []string
		for _, name := range pkg.Scope().Names() {
			obj := pkg.Scope().Lookup(name)
			if !obj.Exported() {
				continue
			}
			switch obj := obj.(type) {
			case *types.Var:
				if holdsCode(obj.Type(), map[types.Type]bool{}) {
					hooks = append(hooks, name)
				}
			case *types.Func:
				if strings.HasPrefix(name, "Set") || strings.HasPrefix(name, "Register") {
					hooks = append(hooks, name)
				}
			}
		}
		if !slices.Equal(hooks, want) {
			t.Errorf("package %s exposes the hooks %v, and isolatedHooks lists %v; read what its isolated functions do with each before changing the list", path, hooks, want)
		}
	}
	for path := range isolatedHooks {
		if !marked[path] {
			t.Errorf("isolatedHooks lists package %s, which has no entry marked isolated", path)
		}
	}

	// Each hook set to an error whose methods fail the test.
	hook := hookError{t}
	savedTooLarge, savedRange, savedSyntax := bytes.ErrTooLarge, strconv.ErrRange, strconv.ErrSyntax
	bytes.ErrTooLarge, strconv.ErrRange, strconv.ErrSyntax = hook, hook, hook
	defer func() { bytes.ErrTooLarge, strconv.ErrRange, strconv.ErrSyntax = savedTooLarge, savedRange, savedSyntax }()

	var b bytes.Buffer
	b.Grow(16)
	b.WriteString("ab")
	b.WriteByte('c')
	b.WriteRune('é')
	_, _ = b.Write([]byte("d"))
	_ = b.Len() + len(b.String()) + len(b.Bytes())
	b.Truncate(1)
	b.Reset()
	_ = bytes.Contains([]byte("abc"), []byte("b"))
	_ = bytes.Map(unicode.ToUpper, []byte("abc"))

	var sb strings.Builder
	sb.Grow(16)
	sb.WriteString("ab")
	sb.WriteByte('c')
	sb.WriteRune('é')
	_, _ = sb.Write([]byte("d"))
	_ = sb.Len() + len(sb.String())
	sb.Reset()

	for _, s := range []string{"x", "99999999999999999999", "-99999999999999999999", "12"} {
		if _, err := strconv.Atoi(s); err != nil && !errors.Is(err, hook) {
			t.Errorf("strconv.Atoi(%q) returned %v, which does not wrap the hook", s, err)
		}
		_, _ = strconv.ParseInt(s, 10, 64)
		_, _ = strconv.ParseUint(s, 10, 64)
	}
	_, _ = strconv.ParseBool("x")
	_, _ = strconv.Unquote("x")
	_ = strconv.Quote("a\x00") + strconv.Itoa(-3) + strconv.FormatInt(7, 2)
	_ = strconv.AppendInt(nil, 5, 10)
	_ = utf8.RuneCountInString("aé") + utf8.RuneLen('é')
	_ = unicode.IsSpace(' ')
}
