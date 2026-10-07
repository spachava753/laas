package main

import (
	"strings"
	"testing"
)

func TestInspect(t *testing.T) {
	tests := []struct {
		name   string
		source string
		symbol string
		kind   string
		keys   []string
	}{
		{"generic function", "package p\n// Copy returns x.\nfunc Copy[T any](x T) T { return x }\n", "Copy", "function", []string{"$doc"}},
		{"generic pointer method", "package p\ntype Box[T any] struct{}\n// Get gets a value.\nfunc (b *Box[T]) Get() {}\n", "Box.Get", "method", []string{"$doc"}},
		{"grouped type", "package p\ntype (\n// Name identifies a person.\nName string\nOther int\n)\n", "Name", "type", []string{"$doc"}},
		{"struct fields and UTF-8", "package p\n// Options configures café.\ntype Options struct {\n// Name identifies a user.\nName string // UTF-8 café.\n// Count bounds results.\nCount int\n}\n", "Options", "struct", []string{"$doc", "Name", "Count"}},
		{"interface", "package p\n// Reader reads.\ntype Reader interface {\n// Read reads once.\nRead()\n}\n", "Reader", "type", []string{"$doc"}},
	}
	for _, test := range tests {
		t.Run(test.name, func(t *testing.T) {
			source := []byte(test.source)
			got, err := inspect(source, test.symbol)
			if err != nil {
				t.Fatal(err)
			}
			if got.Kind != test.kind || len(got.Docs) != len(test.keys) {
				t.Fatalf("unexpected target: %+v", got)
			}
			for _, key := range test.keys {
				if got.Docs[key].Text == "" {
					t.Fatalf("missing doc for %s", key)
				}
			}
			masked := append([]byte(nil), source...)
			for _, r := range got.Ranges {
				for i := r.Start; i < r.End; i++ {
					if masked[i] != '\n' {
						masked[i] = ' '
					}
				}
			}
			stripped, err := inspect(masked, test.symbol)
			if err != nil {
				t.Fatal(err)
			}
			if got.Fingerprint != stripped.Fingerprint {
				t.Fatal("stripping documentation changed non-documentation tokens")
			}
			for key, doc := range stripped.Docs {
				if doc.Text != "" {
					t.Fatalf("doc for %s was not stripped", key)
				}
			}
			changed := strings.Replace(test.source, "package p", "package other", 1)
			other, err := inspect([]byte(changed), test.symbol)
			if err != nil || got.Fingerprint == other.Fingerprint {
				t.Fatal("code change was not detected")
			}
		})
	}
	t.Run("unrelated comment preserved", func(t *testing.T) {
		source := "package p\n// Stable explains another function.\nfunc Stable() {}\n// Target documents the target.\nfunc Target() {}\n"
		before, err := inspect([]byte(source), "Target")
		if err != nil {
			t.Fatal(err)
		}
		after, err := inspect([]byte(strings.Replace(source, "explains", "changes", 1)), "Target")
		if err != nil || before.Fingerprint == after.Fingerprint {
			t.Fatal("unrelated comment change was not detected")
		}
	})
	t.Run("invalid targets", func(t *testing.T) {
		for _, source := range []string{
			"package p\nfunc Other() {}",
			"package p\nfunc Target() {}\nfunc Target() {}",
			"package p\n// Shared types.\ntype (Target int; Other int)",
			"package p\n// Target does work.\n//go:nosplit\nfunc Target() {}",
			"package p\nfunc Target( {",
		} {
			if _, err := inspect([]byte(source), "Target"); err == nil {
				t.Fatalf("accepted invalid target: %s", source)
			}
		}
	})
}
