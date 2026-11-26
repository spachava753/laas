package vego

import (
	"embed"
	"io/fs"
	"math/rand"
	"os"
	"testing/fstest"
	"time"
)

// embedded is what the harnesses of embed.FS read: two packages of the
// corpus, a directory each with files.
//
//go:embed testdata/src/semantics testdata/src/guide
var embedded embed.FS

// embeddedNames are names the harnesses of embed.FS look up: files,
// directories, a name that is not there, and names that are not valid.
var embeddedNames = []string{"testdata/src/guide/guide.go", "testdata/src/guide", "testdata/src", ".", "testdata/absent", "../x", "", "testdata//src"}

// randomMode returns a file mode with random type and permission bits.
func randomMode(rng *rand.Rand) fs.FileMode {
	types := []fs.FileMode{0, fs.ModeDir, fs.ModeSymlink, fs.ModeNamedPipe, fs.ModeSocket, fs.ModeDevice | fs.ModeCharDevice, fs.ModeIrregular}
	return types[rng.Intn(len(types))] | fs.FileMode(rng.Intn(0o1000))
}

func init() {
	harnesses["(io/fs.FileMode).IsDir"] = func(rng *rand.Rand) sample {
		m := randomMode(rng)
		return sample{before: []any{m}, after: []any{m}, results: []any{m.IsDir()}}
	}
	harnesses["(io/fs.FileMode).IsRegular"] = func(rng *rand.Rand) sample {
		m := randomMode(rng)
		return sample{before: []any{m}, after: []any{m}, results: []any{m.IsRegular()}}
	}
	harnesses["(io/fs.FileMode).Type"] = func(rng *rand.Rand) sample {
		m := randomMode(rng)
		return sample{before: []any{m}, after: []any{m}, results: []any{m.Type()}}
	}
	harnesses["(embed.FS).ReadFile"] = func(rng *rand.Rand) sample {
		name := embeddedNames[rng.Intn(len(embeddedNames))]
		before := snapshot(embedded, name)
		data, err := embedded.ReadFile(name)
		return sample{before: before, after: []any{embedded, name}, results: []any{data, err}}
	}
	entries := []implementation{
		{"os.ReadDir's", dirEntryHarness(func(rng *rand.Rand) []fs.DirEntry {
			list, _ := os.ReadDir([]string{".", "testdata", "testdata/src/inputs", "/proc/self"}[rng.Intn(4)])
			return list
		})},
		{"embed.FS's", dirEntryHarness(func(rng *rand.Rand) []fs.DirEntry {
			list, _ := embedded.ReadDir([]string{".", "testdata/src", "testdata/src/guide"}[rng.Intn(3)])
			return list
		})},
		{"fs.FileInfoToDirEntry's", dirEntryHarness(func(rng *rand.Rand) []fs.DirEntry {
			var list []fs.DirEntry
			for _, name := range []string{".", "inputs.go", "/dev/null"} {
				if info, err := os.Lstat(name); err == nil {
					list = append(list, fs.FileInfoToDirEntry(info))
				}
			}
			return list
		})},
		{"fstest.MapFS's", dirEntryHarness(func(rng *rand.Rand) []fs.DirEntry {
			fsys := fstest.MapFS{"a": {Data: []byte("x")}, "d/b": {Mode: 0o644, ModTime: time.Unix(1, 0)}}
			list, _ := fs.ReadDir(fsys, []string{".", "d"}[rng.Intn(2)])
			return list
		})},
	}
	for _, key := range []string{"(io/fs.DirEntry).Name", "(io/fs.DirEntry).IsDir", "(io/fs.DirEntry).Type"} {
		typeHarnesses[key] = entries
	}
}

// dirEntryHarness calls one method of an entry of a directory that list
// gives, by the method of the key the harness runs for; each method takes
// nothing and writes nothing, so every method is called.
func dirEntryHarness(list func(rng *rand.Rand) []fs.DirEntry) func(rng *rand.Rand) sample {
	return func(rng *rand.Rand) sample {
		entries := list(rng)
		if len(entries) == 0 {
			return sample{results: []any{""}}
		}
		d := entries[rng.Intn(len(entries))]
		_, _, _ = d.Name(), d.IsDir(), d.Type()
		return sample{}
	}
}
