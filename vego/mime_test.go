package vego

import (
	"fmt"
	"mime"
	"runtime"
	"strings"
	"testing"
)

// TestMediaTypeBound measures what mime.ParseMediaType allocates on the
// worst shapes of a value, against the requires of its shipped entry,
// 32 * (|v| + 1) + 65536 bytes: a media type of invalid bytes, each of
// which lowercasing makes three, many parameters with one-byte keys and
// values, many uppercase keys, and RFC 2231 continuations of one value.
func TestMediaTypeBound(t *testing.T) {
	alone(t)
	var continued, distinct strings.Builder
	continued.WriteString("a/b")
	for i := range 20000 {
		fmt.Fprintf(&continued, "; x*%d=v", i)
	}
	distinct.WriteString("a/b")
	for i := range 30000 {
		fmt.Fprintf(&distinct, "; K%d=v", i)
	}
	shapes := map[string]string{
		"invalid bytes":  strings.Repeat("\xff", 200000),
		"parameters":     "a/b" + strings.Repeat("; a=b", 40000),
		"distinct keys":  distinct.String(),
		"continuations":  continued.String(),
		"encoded pieces": "a/b; x*=utf-8''" + strings.Repeat("%41", 60000),
	}
	for name, v := range shapes {
		var before, after runtime.MemStats
		runtime.GC()
		runtime.ReadMemStats(&before)
		_, _, _ = mime.ParseMediaType(v)
		runtime.ReadMemStats(&after)
		allocated := after.TotalAlloc - before.TotalAlloc
		bound := uint64(32*(len(v)+1) + 65536)
		if allocated > bound {
			t.Errorf("%s: ParseMediaType of %d bytes allocated %d bytes, more than the entry's bound of %d", name, len(v), allocated, bound)
		}
		t.Logf("%s: %d bytes of value, %d allocated, %.1f per byte", name, len(v), allocated, float64(allocated)/float64(len(v)))
	}
}
