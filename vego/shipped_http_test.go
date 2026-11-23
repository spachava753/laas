package vego

import (
	"bufio"
	"context"
	"crypto/tls"
	"fmt"
	"go/types"
	"io"
	"log"
	"math/rand"
	"net"
	"net/http"
	"net/http/httptest"
	"reflect"
	"slices"
	"strings"
	"sync"
	"testing"
	"unsafe"

	"github.com/spachava753/laas/vego/internal/logic"
)

// The entries of (net/http.ResponseWriter).Header, WriteHeader, and Write,
// and of http.Error and http.NotFound, are claims about every writer that
// a server hands a handler, and about what such a writer does to the
// request beside it. checkHTTPEntries holds them against three writers:
// httptest.ResponseRecorder, the writer of a real HTTP/1 server, and that
// of a real HTTP/2 server. A handler makes a random sequence of calls,
// each only when its requires holds, and around every call:
//
//   - everything reachable from the request without going through an
//     interface value, a function value, or a channel is printed before and
//     after, and must be the same, but for the hidden field Request.Trailer
//     (scoped.go), whose change is recorded: the separation that part 1
//     assumes of a handler's w and req;
//   - every object reachable from the writer after the call was reachable
//     from it before, or from nothing the harness held: the writer keeps
//     nothing it is handed, and grows only by memory it makes;
//   - the slice handed to Write is unchanged;
//   - the clauses of the entry under test hold, with within(result, w) of
//     Header told by whether the map is reachable from the writer.
//
// The clients send bodies that are chunked with trailers, declared and not,
// with Expect: 100-continue, under and over 256 KB, left unread and half
// read, so that a write that drains the body happens; the test fails unless
// some call on HTTP/1 was seen to change Request.Trailer, which is what the
// hidden declaration is for. On HTTP/2 the connection's goroutine writes
// the declared keys of the map while the handler runs, so the harness reads
// only the field there, not the map, which it would race with.

// httpKeys are the entries checkHTTPEntries runs.
var httpKeys = []string{
	"(net/http.ResponseWriter).Header", "(net/http.ResponseWriter).WriteHeader", "(net/http.ResponseWriter).Write",
	"net/http.Error", "net/http.NotFound",
}

// walkStop reports whether the walk of a writer stops at a pointer to a
// type: the server, the connection, and the stream, which other goroutines
// change while the handler runs and which the walk would race with. What
// the writer writes there is no memory verified code sees.
func walkStop(t reflect.Type) bool {
	switch t.Name() {
	case "Server", "serverConn", "conn", "stream", "connReader", "Transport", "persistConn", "Pool":
		return strings.HasPrefix(t.PkgPath(), "net/http") || t.PkgPath() == "sync"
	}
	return false
}

var requestType = reflect.TypeOf(http.Request{})

// memoryWalk walks what a value reaches: pointers, slices to their
// capacity, maps, struct fields, exported or not, and arrays. It stops at
// interface values, function values, channels, unsafe pointers, and
// pointers to types that stop says to. It prints what it sees, with the
// address of every object, and records each object's address. The field
// Trailer of a Request is printed into hidden instead, and its map is read
// only when readHidden is set.
type memoryWalk struct {
	stop       func(reflect.Type) bool
	readHidden bool
	objects    map[uintptr]bool
	print      strings.Builder
	hidden     strings.Builder
}

func newWalk(stop func(reflect.Type) bool, readHidden bool, roots ...any) *memoryWalk {
	w := &memoryWalk{stop: stop, readHidden: readHidden, objects: map[uintptr]bool{}}
	for _, root := range roots {
		v := reflect.ValueOf(root)
		if !v.IsValid() {
			continue
		}
		if v.Kind() == reflect.Interface {
			v = v.Elem()
		}
		w.value(&w.print, v, 0)
	}
	return w
}

// readable returns a value whose unexported fields can be read.
func readable(v reflect.Value) reflect.Value {
	if v.CanInterface() || !v.CanAddr() {
		return v
	}
	return reflect.NewAt(v.Type(), unsafe.Pointer(v.UnsafeAddr())).Elem()
}

func (w *memoryWalk) value(out *strings.Builder, v reflect.Value, depth int) {
	if depth > 60 {
		panic("the walk of a writer went too deep")
	}
	v = readable(v)
	switch v.Kind() {
	case reflect.Interface, reflect.Func, reflect.Chan, reflect.UnsafePointer:
		// Not followed; a change of what it holds is not a write of the
		// memory the separation is about.
		fmt.Fprintf(out, "<%s>", v.Kind())
	case reflect.Pointer:
		if v.IsNil() {
			out.WriteString("nil")
			return
		}
		at := v.Pointer()
		fmt.Fprintf(out, "&%x", at)
		if w.stop != nil && w.stop(v.Type().Elem()) {
			return
		}
		if w.objects[at] {
			return
		}
		w.objects[at] = true
		out.WriteString("{")
		w.value(out, v.Elem(), depth+1)
		out.WriteString("}")
	case reflect.Slice:
		if v.IsNil() {
			out.WriteString("nil")
			return
		}
		at := v.Pointer()
		fmt.Fprintf(out, "[%x %d %d:", at, v.Len(), v.Cap())
		first := !w.objects[at]
		w.objects[at] = true
		if first {
			for i := range v.Len() {
				w.value(out, v.Index(i), depth+1)
				out.WriteString(",")
			}
		}
		out.WriteString("]")
	case reflect.Map:
		if v.IsNil() {
			out.WriteString("nil")
			return
		}
		at := v.Pointer()
		fmt.Fprintf(out, "map %x", at)
		if w.objects[at] {
			return
		}
		w.objects[at] = true
		keys := v.MapKeys()
		slices.SortFunc(keys, func(a, b reflect.Value) int { return strings.Compare(fmt.Sprint(a), fmt.Sprint(b)) })
		out.WriteString("{")
		for _, k := range keys {
			fmt.Fprintf(out, "%v:", k)
			w.value(out, v.MapIndex(k), depth+1)
			out.WriteString(",")
		}
		out.WriteString("}")
	case reflect.Struct:
		out.WriteString("{")
		for i := range v.NumField() {
			field := v.Type().Field(i)
			if v.Type() == requestType && field.Name == "Trailer" {
				// The hidden field: its own value always, its map only
				// where reading it races with nothing.
				trailer := readable(v.Field(i))
				fmt.Fprintf(&w.hidden, "%x", trailer.Pointer())
				if w.readHidden && !trailer.IsNil() {
					keys := trailer.MapKeys()
					slices.SortFunc(keys, func(a, b reflect.Value) int { return strings.Compare(a.String(), b.String()) })
					for _, k := range keys {
						fmt.Fprintf(&w.hidden, " %s=%v", k, trailer.MapIndex(k))
					}
				}
				continue
			}
			fmt.Fprintf(out, "%s:", field.Name)
			w.value(out, v.Field(i), depth+1)
			out.WriteString(";")
		}
		out.WriteString("}")
	case reflect.Array:
		out.WriteString("[")
		for i := range v.Len() {
			w.value(out, v.Index(i), depth+1)
			out.WriteString(",")
		}
		out.WriteString("]")
	default:
		fmt.Fprintf(out, "%v", v)
	}
}

// httpRound is what one handler call checks, collected on the handler's
// goroutine and reported on the test's.
type httpRound struct {
	t       *testing.T
	pv      *pkgVerifier
	key     string
	fn      *funcInfo
	failure []string
	// calls counts the calls of the entry under test, and hidden the calls
	// on HTTP/1 after which Trailer had changed.
	calls, hidden int
	readHidden    bool
}

func (r *httpRound) fail(format string, args ...any) {
	r.failure = append(r.failure, fmt.Sprintf(format, args...))
}

// around makes one call of a sequence and checks what every call must
// keep: the request, what the writer reaches, and what it is handed.
func (r *httpRound) around(what string, w http.ResponseWriter, req *http.Request, handed []any, call func()) {
	reqBefore := newWalk(nil, r.readHidden, req)
	held := newWalk(nil, r.readHidden, append([]any{req}, handed...)...)
	writerBefore := newWalk(walkStop, r.readHidden, w)
	handedBefore := newWalk(nil, true, handed...)
	call()
	reqAfter := newWalk(nil, r.readHidden, req)
	if reqBefore.print.String() != reqAfter.print.String() {
		r.fail("%s changed memory that the request reaches:\nbefore %s\nafter  %s", what, reqBefore.print.String(), reqAfter.print.String())
	}
	if reqBefore.hidden.String() != reqAfter.hidden.String() && r.readHidden {
		r.hidden++
	}
	if before, after := handedBefore.print.String(), newWalk(nil, true, handed...).print.String(); before != after {
		r.fail("%s changed what it was handed:\nbefore %s\nafter  %s", what, before, after)
	}
	for at := range newWalk(walkStop, r.readHidden, w).objects {
		if !writerBefore.objects[at] && held.objects[at] {
			r.fail("%s made the writer reach %x, which the request or what the call was handed reached before", what, at)
		}
	}
}

// check evaluates the requires of the entry under test for a call with the
// given terms, and reports whether it holds.
func (r *httpRound) check(given map[*types.Var]*logic.Term) *sequenceCheck {
	return &sequenceCheck{t: r.t, pv: r.pv, fn: r.fn, given: given}
}

// sequence runs a random sequence of calls on a writer and its request.
func (r *httpRound) sequence(rng *rand.Rand, w http.ResponseWriter, req *http.Request) {
	defer func() {
		if p := recover(); p != nil {
			r.fail("a call panicked: %v", p)
		}
	}()
	wrote := false
	for range 1 + rng.Intn(6) {
		op := []string{"get", "set", "del", "(net/http.ResponseWriter).Header", "(net/http.ResponseWriter).WriteHeader",
			"(net/http.ResponseWriter).Write", "net/http.Error", "net/http.NotFound", "read"}[rng.Intn(9)]
		if rng.Intn(3) == 0 {
			op = r.key
		}
		switch op {
		case "read":
			// Code that is not verified reads part of the body.
			io.CopyN(io.Discard, req.Body, int64(rng.Intn(70000)))
		case "get":
			h := w.Header()
			r.around("Header().Get", w, req, nil, func() { h.Get("Content-Type") })
		case "set":
			h := w.Header()
			r.around("Header().Set", w, req, nil, func() { h.Set(randomHeaderKey(rng), "text/plain") })
		case "del":
			h := w.Header()
			r.around("Header().Del", w, req, nil, func() { h.Del(randomHeaderKey(rng)) })
		case "(net/http.ResponseWriter).Header":
			var m http.Header
			r.around("Header", w, req, nil, func() { m = w.Header() })
			if op == r.key {
				r.calls++
				c := r.check(map[*types.Var]*logic.Term{r.fn.receiver: reference(false)})
				c.results = []*logic.Term{reference(m == nil)}
				within := m != nil && newWalk(walkStop, r.readHidden, w).objects[reflect.ValueOf(m).Pointer()]
				c.within = map[*types.Var]bool{r.fn.results[0]: within}
				if !c.holds(r.fn.ensures) {
					r.fail("the ensures of Header is false: nil %v, reachable from the writer %v", m == nil, within)
				}
				if newWalk(nil, r.readHidden, req).objects[reflect.ValueOf(m).Pointer()] {
					r.fail("the map that Header returned is reachable from the request")
				}
			}
		case "(net/http.ResponseWriter).WriteHeader":
			code := []int{100, 103, 200, 201, 204, 304, 400, 404, 500, 599, 600, 999}[rng.Intn(12)]
			if op == r.key {
				if !r.check(map[*types.Var]*logic.Term{r.fn.receiver: reference(false), r.fn.params[0]: logic.IntLit(int64(code))}).holds(r.fn.requires) {
					continue
				}
				r.calls++
			}
			r.around(fmt.Sprintf("WriteHeader(%d)", code), w, req, nil, func() { w.WriteHeader(code) })
			wrote = wrote || code >= 200
		case "(net/http.ResponseWriter).Write":
			// Empty, small, past the 2 KB a writer buffers before it
			// flushes its header, and past 64 KB.
			p := make([]byte, []int{0, 5, 4096, 70000}[rng.Intn(4)])
			if op == r.key {
				r.calls++
			}
			r.around(fmt.Sprintf("Write of %d bytes", len(p)), w, req, []any{p}, func() { w.Write(p) })
			wrote = true
		case "net/http.Error":
			msg := strings.Repeat("e", []int{0, 10, 3000, 70000}[rng.Intn(4)])
			code := []int{200, 400, 404, 500, 999}[rng.Intn(5)]
			if op == r.key {
				given := map[*types.Var]*logic.Term{r.fn.params[0]: reference(false), r.fn.params[1]: lengthTerm(len(msg)), r.fn.params[2]: logic.IntLit(int64(code))}
				if !r.check(given).holds(r.fn.requires) {
					continue
				}
				r.calls++
			}
			r.around("Error", w, req, nil, func() { http.Error(w, msg, code) })
		case "net/http.NotFound":
			if op == r.key {
				r.calls++
			}
			r.around("NotFound", w, req, nil, func() { http.NotFound(w, req) })
		}
	}
	_ = wrote
}

// randomHeaderKey returns a key a header may hold.
func randomHeaderKey(rng *rand.Rand) string {
	return []string{"Content-Type", "Content-Length", "x-custom", "Trailer", "X-Sum"}[rng.Intn(5)]
}

// sendRandom sends one request to a server: a method, and a body that is
// absent, small, chunked with a declared trailer, chunked with Expect:
// 100-continue, or over 256 KB.
func sendRandom(rng *rand.Rand, client *http.Client, url string) {
	method := []string{"GET", "POST", "HEAD", "PUT"}[rng.Intn(4)]
	var body io.Reader
	length := int64(0)
	var trailer http.Header
	expect := false
	switch rng.Intn(5) {
	case 1:
		body, length = strings.NewReader("small"), 5
	case 2:
		body, length = io.MultiReader(strings.NewReader(strings.Repeat("c", 3000))), -1
		trailer = http.Header{"X-Sum": {"7"}}
	case 3:
		body, length = io.MultiReader(strings.NewReader(strings.Repeat("c", 100))), -1
		trailer = http.Header{"X-Sum": {"8"}}
		expect = true
	case 4:
		body, length = strings.NewReader(strings.Repeat("b", 300000)), 300000
	}
	req, err := http.NewRequestWithContext(context.Background(), method, url, body)
	if err != nil {
		panic(err)
	}
	req.ContentLength = length
	req.Trailer = trailer
	if expect {
		req.Header.Set("Expect", "100-continue")
	}
	resp, err := client.Do(req)
	if err == nil {
		io.Copy(io.Discard, resp.Body)
		resp.Body.Close()
	}
}

// sendUndeclared sends an HTTP/1 request by hand whose chunked body ends
// with a trailer the request did not declare.
func sendUndeclared(addr string) {
	c, err := net.Dial("tcp", addr)
	if err != nil {
		return
	}
	defer c.Close()
	fmt.Fprintf(c, "POST / HTTP/1.1\r\nHost: x\r\nTransfer-Encoding: chunked\r\nConnection: close\r\n\r\n5\r\nhello\r\n0\r\nX-Late: 1\r\n\r\n")
	bufio.NewReader(c).ReadString(0)
}

// checkHTTPEntries runs the entries of the writer of a handler.
func checkHTTPEntries(t *testing.T, pv *pkgVerifier, pkg *types.Package, key string) {
	var fn *funcInfo
	if strings.HasPrefix(key, "(net/http.ResponseWriter).") {
		_, name, _ := splitFuncName(key)
		fn = shippedTypeContract(pv, pkg, name)
	} else {
		fn = contractOfKey(t, pv, pkg, key)
	}
	if fn == nil {
		t.Fatalf("%s has no shipped contract", key)
	}
	for _, defect := range fn.defects {
		t.Errorf("the contract of %s cannot be used: %s", key, defect)
	}
	rng := rand.New(rand.NewSource(28))
	var mu sync.Mutex
	round := &httpRound{t: t, pv: pv, key: key, fn: fn}
	report := func(where string) {
		mu.Lock()
		defer mu.Unlock()
		for _, f := range round.failure {
			t.Errorf("%s: %s", where, f)
		}
		round.failure = nil
	}
	// The recorder.
	for range 150 {
		req := httptest.NewRequest("POST", "/", strings.NewReader(strings.Repeat("r", rng.Intn(5000))))
		round.readHidden = true
		round.sequence(rng, httptest.NewRecorder(), req)
	}
	report("httptest.ResponseRecorder")
	// A real server of each protocol.
	sawTwo := false
	for _, two := range []bool{false, true} {
		server := httptest.NewUnstartedServer(http.HandlerFunc(func(w http.ResponseWriter, req *http.Request) {
			mu.Lock()
			defer mu.Unlock()
			if req.ProtoMajor == 2 {
				sawTwo = true
			}
			round.readHidden = req.ProtoMajor == 1
			round.sequence(rand.New(rand.NewSource(rng.Int63())), w, req)
		}))
		server.Config.ErrorLog = log.New(io.Discard, "", 0)
		if two {
			server.EnableHTTP2 = true
			server.StartTLS()
		} else {
			server.Start()
		}
		client := server.Client()
		if two {
			client.Transport.(*http.Transport).TLSClientConfig = &tls.Config{InsecureSkipVerify: true}
			client.Transport.(*http.Transport).ForceAttemptHTTP2 = true
		}
		for i := range 150 {
			sendRandom(rng, client, server.URL)
			if !two && i%10 == 0 {
				sendUndeclared(server.Listener.Addr().String())
			}
		}
		server.Close()
		report(map[bool]string{false: "the HTTP/1 server", true: "the HTTP/2 server"}[two])
	}
	if !sawTwo {
		t.Errorf("no request reached the handler over HTTP/2")
	}
	if round.calls == 0 {
		t.Errorf("no call of %s was made", key)
	}
	if key == "(net/http.ResponseWriter).Write" && round.hidden == 0 {
		t.Errorf("no write was seen to change Request.Trailer, which the hidden declaration is about; send bodies that the writer drains")
	}
}

// TestStatusTextBound enumerates the codes the entry of http.StatusText
// bounds, and more, against the bound of its ensures.
func TestStatusTextBound(t *testing.T) {
	parallel(t)
	for code := -1000; code <= 2000; code++ {
		if text := http.StatusText(code); len(text) > 31 {
			t.Errorf("StatusText(%d) is %q, %d bytes, more than the 31 its entry says", code, text, len(text))
		}
	}
}

// keepingWriter keeps what Write is handed, and touchingWriter writes the
// request beside it: the two ways around must catch.
type keepingWriter struct {
	*httptest.ResponseRecorder
	kept []byte
}

func (k *keepingWriter) Write(p []byte) (int, error) { k.kept = p; return len(p), nil }

type touchingWriter struct {
	*httptest.ResponseRecorder
	req *http.Request
}

func (w *touchingWriter) Write(p []byte) (int, error) { w.req.URL.Path += "x"; return len(p), nil }

// TestHTTPHarnessCatches shows that the checks every call of the writer
// harness makes fail on a writer that keeps what it is handed and on one
// that writes the request.
func TestHTTPHarnessCatches(t *testing.T) {
	parallel(t)
	for _, c := range []struct {
		name string
		w    func(req *http.Request) http.ResponseWriter
	}{
		{"keeps p", func(*http.Request) http.ResponseWriter { return &keepingWriter{ResponseRecorder: httptest.NewRecorder()} }},
		{"writes req", func(req *http.Request) http.ResponseWriter { return &touchingWriter{httptest.NewRecorder(), req} }},
	} {
		req := httptest.NewRequest("GET", "/a", nil)
		w := c.w(req)
		round := &httpRound{t: t, readHidden: true}
		p := []byte("data")
		round.around("Write", w, req, []any{p}, func() { w.Write(p) })
		if len(round.failure) == 0 {
			t.Errorf("a writer that %s passes the harness", c.name)
		}
	}
}

// storesRuns makes, for each shipped entry with stores, a call on a header
// h with what the call is handed besides h; checkStores holds the claim.
var storesRuns = map[string]func(h http.Header, rng *rand.Rand) (held []any, call func()){
	"(net/http.Header).Set": func(h http.Header, rng *rand.Rand) ([]any, func()) {
		key, value := randomHeaderKey(rng), []string{"", "v", "text/plain"}[rng.Intn(3)]
		return []any{key, value}, func() { h.Set(key, value) }
	},
	"(net/http.Header).Del": func(h http.Header, rng *rand.Rand) ([]any, func()) {
		key := randomHeaderKey(rng)
		return []any{key}, func() { h.Del(key) }
	},
}

// checkStores holds the claim of stores of a call on h: every object that h
// reaches after the call and did not before is one that nothing the harness
// held reached, and is not one that the same call on another header made
// reachable, which memory of the function's package would be.
func checkStores(rng *rand.Rand, run func(h http.Header, rng *rand.Rand) (held []any, call func())) error {
	seed := rng.Int63()
	made := func() (map[uintptr]bool, map[uintptr]bool) {
		h := http.Header{"Content-Type": {"text/html"}, "X-Sum": make([]string, 1, 4)}
		held, call := run(h, rand.New(rand.NewSource(seed)))
		before := newWalk(nil, true, h).objects
		was := newWalk(nil, true, append([]any{h}, held...)...).objects
		call()
		added := map[uintptr]bool{}
		for at := range newWalk(nil, true, h).objects {
			if !before[at] {
				added[at] = true
				if was[at] {
					return nil, added
				}
			}
		}
		return added, nil
	}
	first, stale := made()
	if stale != nil {
		return fmt.Errorf("the call stored into h memory that the harness held before")
	}
	second, stale := made()
	if stale != nil {
		return fmt.Errorf("the call stored into h memory that the harness held before")
	}
	for at := range first {
		if second[at] {
			return fmt.Errorf("two calls stored into h the same memory, which neither made")
		}
	}
	return nil
}

// stored is package state that a function that breaks stores writes.
var stored = []string{"kept"}

// TestStoresClaims holds the claim of every shipped entry that lists
// stores, and shows the check failing on a function that stores its
// argument and on one that stores package state.
func TestStoresClaims(t *testing.T) {
	parallel(t)
	for _, file := range shippedContracts() {
		for key, entry := range file.entries {
			if len(entry.stores) == 0 {
				continue
			}
			run := storesRuns[key]
			if run == nil {
				t.Errorf("no run checks the stores of %s; add one to storesRuns", key)
				continue
			}
			rng := rand.New(rand.NewSource(28))
			for range 200 {
				if err := checkStores(rng, run); err != nil {
					t.Errorf("%s: %v", key, err)
					break
				}
			}
		}
	}
	argument := []string{"handed"}
	for name, run := range map[string]func(h http.Header, rng *rand.Rand) ([]any, func()){
		"stores its argument": func(h http.Header, _ *rand.Rand) ([]any, func()) {
			return []any{argument}, func() { h["X"] = argument }
		},
		"stores package state": func(h http.Header, _ *rand.Rand) ([]any, func()) {
			return nil, func() { h["X"] = stored }
		},
	} {
		if checkStores(rand.New(rand.NewSource(1)), run) == nil {
			t.Errorf("a function that %s passes the check of stores", name)
		}
	}
}
