package solver

import (
	"bufio"
	"fmt"
	"os"
	"strconv"
	"strings"
	"testing"
	"time"
)

// The test binary stands in for Z3 when VEGO_FAKE_Z3 is set, so that the
// tests can give the cache on disk chosen replies: a script cannot stand in
// there, since a cache needs the binary that answers. It reports the pinned
// version, and answers each problem with the lines of VEGO_FAKE_Z3 and each
// get-value with those of VEGO_FAKE_Z3_VALUES, in which {line} becomes the
// number of lines it has read. With VEGO_FAKE_Z3 set to "exit" it ends at
// once without reading anything. VEGO_FAKE_Z3_DELAY is a number of
// milliseconds it waits before it answers a problem.
func TestMain(m *testing.M) {
	if reply, ok := os.LookupEnv("VEGO_FAKE_Z3"); ok {
		fakeZ3(reply, os.Getenv("VEGO_FAKE_Z3_VALUES"))
		os.Exit(0)
	}
	os.Exit(m.Run())
}

func fakeZ3(reply, values string) {
	if len(os.Args) > 1 && os.Args[1] == "-version" {
		fmt.Println("Z3 version " + Version + " - 64 bit")
		return
	}
	if reply == "exit" {
		os.Exit(3)
	}
	in := bufio.NewScanner(os.Stdin)
	in.Buffer(nil, 1<<24)
	read, problem, asked := 0, false, false
	for in.Scan() {
		read++
		line := in.Text()
		problem = problem || strings.Contains(line, "(check-sat-using")
		asked = asked || strings.HasPrefix(line, "(get-value")
		i := strings.Index(line, `(echo "`)
		if i < 0 {
			continue
		}
		end := line[i+len(`(echo "`) : strings.LastIndex(line, `"`)]
		switch {
		case asked:
			fmt.Println(strings.ReplaceAll(values, "{line}", strconv.Itoa(read)))
		case problem:
			if delay, err := strconv.Atoi(os.Getenv("VEGO_FAKE_Z3_DELAY")); err == nil {
				time.Sleep(time.Duration(delay) * time.Millisecond)
			}
			fmt.Println(reply)
		}
		problem, asked = false, false
		fmt.Println(end)
	}
}

// fakeSolver returns a solver of its own whose processes are the test
// binary answering as VEGO_FAKE_Z3 says, keeping answers in dir.
func fakeSolver(t *testing.T, dir, reply, values string) (*Solver, error) {
	t.Helper()
	t.Setenv("VEGO_FAKE_Z3", reply)
	t.Setenv("VEGO_FAKE_Z3_VALUES", values)
	self, err := os.Executable()
	if err != nil {
		t.Fatal(err)
	}
	return opened(t, self, dir)
}
