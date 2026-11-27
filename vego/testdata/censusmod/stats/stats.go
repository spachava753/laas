// Package stats is the example of the census in docs/verification.md.
package stats

import (
	"os"
	"strings"
)

func count(xs []int) int { return len(xs) }

func Mean(xs []int) int {
	if count(xs) == 0 {
		return 0
	}
	total := 0
	for _, x := range xs {
		total += x
	}
	return total / count(xs)
}

func Load(name string) (string, error) {
	info, err := os.Stat(name)
	if err != nil {
		return "", err
	}
	return strings.TrimSpace(info.Name()), nil
}

func Pump(xs []int) chan int {
	ch := make(chan int)
	go func() {
		for _, x := range xs {
			ch <- x
		}
	}()
	return ch
}
