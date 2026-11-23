//go:build !goexperiment.jsonv2

package main

import "runtime"

func build() string { return runtime.Version() + " v1" }
