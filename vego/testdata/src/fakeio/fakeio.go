// Package fakeio has an EOF of its own.
package fakeio

import "errors"

var EOF = errors.New("fake eof")
