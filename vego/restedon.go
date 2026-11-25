package vego

import (
	"fmt"
	"strings"
)

// Shipped entries rest on the shipped entries of some methods of
// interfaces, in two directions (S0 of F35). An entry whose code calls the
// method on what it is handed, as (*bufio.Writer).Write calls Write of the
// writer it keeps, is true only of values whose method meets the shipped
// entry of that method: one that verified code checked against a weaker
// replacement in the trust file of the project breaks it. And an entry that
// vouches for a value of the interface it returns, as io.NopCloser vouches
// that the Close of its result meets the entry of (io.Closer).Close, is
// true only of an entry that promises no more than the code of the result
// delivers: a replacement that promises more breaks it.
//
// So a project entry for one of these keys must be the shipped entry
// itself; its reason may differ, and nothing else (projectReplaces). One
// that differs is reported at its line of the trust file in every package
// that reads the file, and the shipped entry is used in its place
// (entryFor), so that no shipped entry rests on it unseen and no other
// entry draws a defect from it (F11 and F12 of the review of S0). Adding
// vouches alone, with each shipped wrapper saying which keys the errors of
// its result are drawn from, is the way to let a project vouch for the
// errors of Read and Write, and is not built (see the roadmap).
//
// restedOn lists the keys, each with a shipped entry that rests on it and
// how, as messages name it. TestRestedOn computes the keys from the
// shipped files and the types of the toolchain, in both directions, and
// fails when this table differs.
var restedOn = map[string]string{
	"(io.Writer).Write":                     "(*bufio.Writer).Write calls it on the writer it keeps",
	"(io.Reader).Read":                      "bufio.NewScanner keeps a reader whose Read the Scanner calls",
	"(io.Closer).Close":                     "io.NopCloser vouches that the Close of its result meets it",
	"(net/http.ResponseWriter).Header":      "net/http.Error calls it on its writer",
	"(net/http.ResponseWriter).Write":       "net/http.Error calls it on its writer through fmt.Fprintln",
	"(net/http.ResponseWriter).WriteHeader": "net/http.Error calls it on its writer",
}

// shippedEntry returns the shipped entry for a key, or nil.
func shippedEntry(key string) *trustEntry {
	for _, file := range shippedContracts() {
		if entry := file.entries[key]; entry != nil {
			return entry
		}
	}
	return nil
}

// projectReplaces describes how a project entry for a key that shipped
// entries rest on differs from the shipped entry, or returns "" when it
// does not replace one or is the same entry. Every field the entry reads is
// compared, by its text and in order; the reason may differ.
func projectReplaces(entry *trustEntry) string {
	if entry == nil || entry.file == nil || entry.file.shipped {
		return ""
	}
	resting, ok := restedOn[entry.key]
	if !ok {
		return ""
	}
	shipped := shippedEntry(entry.key)
	if shipped == nil {
		return ""
	}
	mine, theirs := entry.fingerprint(), shipped.fingerprint()
	if mine == theirs {
		return ""
	}
	said := func(text string) string {
		if text == "" {
			return "modifies: [] and nothing more"
		}
		return strings.ReplaceAll(text, "\n", "; ")
	}
	return fmt.Sprintf("the entry of %s replaces the shipped entry, on which shipped entries rest (%s), and it differs from it; "+
		"those entries are true only of values whose method meets the shipped entry, and of an entry that promises no more than the code they vouch for delivers, "+
		"so a replacement must be the shipped entry itself, with a reason of its own, and the shipped entry is used in its place; it says %s, and the shipped entry says %s",
		entry.key, resting, said(mine), said(theirs))
}
