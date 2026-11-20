package trialfaults

import "os"

// Store reads what it holds, and its exported method calls back into
// Missing. The shipped entry of os.IsNotExist claims that it calls nothing
// that err holds, so handing it an error of unknown origin is no cycle.
type Store struct{ data []byte }

// Load is exported, and reaches Missing.
func (s Store) Load(err error) bool { return Missing(err) }

// @Ensures err = nil -> ~missing
func Missing(err error) (missing bool) {
	return os.IsNotExist(err)
}
