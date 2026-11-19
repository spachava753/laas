// Package closer closes the body of a response under a project entry for
// (io.Closer).Close, which vego does not ship.
package closer

import "net/http"

// @Requires resp != nil And resp.Body != nil
// @Ensures True
func Done(resp *http.Response) (c int) {
	defer resp.Body.Close()
	return resp.StatusCode
}
