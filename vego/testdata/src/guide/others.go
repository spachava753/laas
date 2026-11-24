package guide

import "guidehandler"

// Handle serves a request named path.
//
// @Modifies guidehandler
// @Ensures True
func Handle(path string) {
	guidehandler.Serve()
}

// HandleByPath lists the state of guidestats by its import path.
//
// @Modifies "guidestats"
// @Ensures True
func HandleByPath(path string) {
	guidehandler.Serve()
}

// HandleUnlisted does not list what Serve changes.
//
// @Ensures True
func HandleUnlisted(path string) {
	guidehandler.Serve() // want `^vego: Serve may modify the state of package guidestats \(guidestats.requests\), which HandleUnlisted may not modify; list guidehandler, whose state includes it, in a // @Modifies clause$`
}
