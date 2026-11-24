package chainclash

// Clash names rand, which the files of the package import as two
// packages, and this file imports neither.
//
// @Modifies rand // want `^vego: in Modifies annotation: rand names more than one package in the files of this package \("crypto/rand" and "math/rand"\), and the file of Clash imports none of them; write the import path, as // @Modifies "crypto/rand"$`
// @Ensures True
func Clash() {}
