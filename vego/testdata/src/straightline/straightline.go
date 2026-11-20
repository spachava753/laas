// Package straightline is a function of 120 straight-line statements that
// write and read a slice of 16, measured with F12; see Long functions cost
// the square of their length under Speed in the ROADMAP. It is not the
// program of the same description in the table there, which is not in the
// repository. It is not part of the tests: it takes about 9 s.
package straightline

// Fill writes and reads a slice of 16 in 120 statements.
//
// @Requires |s| = 16 And 0 <= s[0] < 100
// @Modifies s
// @Ensures s'[0] = 1
func Fill(s []int) {
	s[0] = 0
	s[10] = s[1] % 1000
	s[2] = s[1] / 2
	s[3] = 3
	s[15] = s[4] % 1000
	s[5] = s[6] / 2
	s[6] = 6
	s[4] = s[7] % 1000
	s[8] = s[11] / 2
	s[9] = 9
	s[9] = s[10] % 1000
	s[11] = s[0] / 2
	s[12] = 12
	s[14] = s[13] % 1000
	s[14] = s[5] / 2
	s[15] = 15
	s[3] = s[0] % 1000
	s[1] = s[10] / 2
	s[2] = 18
	s[8] = s[3] % 1000
	s[4] = s[15] / 2
	s[5] = 21
	s[13] = s[6] % 1000
	s[7] = s[4] / 2
	s[8] = 24
	s[2] = s[9] % 1000
	s[10] = s[9] / 2
	s[11] = 27
	s[7] = s[12] % 1000
	s[13] = s[14] / 2
	s[14] = 30
	s[12] = s[15] % 1000
	s[0] = s[3] / 2
	s[1] = 33
	s[1] = s[2] % 1000
	s[3] = s[8] / 2
	s[4] = 36
	s[6] = s[5] % 1000
	s[6] = s[13] / 2
	s[7] = 39
	s[11] = s[8] % 1000
	s[9] = s[2] / 2
	s[10] = 42
	s[0] = s[11] % 1000
	s[12] = s[7] / 2
	s[13] = 45
	s[5] = s[14] % 1000
	s[15] = s[12] / 2
	s[0] = 48
	s[10] = s[1] % 1000
	s[2] = s[1] / 2
	s[3] = 51
	s[15] = s[4] % 1000
	s[5] = s[6] / 2
	s[6] = 54
	s[4] = s[7] % 1000
	s[8] = s[11] / 2
	s[9] = 57
	s[9] = s[10] % 1000
	s[11] = s[0] / 2
	s[12] = 60
	s[14] = s[13] % 1000
	s[14] = s[5] / 2
	s[15] = 63
	s[3] = s[0] % 1000
	s[1] = s[10] / 2
	s[2] = 66
	s[8] = s[3] % 1000
	s[4] = s[15] / 2
	s[5] = 69
	s[13] = s[6] % 1000
	s[7] = s[4] / 2
	s[8] = 72
	s[2] = s[9] % 1000
	s[10] = s[9] / 2
	s[11] = 75
	s[7] = s[12] % 1000
	s[13] = s[14] / 2
	s[14] = 78
	s[12] = s[15] % 1000
	s[0] = s[3] / 2
	s[1] = 81
	s[1] = s[2] % 1000
	s[3] = s[8] / 2
	s[4] = 84
	s[6] = s[5] % 1000
	s[6] = s[13] / 2
	s[7] = 87
	s[11] = s[8] % 1000
	s[9] = s[2] / 2
	s[10] = 90
	s[0] = s[11] % 1000
	s[12] = s[7] / 2
	s[13] = 93
	s[5] = s[14] % 1000
	s[15] = s[12] / 2
	s[0] = 96
	s[10] = s[1] % 1000
	s[2] = s[1] / 2
	s[3] = 99
	s[15] = s[4] % 1000
	s[5] = s[6] / 2
	s[6] = 102
	s[4] = s[7] % 1000
	s[8] = s[11] / 2
	s[9] = 105
	s[9] = s[10] % 1000
	s[11] = s[0] / 2
	s[12] = 108
	s[14] = s[13] % 1000
	s[14] = s[5] / 2
	s[15] = 111
	s[3] = s[0] % 1000
	s[1] = s[10] / 2
	s[2] = 114
	s[8] = s[3] % 1000
	s[4] = s[15] / 2
	s[5] = 117
	s[13] = s[6] % 1000
	s[7] = s[4] / 2
	s[0] = 1
}
