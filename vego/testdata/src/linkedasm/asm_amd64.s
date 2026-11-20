#include "textflag.h"

// func load() error
TEXT ·load(SB), NOSPLIT, $0-16
	MOVQ ·ErrAsm(SB), AX
	MOVQ AX, ret+0(FP)
	MOVQ ·ErrAsm+8(SB), AX
	MOVQ AX, ret+8(FP)
	RET

// func clear()
TEXT ·clear(SB), NOSPLIT, $0-0
	MOVQ $0, AX
	MOVQ AX, linked·example∕lib·ErrFar(SB) // want `vego: lib.ErrFar may be changed here, but proofs in package linked.example/lib rely on it being the error it was declared with`
	MOVQ AX, linked·example∕lib·ErrFar+8(SB) // want `vego: lib.ErrFar may be changed here, but proofs in package linked.example/lib rely on it being the error it was declared with`
	RET
