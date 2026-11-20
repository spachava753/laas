#include "textflag.h"

// func load() error
TEXT ·load(SB), NOSPLIT, $0-16
	MOVQ ·ErrAsm(SB), AX
	MOVQ AX, ret+0(FP)
	MOVQ ·ErrAsm+8(SB), AX
	MOVQ AX, ret+8(FP)
	RET
