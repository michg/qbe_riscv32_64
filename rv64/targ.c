#include "all.h"

Rv64Op rv64_op[NOp] = {
#define O(op, t, x) [O##op] =
#define V(imm) { imm },
#include "../ops.h"
};

int rv64_rsave[] = {
	T0, T1, T2, T3, T4, T5,
	A0, A1, A2, A3, A4, A5, A6, A7,
	FA0, FA1, FA2,  FA3,  FA4, FA5, FA6, FA7,
	FT0, FT1, FT2,  FT3,  FT4, FT5, FT6, FT7,
	FT8, FT9, FT10,
	-1
};
int rv64_rclob[] = {
	     S1,  S2,   S3,   S4,  S5,  S6,  S7,
	S8,  S9,  S10,  S11,
	FS0, FS1, FS2,  FS3,  FS4, FS5, FS6, FS7,
	FS8, FS9, FS10, FS11,
	-1
};

#define RGLOB (BIT(FP) | BIT(SP) | BIT(GP) | BIT(TP) | BIT(RA))

static int
rv64_memargs(int op)
{
	(void)op;
	return 0;
}

int opt_rv32 = 0;
int regsize;
int regcls;
char *ldreg;
char *streg;

Topt rvopts[] = {{"rv32", &opt_rv32}, {"", 0}};
struct t_prop {
  int regsize;
  int regcls;
  char *ldreg;
  char *streg;
} rv_prop[2] = {{8, Kl, "ld", "sd"}, {4, Kw, "lw","sw"}};

void rv64_init() {
    regsize = rv_prop[opt_rv32].regsize;
    regcls = rv_prop[opt_rv32].regcls;
    ldreg = rv_prop[opt_rv32].ldreg;
    streg = rv_prop[opt_rv32].streg;
}

Target T_rv64 = {
	.name = "rv64",
	.gpr0 = T0,
	.ngpr = NGPR,
	.fpr0 = FT0,
	.nfpr = NFPR,
	.rglob = RGLOB,
	.nrglob = 5,
	.rsave = rv64_rsave,
	.nrsave = {NGPS, NFPS},
	.retregs = rv64_retregs,
	.argregs = rv64_argregs,
	.memargs = rv64_memargs,
	.topts = rvopts,
	.abi0 = elimsb,
	.abi1 = rv64_abi,
	.isel = rv64_isel,
	.emitfn = rv64_emitfn,
	.emitfin = elf_emitfin,
	.asloc = ".L",
	.init = rv64_init,
};



MAKESURE(rsave_size_ok, sizeof rv64_rsave == (NGPS+NFPS+1) * sizeof(int));
MAKESURE(rclob_size_ok, sizeof rv64_rclob == (NCLR+1) * sizeof(int));
