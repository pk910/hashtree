/* Freestanding RV64 harness for the shipped hashtree objects (run under qemu-riscv64).
 *
 *   rv_harness k <kernel> <count> <seed> <inOff> <outOff>   kernel 0=x1 1=zbb_x1 2=crypto 3=hashtree_hash
 *   rv_harness a <kernel> <count> <seed> <inOff> <outOff>   output inside the input buffer (at outOff)
 *   rv_harness probe                                         print riscv_hwprobe(IMA_EXT_0)
 *
 * Input bytes: the LCG of RvCheck.randInput; output: hex of out[0 .. 32*count).
 * Provides `syscall`, `__stack_chk_guard`, `__stack_chk_fail` for hashtree.o (no libc). */
typedef unsigned long u64;
typedef unsigned char u8;

extern void hashtree_sha256_riscv_x1(u8 *, const u8 *, u64);
extern void hashtree_sha256_riscv_zbb_x1(u8 *, const u8 *, u64);
extern void hashtree_sha256_riscv_crypto(u8 *, const u8 *, u64);
extern void hashtree_hash(u8 *, const u8 *, u64);

static long sys6(long n, long a, long b, long c, long d, long e, long f) {
    register long a7 asm("a7") = n;
    register long a0 asm("a0") = a;
    register long a1 asm("a1") = b;
    register long a2 asm("a2") = c;
    register long a3 asm("a3") = d;
    register long a4 asm("a4") = e;
    register long a5 asm("a5") = f;
    asm volatile("ecall" : "+r"(a0) : "r"(a7), "r"(a1), "r"(a2), "r"(a3), "r"(a4), "r"(a5) : "memory");
    return a0;
}
/* glibc's syscall(number, ...): variadic integer arguments travel in a1..a6 as here. */
long syscall(long n, long a, long b, long c, long d, long e, long f) {
    long r = sys6(n, a, b, c, d, e, f);
    return r < 0 && r > -4096 ? -1 : r;
}
u64 __stack_chk_guard = 0x5a6b7c8d9eafb0c1UL;
static void exit_(long c) { sys6(93, c, 0, 0, 0, 0, 0); for (;;) {} }
void __stack_chk_fail(void) { exit_(99); }
static void put(const char *s, long n) { sys6(64, 1, (long)s, n, 0, 0, 0); }

static u64 num(const char *s) { u64 n = 0; while (*s >= '0' && *s <= '9') n = n * 10 + (*s++ - '0'); return n; }
static int streq(const char *a, const char *b) { while (*a && *a == *b) { a++; b++; } return *a == *b; }

static u8 inbuf[64 * 64 + 256] __attribute__((aligned(64)));
static u8 outbuf[32 * 64 + 128] __attribute__((aligned(64)));
static char line[2 * 32 * 64 + 64];
static const char hx[] = "0123456789abcdef";

static void hexout(const u8 *p, u64 n) {
    for (u64 i = 0; i < n; i++) { line[2 * i] = hx[p[i] >> 4]; line[2 * i + 1] = hx[p[i] & 15]; }
    line[2 * n] = '\n';
    put(line, 2 * n + 1);
}

long cmain(long *sp) {
    long argc = sp[0];
    char **argv = (char **)(sp + 1);
    if (argc == 2 && streq(argv[1], "probe")) {
        u64 pair[2] = {4, 0};
        long r = syscall(258, (long)pair, 1, 0, 0, 0, 0);
        u8 b[8];
        for (int i = 0; i < 8; i++) b[i] = (u8)(pair[1] >> (56 - 8 * i));
        if (r != 0) { put("hwprobe failed\n", 15); return 1; }
        hexout(b, 8);
        return 0;
    }
    if (argc != 7 || !(streq(argv[1], "k") || streq(argv[1], "a"))) { put("usage\n", 6); return 2; }
    int alias = streq(argv[1], "a");
    u64 k = num(argv[2]), count = num(argv[3]), seed = num(argv[4]), io = num(argv[5]), oo = num(argv[6]);
    if (count > 64 || io > 127 || oo > 127 || (alias && oo > io)) return 2;
    u64 x = seed * 6364136223846793005UL + 1442695040888963407UL;
    for (u64 i = 0; i < 64 * count; i++) {
        x = x * 6364136223846793005UL + 1442695040888963407UL;
        inbuf[io + i] = (u8)((x >> 33) & 255);
    }
    for (u64 i = 0; i < sizeof outbuf; i++) outbuf[i] = 0xee;
    u8 *out = alias ? inbuf + oo : outbuf + oo;
    const u8 *in = inbuf + io;
    switch (k) {
    case 0: hashtree_sha256_riscv_x1(out, in, count); break;
    case 1: hashtree_sha256_riscv_zbb_x1(out, in, count); break;
    case 2: hashtree_sha256_riscv_crypto(out, in, count); break;
    case 3: hashtree_hash(out, in, count); break;
    default: return 2;
    }
    /* bytes around the output must be untouched */
    for (u64 i = 0; i < sizeof outbuf; i++)
        if ((alias || i < oo || i >= oo + 32 * count) && outbuf[i] != 0xee) { put("clobber\n", 8); return 3; }
    hexout(out, 32 * count);
    return 0;
}

asm(".globl _start\n"
    "_start:\n"
    ".option push\n.option norelax\n"
    "  la gp, __global_pointer$\n"
    ".option pop\n"
    "  mv a0, sp\n"
    "  andi sp, sp, -16\n"
    "  call cmain\n"
    "  li a7, 93\n"
    "  ecall\n");
