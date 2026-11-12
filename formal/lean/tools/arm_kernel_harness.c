/* Differential test of the shipped AArch64 kernel objects (run under qemu-aarch64-static):
 * for each kernel and count 0..34 hash the same pseudo-random input as `armcheck` (seed =
 * count + 7, the LCG of ArmCheck.randInput) and print `<kernel> <count> <hex output>`, the
 * format of `armcheck --dumpall`.  Input and output are deliberately misaligned (+3, +5); a
 * write past the output is reported.  Link with the shipped .o files (ar x libhashtree.a).
 * Usage: arm_kernel_harness [kernel...]   (default: all three) */
#include "arm_rt.h"

void hashtree_sha256_sha_x1(unsigned char *out, const unsigned char *in, uint64_t count);
void hashtree_sha256_neon_x1(unsigned char *out, const unsigned char *in, uint64_t count);
void hashtree_sha256_neon_x4(unsigned char *out, const unsigned char *in, uint64_t count);

static void rand_input(uint64_t seed, unsigned char *a, size_t n) {
  uint64_t x = seed * 6364136223846793005ull + 1442695040888963407ull;
  for (size_t i = 0; i < n; i++) {
    x = x * 6364136223846793005ull + 1442695040888963407ull;
    a[i] = (unsigned char)((x >> 33) % 256);
  }
}

static unsigned char inb[64 * 35 + 64], outb[32 * 35 + 64];

int main(int argc, char **argv) {
  struct { const char *name; void (*f)(unsigned char *, const unsigned char *, uint64_t); } ks[] = {
    {"hashtree_sha256_sha_x1", hashtree_sha256_sha_x1},
    {"hashtree_sha256_neon_x4", hashtree_sha256_neon_x4},
    {"hashtree_sha256_neon_x1", hashtree_sha256_neon_x1}};
  for (int k = 0; k < 3; k++) {
    if (argc > 1) {
      int want = 0;
      for (int a = 1; a < argc; a++) if (streq(argv[a], ks[k].name)) want = 1;
      if (!want) continue;
    }
    for (int count = 0; count < 35; count++) {
      unsigned char *in = inb + 3, *out = outb + 5;
      rand_input(count + 7, in, 64 * count);
      memset(outb, 0xa5, sizeof outb);
      ks[k].f(out, in, count);
      for (int i = 0; i < (int)sizeof outb; i++)
        if ((i < 5 || i >= 5 + 32 * count) && outb[i] != 0xa5) { os("OVERRUN "); os(ks[k].name); oc('\n'); sys_exit(1); }
      os(ks[k].name); oc(' '); odec(count); oc(' ');
      for (int i = 0; i < 32 * count; i++) ohex2(out[i]);
      oc('\n');
    }
  }
  return 0;
}
