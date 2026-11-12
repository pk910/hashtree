/* Minimal freestanding runtime for the qemu harnesses (the VM has no aarch64 libc headers):
 * _start, write/exit syscalls, memset/memcpy, buffered hex/decimal output.
 * Build: aarch64-linux-gnu-gcc -O2 -static -nostdlib -ffreestanding -fno-builtin ... */
#include <stdint.h>
#include <stddef.h>

static long sys3(long n, long a, long b, long c) {
  register long x8 __asm__("x8") = n;
  register long x0 __asm__("x0") = a;
  register long x1 __asm__("x1") = b;
  register long x2 __asm__("x2") = c;
  __asm__ volatile("svc #0" : "+r"(x0) : "r"(x8), "r"(x1), "r"(x2) : "memory");
  return x0;
}
static char obuf[1 << 16];
static size_t olen;
static void oflush(void) { size_t o = 0; while (o < olen) { long r = sys3(64, 1, (long)(obuf + o), olen - o); if (r <= 0) break; o += r; } olen = 0; }
static void oc(char c) { if (olen == sizeof obuf) oflush(); obuf[olen++] = c; }
static void os(const char *s) { while (*s) oc(*s++); }
static void ohex(uint64_t v) { char t[16]; int n = 0; do { t[n++] = "0123456789abcdef"[v & 15]; v >>= 4; } while (v); while (n) oc(t[--n]); }
static void ohex2(unsigned v) { oc("0123456789abcdef"[(v >> 4) & 15]); oc("0123456789abcdef"[v & 15]); }
static void odec(long long v) { char t[24]; int n = 0; unsigned long long u = v < 0 ? -(unsigned long long)v : (unsigned long long)v; if (v < 0) oc('-'); do { t[n++] = '0' + u % 10; u /= 10; } while (u); while (n) oc(t[--n]); }
__attribute__((noreturn)) static void sys_exit(int c) { oflush(); sys3(94, c, 0, 0); for (;;) {} }
void *memset(void *d, int c, size_t n) { unsigned char *p = d; while (n--) *p++ = (unsigned char)c; return d; }
void *memcpy(void *d, const void *s, size_t n) { unsigned char *p = d; const unsigned char *q = s; while (n--) *p++ = *q++; return d; }
static int streq(const char *a, const char *b) { while (*a && *a == *b) { a++; b++; } return *a == *b; }
static int atoi_(const char *s) { int v = 0; while (*s >= '0' && *s <= '9') v = 10 * v + (*s++ - '0'); return v; }
int main(int argc, char **argv);
__attribute__((used)) void cstart(uint64_t *sp) { sys_exit(main((int)sp[0], (char **)(sp + 1))); }
__asm__(".global _start\n_start:\n\tmov x0, sp\n\tbl cstart\n");
