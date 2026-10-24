/* Universal route charts over F_2^4 for an alphabet of 2r letters (r generators and inverses), label-reduced words of
   length 4: A_t in GL_4(F_2) as 4x4 bit matrices, b_t in F_2^4. Simulated annealing on the number of singular words. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <time.h>
typedef unsigned int u32;
static int R;                     /* number of generators */
static u32 A[16][4], b[16];       /* A[t][row] bitmask of row; letters 2i = gen i, 2i+1 = inverse */
static u32 mv(const u32 *M, u32 x) { u32 y = 0; for (int i = 0; i < 4; i++) y |= (u32)(__builtin_popcount(M[i] & x) & 1) << i; return y; }
static int inv4(const u32 *M, u32 *Ri) { u32 a[4], r[4]; for (int i = 0; i < 4; i++) { a[i] = M[i]; r[i] = 1u << i; }
    for (int c = 0; c < 4; c++) { int p = -1; for (int i = c; i < 4; i++) if (a[i] >> c & 1) { p = i; break; } if (p < 0) return 0;
        u32 t = a[p]; a[p] = a[c]; a[c] = t; t = r[p]; r[p] = r[c]; r[c] = t;
        for (int i = 0; i < 4; i++) if (i != c && (a[i] >> c & 1)) { a[i] ^= a[c]; r[i] ^= r[c]; } }
    for (int i = 0; i < 4; i++) Ri[i] = r[i]; return 1; }
static int rank4cols(u32 c1, u32 c2, u32 c3, u32 c4) { u32 v[4] = {c1, c2, c3, c4}; int r = 0;
    for (int bit = 0; bit < 4; bit++) { int p = -1; for (int i = r; i < 4; i++) if (v[i] >> bit & 1) { p = i; break; } if (p < 0) continue;
        u32 t = v[p]; v[p] = v[r]; v[r] = t; for (int i = 0; i < 4; i++) if (i != r && (v[i] >> bit & 1)) v[i] ^= v[r]; r++; }
    return r; }
static int setup(void) { for (int i = 0; i < R; i++) { if (!inv4(A[2*i], A[2*i+1])) return 0; b[2*i+1] = mv(A[2*i+1], b[2*i]); if (!b[2*i]) return 0; } return 1; }
static int cost(void) { int bad = 0, L = 2 * R;
    for (int t1 = 0; t1 < L; t1++) for (int t2 = 0; t2 < L; t2++) { if (t2 == (t1 ^ 1)) continue; u32 p2 = mv(A[t2], b[t1]);
      for (int t3 = 0; t3 < L; t3++) { if (t3 == (t2 ^ 1)) continue; u32 p3a = mv(A[t3], p2), p3b = mv(A[t3], b[t2]);
        for (int t4 = 0; t4 < L; t4++) { if (t4 == (t3 ^ 1)) continue;
          if (rank4cols(mv(A[t4], p3a), mv(A[t4], p3b), mv(A[t4], b[t3]), b[t4]) < 4) bad++; } } }
    return bad; }
static unsigned long long rs = 88172645463325252ULL;
static unsigned long long rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
int main(int argc, char **argv) {
    R = argc > 1 ? atoi(argv[1]) : 4; rs ^= (unsigned long long)(argc > 2 ? atoll(argv[2]) : time(NULL)) * 0x9E3779B97F4A7C15ULL;
    long iters = argc > 3 ? atol(argv[3]) : 200000; int restarts = argc > 4 ? atoi(argv[4]) : 20;
    int L = 2 * R, nwords = L * (L-1) * (L-1) * (L-1), best = 1 << 30;
    for (int rr = 0; rr < restarts; rr++) {
        do { for (int i = 0; i < R; i++) { for (int j = 0; j < 4; j++) A[2*i][j] = rnd() & 15; b[2*i] = rnd() & 15; } } while (!setup());
        int c = cost(); double T = 3.0;
        for (long it = 0; it < iters && c > 0; it++) {
            u32 sA[16][4], sb[16]; memcpy(sA, A, sizeof A); memcpy(sb, b, sizeof b);
            int g = rnd() % R; if (rnd() % 5) A[2*g][rnd() & 3] ^= 1u << (rnd() & 3); else b[2*g] ^= 1u << (rnd() & 3);
            if (!setup()) { memcpy(A, sA, sizeof A); memcpy(b, sb, sizeof b); continue; }
            int c2 = cost();
            if (c2 <= c || (double)(rnd() % 1000000) / 1e6 < exp((c - c2) / T)) c = c2; else { memcpy(A, sA, sizeof A); memcpy(b, sb, sizeof b); }
            T *= 0.99997; if (T < 0.1) T = 0.1;
        }
        if (c < best) { best = c; printf("R=%d restart %d: %d singular of %d words\n", R, rr, c, nwords); fflush(stdout); }
        if (c == 0) { for (int i = 0; i < R; i++) { printf("gen %d: A rows", i); for (int j = 0; j < 4; j++) printf(" %x", A[2*i][j]); printf(" b %x\n", b[2*i]); } return 0; }
    }
    return 1;
}
