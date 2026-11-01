/* capacity: an upper bound on |(S S^-1)^h| for Haar sets S = {e, s1, s2, s3} in any metacyclic group
 * G = Z_m x|_r Z_k in which r has multiplicative order d (mod m).
 *
 * Formal model: s_i = (e_i, y_i) in R^3 x| Z^3, R = Z[x]/(x^d - 1), e_i the i-th unit vector of R^3, y_i the i-th
 * unit vector of Z^3, and y in Z^3 acts on R^3 by multiplication with x^(c . y), c = (c1, c2, c3) = (j1, j2, j3) mod d.
 * Every word in S S^-1 maps onto G by e_i -> a_i, x -> r, y_i -> j_i, so |T^h| in G <= number of distinct formal
 * words (T = S S^-1).  The other side (S^-1 S) is the same up to the anti-automorphism g -> g^-1, so one count is
 * enough.  Prints, for each d, the maximum over c in Z_d^3 (and the c reaching it).
 * Usage: capacity DMAX [H]   (H = 4 for diameter 9)
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#define MAXD 64
static int d, H = 4, L;              /* L = 3d + 3 coordinates */
typedef struct { int16_t v[3 * MAXD + 3]; } El;
static El *tab; static uint64_t *hk; static size_t cap;
static uint64_t hsh(const El *e) { uint64_t h = 1469598103934665603ULL; for (int i = 0; i < L; i++) { h ^= (uint16_t)e->v[i]; h *= 1099511628211ULL; } return h | 1; }
static int ins(const El *e) { uint64_t h = hsh(e); size_t i = h & (cap - 1);
    while (hk[i]) { if (hk[i] == h && !memcmp(tab[i].v, e->v, L * 2)) return 0; i = (i + 1) & (cap - 1); }
    hk[i] = h; tab[i] = *e; return 1; }
static int c[3];
static void mulel(const El *a, const El *b, El *o) {  /* (P,y)(P',y') = (P + x^(c.y) P', y + y') */
    int sh = 0; for (int i = 0; i < 3; i++) sh += c[i] * a->v[3 * d + i]; sh %= d; if (sh < 0) sh += d;
    for (int i = 0; i < L; i++) o->v[i] = a->v[i];
    for (int g = 0; g < 3; g++) for (int t = 0; t < d; t++) o->v[g * d + (t + sh) % d] += b->v[g * d + t];
    for (int i = 0; i < 3; i++) o->v[3 * d + i] += b->v[3 * d + i];
}
static void invel(const El *a, El *o) {  /* (P,y)^-1 = (-x^(-c.y) P, -y) */
    int sh = 0; for (int i = 0; i < 3; i++) sh += c[i] * a->v[3 * d + i]; sh %= d; if (sh < 0) sh += d; sh = (d - sh) % d;
    memset(o, 0, sizeof(El));
    for (int g = 0; g < 3; g++) for (int t = 0; t < d; t++) o->v[g * d + (t + sh) % d] = -a->v[g * d + t];
    for (int i = 0; i < 3; i++) o->v[3 * d + i] = -a->v[3 * d + i];
}
static long count(void) {
    El S[4]; memset(S, 0, sizeof S);
    for (int i = 1; i <= 3; i++) { S[i].v[(i - 1) * d] = 1; S[i].v[3 * d + i - 1] = 1; }
    El T[16]; int nt = 0;
    for (int i = 0; i < 4; i++) for (int j = 0; j < 4; j++) { El iv, o; invel(&S[j], &iv); mulel(&S[i], &iv, &o);
        int dup = 0; for (int t = 0; t < nt; t++) if (!memcmp(T[t].v, o.v, L * 2)) dup = 1; if (!dup) T[nt++] = o; }
    memset(hk, 0, cap * 8);
    El *fr = malloc(sizeof(El) * 200000), *nx = malloc(sizeof(El) * 200000); int nf = 1; memset(&fr[0], 0, sizeof(El));
    ins(&fr[0]); long tot = 1;
    for (int s = 0; s < H; s++) { int nn = 0;
        for (int i = 0; i < nf; i++) for (int t = 0; t < nt; t++) { El o; mulel(&fr[i], &T[t], &o); if (ins(&o)) { nx[nn++] = o; } }
        El *tmp = fr; fr = nx; nx = tmp; nf = nn; tot += nn; }
    free(fr); free(nx); return tot;
}
int main(int argc, char **argv) {
    int dmax = atoi(argv[1]); if (argc > 2) H = atoi(argv[2]);
    cap = 1 << 18; tab = malloc(sizeof(El) * cap); hk = malloc(8 * cap);
    for (d = 1; d <= dmax; d++) { L = 3 * d + 3; long best = 0; int bc[3] = {0, 0, 0};
        for (c[0] = 0; c[0] < d; c[0]++) for (c[1] = c[0]; c[1] < d; c[1]++) for (c[2] = c[1]; c[2] < d; c[2]++) {
            long n = count(); if (n > best) { best = n; bc[0] = c[0]; bc[1] = c[1]; bc[2] = c[2]; } }
        printf("d %d  max formal |T^%d| = %ld  at c = (%d,%d,%d)\n", d, H, best, bc[0], bc[1], bc[2]); fflush(stdout); }
    return 0;
}
