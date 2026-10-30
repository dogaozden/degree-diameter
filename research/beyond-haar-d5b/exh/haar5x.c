/* haar5x.c: exhaustive search for Haar graphs H(G, S) of valency 5 and diameter <= 5 (G given by its table, |G| <= 256).
 *
 * H(G, S): vertices (g, A), (g, B); (g, A) ~ (s g, B) for s in S. Right multiplication by G is regular on each side,
 * so the diameter is <= 5 iff (1, A) reaches every (h, A) within 4 and (1, B) every (h, B) within 4 (then every
 * A-B pair is within 5). (1, A) -> (s, B) -> (t^-1 s, A): the A side is covered by the non-backtracking products
 * 1, t^-1 s (t != s), u^-1 v t^-1 s (consecutive letters distinct), i.e. the closed-walk products of S^-1 S S^-1 S;
 * the B side by s t^-1 and s t^-1 u v^-1 likewise.
 * H(G, S) is isomorphic to H(G, S t) (relabel B by right multiplication) and to H(G, phi(S)) for phi in Aut(G), so we
 * take 1 in S, S = {1, a, b, c, d} with a < b < c < d, and a equal to the smallest element of its Aut(G)-orbit:
 * if r is the smallest orbit representative met by S\{1}, an automorphism maps that element to r, and every other
 * element of the image is >= its own representative >= r, so the image is {1, r, ...} with r a representative.
 * usage: haar5x GROUP AUTGENS     (AUTGENS as in b4a2y: k then k image lists)
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXM 256
#define NW 4
typedef struct { uint64_t w[NW]; } bs;
static int m, mul[MAXM][MAXM], inv_[MAXM];
static inline void setb(bs *x, int i) { x->w[i >> 6] |= 1ULL << (i & 63); }
static inline int cnt_missing(const bs *x) { int c = 0; for (int k = 0; k < NW; k++) c += __builtin_popcountll(x->w[k]); return m - c; }

/* cover of side A (sgn = 0: letters x^-1 y ...) or side B (sgn = 1: x y^-1 ...) by words over the letters L[0..n-1],
 * only words that use at least one letter >= first (so incremental sets can be combined) */
static void cover(const int *L, int n, int first, int side, bs *c) {
    for (int i = 0; i < n; i++) for (int j = 0; j < n; j++) { if (j == i) continue;
        int p = side == 0 ? mul[inv_[L[i]]][L[j]] : mul[L[i]][inv_[L[j]]];
        if (i >= first || j >= first) setb(c, p);
        for (int k = 0; k < n; k++) { if (k == j) continue;
            for (int l = 0; l < n; l++) { if (l == k) continue;
                if (i < first && j < first && k < first && l < first) continue;
                int q = side == 0 ? mul[mul[p][inv_[L[k]]]][L[l]] : mul[mul[p][L[k]]][inv_[L[l]]];
                setb(c, q); } } }
}

int main(int argc, char **argv) {
    if (argc < 3) return 2;
    FILE *f = fopen(argv[1], "r"); if (!f || fscanf(f, "%d", &m) != 1 || m > MAXM) return 2;
    for (int i = 0; i < m; i++) for (int j = 0; j < m; j++) if (fscanf(f, "%d", &mul[i][j]) != 1) return 2;
    fclose(f);
    for (int i = 0; i < m; i++) for (int j = 0; j < m; j++) if (mul[i][j] == 0) inv_[i] = j;
    int ng; f = fopen(argv[2], "r"); if (!f || fscanf(f, "%d", &ng) != 1) return 2;
    int (*gens)[MAXM] = malloc(sizeof(int[MAXM]) * (ng + 1));
    for (int a = 0; a < ng; a++) for (int x = 0; x < m; x++) if (fscanf(f, "%d", &gens[a][x]) != 1) return 2;
    fclose(f);
    /* Aut-orbit representatives (smallest element) */
    int rep[MAXM]; for (int g = 0; g < m; g++) rep[g] = g;
    for (int changed = 1; changed; ) { changed = 0;
        for (int g = 0; g < m; g++) for (int k = 0; k < ng; k++) { int h = gens[k][g];
            int r = rep[g] < rep[h] ? rep[g] : rep[h]; if (rep[g] != r || rep[h] != r) { rep[g] = rep[h] = r; changed = 1; } } }
    for (int g = 0; g < m; g++) { int r = g; while (rep[r] != r) r = rep[r]; rep[g] = r; }
    long long nabc = 0, ntest = 0, nsol = 0; clock_t t0 = clock();
    /* walks using only letters of {1,a,b,c}: at most 4*3*3*3 + 12 = 120; the rest use d: bound 341 - 1 - 120 */
    for (int a = 1; a < m; a++) { if (rep[a] != a) continue;
        for (int b = a + 1; b < m; b++) for (int c = b + 1; c < m; c++) {
            int L[5] = {0, a, b, c, 0};
            bs cA = {{0}}, cB = {{0}}; setb(&cA, 0); setb(&cB, 0);
            cover(L, 4, 0, 0, &cA); cover(L, 4, 0, 1, &cB);
            nabc++;
            if (cnt_missing(&cA) > 220 || cnt_missing(&cB) > 220) continue;
            for (int d = c + 1; d < m; d++) {
                L[4] = d; ntest++;
                bs xA = cA; cover(L, 5, 4, 0, &xA); if (cnt_missing(&xA)) continue;
                bs xB = cB; cover(L, 5, 4, 1, &xB); if (cnt_missing(&xB)) continue;
                nsol++; printf("SOL S 0 %d %d %d %d\n", a, b, c, d); fflush(stdout);
            }
        }
    }
    fprintf(stderr, "m %d autgens %d abc %lld tests %lld solutions %lld secs %.1f\n", m, ng, nabc, ntest, nsol,
            (double)(clock() - t0) / CLOCKS_PER_SEC);
    return 0;
}
