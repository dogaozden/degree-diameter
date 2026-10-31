/* qfeas.c: quotient counting test for Haar graphs H(G,S), |S| = 6, diameter <= 5 (job six-five-384).
 *
 * If H(G,S) has diameter <= 5, every element of G is the value of one of the 781 non-backtracking words
 *   e,   s_b^-1 s_a (a != b, 30 words),   s_a^-1 s_b s_c^-1 s_d (a != b, b != c, c != d, 750 words)      (side A)
 * and of one of the 781 words  e, s_a s_b^-1, s_a s_b^-1 s_c s_d^-1  (same index rules)                    (side B)
 * (the even-distance walks of length <= 4 from (e,A) and from (e,B)). For a normal subgroup N with Q = G/N and
 * images q_i of s_i, every coset y of N therefore needs at least |N| words with image y, on both sides.
 * Images may coincide (indices stay distinct). Left translation S -> tS keeps S^-1 S, so q_1 = e WLOG; and for
 * an automorphism phi of Q, phi(q) passes iff q passes, so q_2 can be restricted to Aut(Q)-orbit representatives
 * (or e, if all images are e).
 *
 * input (stdin or FILE): n, n x n table (element 0 = identity), then k and k automorphisms (permutations) or k = 0.
 * usage: qfeas FILE T   (T = |N| = required words per coset). Output: "FEAS q1..q6 minA minB" for the first
 * passing image tuple and stops, or "INFEAS tuples=... bestmin=..." (bestmin = max over tuples of min(minA,minB)).
 * env ALL=1: do not stop at the first passing tuple (count them).
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int n, *M, *INV;
static inline int mul(int a, int b) { return M[a * n + b]; }

static int find(int *p, int x) { while (p[x] != x) { p[x] = p[p[x]]; x = p[x]; } return x; }

int main(int argc, char **argv) {
    if (argc < 3) { fprintf(stderr, "usage: qfeas FILE T\n"); return 2; }
    FILE *f = fopen(argv[1], "r"); if (!f) return 2;
    int T = atoi(argv[2]); int all = getenv("ALL") ? atoi(getenv("ALL")) : 0;
    if (fscanf(f, "%d", &n) != 1) return 2;
    M = malloc(sizeof(int) * n * n); INV = malloc(sizeof(int) * n);
    for (int i = 0; i < n * n; i++) if (fscanf(f, "%d", &M[i]) != 1) return 2;
    for (int a = 0; a < n; a++) for (int b = 0; b < n; b++) if (M[a * n + b] == 0) INV[a] = b;
    int k = 0; if (fscanf(f, "%d", &k) != 1) k = 0;
    int *par = malloc(sizeof(int) * n); for (int i = 0; i < n; i++) par[i] = i;
    int *g = malloc(sizeof(int) * n);
    for (int a = 0; a < k; a++) {
        for (int i = 0; i < n; i++) if (fscanf(f, "%d", &g[i]) != 1) return 2;
        for (int x = 0; x < n; x++) { int u = find(par, x), v = find(par, g[x]); if (u != v) { if (u < v) par[v] = u; else par[u] = v; } }
    }
    fclose(f);
    int *reps = malloc(sizeof(int) * n), nreps = 0;
    for (int x = 0; x < n; x++) if (find(par, x) == x) reps[nreps++] = x;   /* includes 0 = e */
    if ((long)T * n > 781) { printf("INFEAS trivially (T*n = %ld > 781)\n", (long)T * n); return 0; }
    int *cA = malloc(sizeof(int) * n), *cB = malloc(sizeof(int) * n);
    int q[6]; q[0] = 0;
    long tuples = 0, nfeas = 0; int bestmin = -1; int bq[6] = {0};
    for (int r = 0; r < nreps; r++) {
        q[1] = reps[r];
        for (q[2] = 0; q[2] < n; q[2]++)
        for (q[3] = q[2]; q[3] < n; q[3]++)
        for (q[4] = q[3]; q[4] < n; q[4]++)
        for (q[5] = q[4]; q[5] < n; q[5]++) {
            tuples++;
            int DA[36], DB[36];
            for (int a = 0; a < 6; a++) for (int b = 0; b < 6; b++) {
                DA[a * 6 + b] = mul(INV[q[a]], q[b]); DB[a * 6 + b] = mul(q[a], INV[q[b]]); }
            memset(cA, 0, sizeof(int) * n); memset(cB, 0, sizeof(int) * n);
            cA[0]++; cB[0]++;
            for (int a = 0; a < 6; a++) for (int b = 0; b < 6; b++) if (a != b) { cA[DA[a * 6 + b]]++; cB[DB[a * 6 + b]]++; }
            for (int a = 0; a < 6; a++) for (int b = 0; b < 6; b++) if (a != b) {
                const int *rowA = M + DA[a * 6 + b] * n, *rowB = M + DB[a * 6 + b] * n;
                for (int c = 0; c < 6; c++) if (c != b) for (int d = 0; d < 6; d++) if (d != c) {
                    cA[rowA[DA[c * 6 + d]]]++; cB[rowB[DB[c * 6 + d]]]++; }
            }
            int mA = 1 << 30, mB = 1 << 30;
            for (int y = 0; y < n; y++) { if (cA[y] < mA) mA = cA[y]; if (cB[y] < mB) mB = cB[y]; }
            int m = mA < mB ? mA : mB;
            if (m > bestmin) { bestmin = m; memcpy(bq, q, sizeof q); }
            if (m >= T) {
                nfeas++;
                if (!all) { printf("FEAS %d %d %d %d %d %d minA=%d minB=%d tuples=%ld\n", q[0], q[1], q[2], q[3], q[4], q[5], mA, mB, tuples); return 0; }
            }
        }
    }
    if (nfeas) printf("FEAS count=%ld tuples=%ld bestmin=%d\n", nfeas, tuples, bestmin);
    else printf("INFEAS tuples=%ld bestmin=%d at %d %d %d %d %d %d (T=%d, reps=%d)\n", tuples, bestmin, bq[0], bq[1], bq[2], bq[3], bq[4], bq[5], T, nreps);
    return 0;
}
