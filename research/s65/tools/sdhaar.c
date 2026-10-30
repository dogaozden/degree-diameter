/* sdhaar.c: exhaustive search over SELF-DUAL Haar graphs H(G,S), |S| = 6, diameter 5.
 *
 * H(G,S): (g,A) ~ (s g, B) for s in S. If phi in Aut(G) satisfies phi(S) = S^-1, then (g,A) -> (phi(g),B),
 * (g,B) -> (phi(g),A) is a colour-reversing automorphism, and the side-B condition (S S^-1)^2 = G is the image under
 * phi of the side-A condition (S^-1 S)^2 = G. So only side A has to be covered. Such S are exactly the unions of
 * orbits of sigma(s) = phi(s)^-1 with total size 6 (sigma^2 = phi^2; for an involution phi the orbits have size 1 or
 * 2). Every union is tested (no symmetry reduction); a covering S is re-checked by BFS on the full graph.
 * usage: sdhaar FILE        (FILE from sdhaar.g: n, table, k, k automorphisms as permutations)
 * env: PHI (only this automorphism index), MAXOUT (print at most this many near-miss sets, 5),
 *      MAXFIX (at most this many sigma-fixed elements in S, 2: S then has >= 2 sigma-pairs)
 * Output: per phi "PHI i fixed F pairs P ... sets N covered C minunc U", "VALID S = ..." lines, "RESULT ...".
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define W 8
static int N, *M, *INV;
static inline int mul(int a, int b) { return M[a * N + b]; }
static int S[6];
static long long nsets, ncov; static int minunc;

static int unc_A(void) {   /* elements of G missing from {e} u S^-1 S u (S^-1 S)^2 */
    int Q[36], nq = 0;
    for (int i = 0; i < 6; i++) for (int j = 0; j < 6; j++) Q[nq++] = mul(INV[S[i]], S[j]);
    uint64_t c[W] = {0};
    for (int i = 0; i < nq; i++) { const int *row = M + Q[i] * N; c[Q[i] >> 6] |= 1ULL << (Q[i] & 63);
        for (int j = 0; j < nq; j++) { int x = row[Q[j]]; c[x >> 6] |= 1ULL << (x & 63); } }
    int t = 0; for (int w = 0; w < W; w++) t += __builtin_popcountll(c[w]);
    return N - t;
}
static int bfs_ok(void) {   /* full check on the Haar graph: from (e,A) and (e,B) everything within 5 */
    int n = 2 * N; int *dist = malloc(sizeof(int) * n), *q = malloc(sizeof(int) * n); int ok = 1;
    for (int src = 0; src < 2 && ok; src++) {
        for (int v = 0; v < n; v++) dist[v] = -1;
        int h = 0, t = 0, s0 = src * N; dist[s0] = 0; q[t++] = s0;
        while (h < t) { int v = q[h++]; if (dist[v] == 5) continue; int g = v % N;
            for (int i = 0; i < 6; i++) { int w = v < N ? N + mul(S[i], g) : mul(INV[S[i]], g);
                if (dist[w] < 0) { dist[w] = dist[v] + 1; q[t++] = w; } } }
        if (t < n) ok = 0;
    }
    free(dist); free(q); return ok;
}
/* orbits of sigma */
static int norb, *osz, **orb;
static int MAXOUT = 5, nout = 0, MAXFIX = 2, nfix = 0;
static void rec(int start, int filled) {
    if (filled == 6) {
        nsets++;
        int u = unc_A();
        if (u < minunc) minunc = u;
        if (u == 0) { ncov++;
            if (bfs_ok()) { printf("VALID S = %d %d %d %d %d %d\n", S[0], S[1], S[2], S[3], S[4], S[5]); fflush(stdout); }
            else printf("ACOVER-BUT-BFS-FAIL S = %d %d %d %d %d %d\n", S[0], S[1], S[2], S[3], S[4], S[5]); }
        else if (u <= 2 && nout < MAXOUT) { nout++; printf("NEAR unc=%d S = %d %d %d %d %d %d\n", u, S[0], S[1], S[2], S[3], S[4], S[5]); }
        return;
    }
    for (int o = start; o < norb; o++) {
        if (filled + osz[o] > 6) continue;
        if (osz[o] == 1 && nfix >= MAXFIX) continue;
        for (int k = 0; k < osz[o]; k++) S[filled + k] = orb[o][k];
        nfix += osz[o] == 1; rec(o + 1, filled + osz[o]); nfix -= osz[o] == 1;
    }
}

int main(int argc, char **argv) {
    if (argc < 2) return 2;
    FILE *f = fopen(argv[1], "r"); if (!f || fscanf(f, "%d", &N) != 1 || N > 64 * W) return 2;
    M = malloc(sizeof(int) * N * N); INV = malloc(sizeof(int) * N);
    for (int i = 0; i < N * N; i++) if (fscanf(f, "%d", &M[i]) != 1) return 2;
    for (int a = 0; a < N; a++) for (int b = 0; b < N; b++) if (M[a * N + b] == 0) INV[a] = b;
    int k; if (fscanf(f, "%d", &k) != 1) return 2;
    int *phi = malloc(sizeof(int) * N * k);
    for (int a = 0; a < k; a++) for (int i = 0; i < N; i++) if (fscanf(f, "%d", &phi[a * N + i]) != 1) return 2;
    fclose(f);
    int ONLY = getenv("PHI") ? atoi(getenv("PHI")) : -1; if (getenv("MAXOUT")) MAXOUT = atoi(getenv("MAXOUT"));
    if (getenv("MAXFIX")) MAXFIX = atoi(getenv("MAXFIX"));
    osz = malloc(sizeof(int) * N); orb = malloc(sizeof(int *) * N); for (int i = 0; i < N; i++) orb[i] = malloc(sizeof(int) * 8);
    int *seen = malloc(sizeof(int) * N); long long tot = 0, totcov = 0; int gmin = N; clock_t t0 = clock();
    for (int a = 0; a < k; a++) {
        if (ONLY >= 0 && a != ONLY) continue;
        const int *p = phi + a * N;
        memset(seen, 0, sizeof(int) * N); norb = 0; int fixed = 0, pairs = 0, big = 0;
        for (int x = 0; x < N; x++) if (!seen[x]) {
            int len = 0, y = x;
            while (!seen[y] && len < 8) { seen[y] = 1; orb[norb][len++] = y; y = INV[p[y]]; }
            if (y != x) { fprintf(stderr, "sigma orbit too long\n"); return 3; }
            osz[norb++] = len; if (len == 1) fixed++; else if (len == 2) pairs++; else big++;
        }
        nsets = ncov = 0; minunc = N; nout = 0;
        rec(0, 0);
        printf("PHI %d fixed %d pairs %d longer %d sets %lld covered %lld minunc %d secs %.1f\n", a, fixed, pairs, big, nsets, ncov, minunc,
               (double)(clock() - t0) / CLOCKS_PER_SEC);
        fflush(stdout);
        tot += nsets; totcov += ncov; if (minunc < gmin) gmin = minunc;
    }
    printf("RESULT N %d phis %d sets %lld covered %lld minunc %d\n", N, k, tot, totcov, gmin);
    return 0;
}
