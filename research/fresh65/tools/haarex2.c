/* Exhaustive Haar search at (6,5), orderly version (job fresh-6-5).
 *
 * H(G,S) ~ H(G, phi(g S h)) and ~ H(G, S^-1) for phi in Aut(G), g, h in G. Normalise e in S. Ordered pairs
 * (x, y) of distinct non-identity elements fall into Aut-classes; class(x,y) = the smallest index x*N+y in the
 * class. We visit S = {e, r, r2, a, b, c} only for (r, r2) a class minimum, and prune a prefix P as soon as some
 * transform of P that contains e (P t^-1, t^-1 P, P^-1 t, t P^-1 for t in P) has an ordered pair of non-identity
 * elements in a smaller class than (r, r2). Every isomorphism class of such Haar graphs keeps at least one
 * member (map its globally smallest pair onto the class representative), so the search stays exhaustive.
 *
 * input: N, the N x N multiplication table (element 0 = identity), then k and k automorphisms as permutations
 * of 0..N-1 (from haarex2.g). usage: haarex2 FILE [PAIRFROM PAIRTO]   (pair index range, for splitting)
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

#define W 8
static int N, *M, *INV, *CL;   /* CL[x*N+y] = class minimum index of the ordered pair (x,y) */
static inline int mul(int a, int b) { return M[a * N + b]; }

static int find(int *p, int x) { while (p[x] != x) { p[x] = p[p[x]]; x = p[x]; } return x; }

/* does some transform of P (size np, P[0] = e) have a pair class < cur ? */
static int bad(const int *P, int np, int cur) {
    int T[6];
    for (int ti = 0; ti < np; ti++) {
        int t = P[ti], ti_inv = INV[t];
        for (int mode = 0; mode < 4; mode++) {
            for (int i = 0; i < np; i++) {
                int x = P[i];
                switch (mode) {
                    case 0: T[i] = mul(x, ti_inv); break;            /* P t^-1 */
                    case 1: T[i] = mul(ti_inv, x); break;            /* t^-1 P */
                    case 2: T[i] = mul(INV[x], t); break;            /* P^-1 t */
                    default: T[i] = mul(t, INV[x]); break;           /* t P^-1 */
                }
            }
            for (int i = 0; i < np; i++) { if (T[i] == 0) continue;
                for (int j = 0; j < np; j++) { if (j == i || T[j] == 0) continue;
                    if (CL[T[i] * N + T[j]] < cur) return 1; } }
        }
    }
    return 0;
}

static int cover_count(const int *Q, int nq) {
    uint64_t c[W] = {0};
    for (int i = 0; i < nq; i++) { const int *row = M + Q[i] * N; for (int j = 0; j < nq; j++) { int x = row[Q[j]]; c[x >> 6] |= 1ULL << (x & 63); } }
    int t = 0; for (int w = 0; w < W; w++) t += __builtin_popcountll(c[w]);
    return t;
}

int main(int argc, char **argv) {
    FILE *f = fopen(argv[1], "r"); if (!f) return 2;
    if (fscanf(f, "%d", &N) != 1 || N > 64 * W) return 2;
    M = malloc(sizeof(int) * N * N); INV = malloc(sizeof(int) * N);
    for (int i = 0; i < N * N; i++) if (fscanf(f, "%d", &M[i]) != 1) return 2;
    for (int a = 0; a < N; a++) for (int b = 0; b < N; b++) if (M[a * N + b] == 0) INV[a] = b;
    int k; if (fscanf(f, "%d", &k) != 1) return 2;
    int *par = malloc(sizeof(int) * N * N);
    for (int i = 0; i < N * N; i++) par[i] = i;
    int *g = malloc(sizeof(int) * N);
    for (int a = 0; a < k; a++) {
        for (int i = 0; i < N; i++) if (fscanf(f, "%d", &g[i]) != 1) return 2;
        for (int x = 1; x < N; x++) for (int y = 1; y < N; y++) if (x != y) {
            int u = find(par, x * N + y), v = find(par, g[x] * N + g[y]);
            if (u != v) { if (u < v) par[v] = u; else par[u] = v; }
        }
    }
    fclose(f);
    CL = malloc(sizeof(int) * N * N);
    for (int i = 0; i < N * N; i++) CL[i] = find(par, i);   /* union by smaller index: root = class minimum */
    int npairs = 0; int *pr = malloc(sizeof(int) * N * N);
    for (int x = 1; x < N; x++) for (int y = 1; y < N; y++) if (x != y && CL[x * N + y] == x * N + y) pr[npairs++] = x * N + y;
    int p0 = argc > 3 ? atoi(argv[2]) : 0, p1 = argc > 3 ? atoi(argv[3]) : npairs;
    printf("N=%d automorphism generators=%d pair classes=%d, doing %d..%d\n", N, k, npairs, p0, p1); fflush(stdout);
    long total = 0, nvalid = 0, naside = 0; int gmin = N;
    for (int p = p0; p < p1 && p < npairs; p++) {
        int cur = pr[p];
        int S[6]; S[0] = 0; S[1] = cur / N; S[2] = cur % N;
        if (bad(S, 3, cur)) continue;
        int pmin = N; long pl = 0;
        for (int a = 1; a < N; a++) {
            if (a == S[1] || a == S[2]) continue;
            S[3] = a; if (bad(S, 4, cur)) continue;
            for (int b = a + 1; b < N; b++) {
                if (b == S[1] || b == S[2]) continue;
                S[4] = b; if (bad(S, 5, cur)) continue;
                int Q5[32], n5 = 0;
                for (int i = 0; i < 5; i++) for (int j = 0; j < 5; j++) if (i != j) Q5[n5++] = mul(INV[S[i]], S[j]);
                Q5[n5++] = 0;
                uint64_t c5[W] = {0};
                for (int i = 0; i < n5; i++) { const int *row = M + Q5[i] * N; for (int j = 0; j < n5; j++) { int x = row[Q5[j]]; c5[x >> 6] |= 1ULL << (x & 63); } }
                for (int c = b + 1; c < N; c++) {
                    if (c == S[1] || c == S[2]) continue;
                    pl++;
                    int Qn[10], nn = 0;
                    for (int i = 0; i < 5; i++) { Qn[nn++] = mul(INV[c], S[i]); Qn[nn++] = mul(INV[S[i]], c); }
                    uint64_t cv[W]; memcpy(cv, c5, sizeof cv);
                    for (int i = 0; i < nn; i++) {
                        const int *row = M + Qn[i] * N;
                        for (int j = 0; j < n5; j++) { int x = row[Q5[j]]; cv[x >> 6] |= 1ULL << (x & 63); }
                        for (int j = 0; j < nn; j++) { int x = row[Qn[j]]; cv[x >> 6] |= 1ULL << (x & 63); }
                    }
                    for (int i = 0; i < n5; i++) { const int *row = M + Q5[i] * N; for (int j = 0; j < nn; j++) { int x = row[Qn[j]]; cv[x >> 6] |= 1ULL << (x & 63); } }
                    int t = 0; for (int w = 0; w < W; w++) t += __builtin_popcountll(cv[w]);
                    int unc = N - t;
                    if (unc < pmin) pmin = unc;
                    if (unc == 0) {
                        S[5] = c; naside++;
                        int P[32], npp = 0;
                        for (int i = 0; i < 6; i++) for (int j = 0; j < 6; j++) if (i != j) P[npp++] = mul(S[i], INV[S[j]]);
                        P[npp++] = 0;
                        int tb = cover_count(P, npp);
                        if (tb == N) { nvalid++; printf("VALID S = %d %d %d %d %d %d\n", S[0], S[1], S[2], S[3], S[4], S[5]); fflush(stdout); }
                        else if (N - tb < 4) printf("ASIDE S = %d %d %d %d %d %d Bunc=%d\n", S[0], S[1], S[2], S[3], S[4], S[5], N - tb);
                    }
                }
            }
        }
        total += pl;
        if (pmin < gmin) gmin = pmin;
        printf("PAIR %d r=%d r2=%d sets=%ld minA=%d\n", p, S[1], S[2], pl, pmin); fflush(stdout);
    }
    printf("DONE N=%d pairs=%d..%d sets=%ld Acovered=%ld valid=%ld minA=%d\n", N, p0, p1, total, naside, nvalid, gmin);
    return 0;
}
