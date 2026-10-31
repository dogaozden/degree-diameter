/* haarex3.c: haarex2.c (exhaustive orderly Haar search at (6,5), job fresh-6-5) with the last element SOLVED instead
 * of enumerated (job squad-6-5). Same enumeration of S = {e, r, r2, a, b, c} and the same orderly pruning; for each
 * prefix {e, r, r2, a, b} the elements x missed by the prefix's own words (Q5 Q5, Q5 = prefix^-1 prefix) must each be
 * covered by a word containing c, and every such word is solved for c exactly:
 *   q c^-1 s = x  ->  c = s x^-1 q;      q s^-1 c = x  ->  c = s q^-1 x;
 *   c^-1 s q = x  ->  c = s q x^-1;      s^-1 c q = x  ->  c = s x q^-1;           (q in Q5, s in the prefix)
 *   c^-1 s c^-1 t = x  ->  c = s w^-1 with w^2 = x t^-1 s;   s^-1 c t^-1 c = x  ->  c = w t with w^2 = s x t^-1;
 *   c^-1 (s t^-1) c = x  ->  c in {c : c^-1 y c = x}  (y = s t^-1, s != t);
 *   (s^-1 c)(c^-1 t) = s^-1 t lies in Q5 already.
 * The candidate set for c is the intersection over the missed x of these solution sets (restricted to c > b,
 * c not in {r, r2}); every survivor covers side A exactly, and is then checked on side B as in haarex2. The exact
 * minimum of the side-A miss (minA of haarex2) is not computed: "minA" below is 0 if some S covers side A, else -1.
 * Output format as haarex2 (PAIR, ASIDE, VALID, DONE lines). Original header follows.
 *
 * Exhaustive Haar search at (6,5), orderly version (job fresh-6-5).
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


static int *SQOFF, *SQ;          /* square roots: SQ[SQOFF[z] .. SQOFF[z+1]) = all w with w*w = z */
static int *CJOFF, *CJ;          /* conjugators: for y, x: CJ[CJOFF[y*N+x] .. CJOFF[y*N+x+1]) = all c with c^-1 y c = x */

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
    for (int i = 0; i < N * N; i++) CL[i] = find(par, i);
    int npairs = 0; int *pr = malloc(sizeof(int) * N * N);
    for (int x = 1; x < N; x++) for (int y = 1; y < N; y++) if (x != y && CL[x * N + y] == x * N + y) pr[npairs++] = x * N + y;
    /* square-root and conjugator tables */
    SQOFF = calloc(N + 1, sizeof(int)); SQ = malloc(sizeof(int) * N);
    for (int w = 0; w < N; w++) SQOFF[mul(w, w) + 1]++;
    for (int z = 0; z < N; z++) SQOFF[z + 1] += SQOFF[z];
    { int *fill = calloc(N, sizeof(int)); for (int w = 0; w < N; w++) { int z = mul(w, w); SQ[SQOFF[z] + fill[z]++] = w; } free(fill); }
    CJOFF = calloc((size_t)N * N + 1, sizeof(int)); CJ = malloc(sizeof(int) * N * N);
    for (int y = 0; y < N; y++) for (int c = 0; c < N; c++) CJOFF[y * N + mul(mul(INV[c], y), c) + 1]++;
    for (int i = 0; i < N * N; i++) CJOFF[i + 1] += CJOFF[i];
    { int *fill = calloc((size_t)N * N, sizeof(int));
      for (int y = 0; y < N; y++) for (int c = 0; c < N; c++) { int x = mul(mul(INV[c], y), c); CJ[CJOFF[y * N + x] + fill[y * N + x]++] = c; }
      free(fill); }
    int p0 = argc > 3 ? atoi(argv[2]) : 0, p1 = argc > 3 ? atoi(argv[3]) : npairs;
    printf("N=%d automorphism generators=%d pair classes=%d, doing %d..%d (haarex3)\n", N, k, npairs, p0, p1); fflush(stdout);
    long total = 0, nvalid = 0, naside = 0, nprefix = 0; int gminA = -1;
    for (int p = p0; p < p1 && p < npairs; p++) {
        int cur = pr[p];
        int S[6]; S[0] = 0; S[1] = cur / N; S[2] = cur % N;
        if (bad(S, 3, cur)) continue;
        long pl = 0; int pminA = -1;
        for (int a = 1; a < N; a++) {
            if (a == S[1] || a == S[2]) continue;
            S[3] = a; if (bad(S, 4, cur)) continue;
            for (int b = a + 1; b < N; b++) {
                if (b == S[1] || b == S[2]) continue;
                S[4] = b; if (bad(S, 5, cur)) continue;
                nprefix++;
                int Q5[32], n5 = 0;
                for (int i = 0; i < 5; i++) for (int j = 0; j < 5; j++) if (i != j) Q5[n5++] = mul(INV[S[i]], S[j]);
                Q5[n5++] = 0;
                uint64_t c5[W] = {0};
                for (int i = 0; i < n5; i++) { const int *row = M + Q5[i] * N; for (int j = 0; j < n5; j++) { int x = row[Q5[j]]; c5[x >> 6] |= 1ULL << (x & 63); } }
                /* candidates: c > b, c != r, r2 */
                uint64_t cand[W] = {0};
                for (int c = b + 1; c < N; c++) if (c != S[1] && c != S[2]) cand[c >> 6] |= 1ULL << (c & 63);
                pl += 0;
                int empty = 0;
                for (int x = 0; x < N && !empty; x++) {
                    if (c5[x >> 6] >> (x & 63) & 1) continue;
                    uint64_t ax[W] = {0};
                    int xi = INV[x];
                    for (int si = 0; si < 5; si++) { int s = S[si];
                        for (int qi = 0; qi < n5; qi++) { int q = Q5[qi], c;
                            c = mul(mul(s, xi), q); ax[c >> 6] |= 1ULL << (c & 63);
                            c = mul(mul(s, INV[q]), x); ax[c >> 6] |= 1ULL << (c & 63);
                            c = mul(mul(s, q), xi); ax[c >> 6] |= 1ULL << (c & 63);
                            c = mul(mul(s, x), INV[q]); ax[c >> 6] |= 1ULL << (c & 63); }
                        for (int ti = 0; ti < 5; ti++) { int t = S[ti];
                            int z1 = mul(mul(x, INV[t]), s);              /* c = s w^-1, w^2 = x t^-1 s */
                            for (int u = SQOFF[z1]; u < SQOFF[z1 + 1]; u++) { int c = mul(s, INV[SQ[u]]); ax[c >> 6] |= 1ULL << (c & 63); }
                            int z2 = mul(mul(s, x), INV[t]);              /* c = w t, w^2 = s x t^-1 */
                            for (int u = SQOFF[z2]; u < SQOFF[z2 + 1]; u++) { int c = mul(SQ[u], t); ax[c >> 6] |= 1ULL << (c & 63); }
                            if (ti != si) { int y = mul(s, INV[t]);       /* c^-1 y c = x */
                                for (int u = CJOFF[y * N + x]; u < CJOFF[y * N + x + 1]; u++) { int c = CJ[u]; ax[c >> 6] |= 1ULL << (c & 63); } }
                        }
                    }
                    int any = 0; for (int w = 0; w < W; w++) { cand[w] &= ax[w]; any |= cand[w] != 0; }
                    if (!any) empty = 1;
                }
                if (empty) continue;
                /* every surviving c covers side A: check side B */
                for (int c = b + 1; c < N; c++) {
                    if (!(cand[c >> 6] >> (c & 63) & 1)) continue;
                    pl++; S[5] = c; naside++; pminA = 0;
                    int P[32], npp = 0;
                    for (int i = 0; i < 6; i++) for (int j = 0; j < 6; j++) if (i != j) P[npp++] = mul(S[i], INV[S[j]]);
                    P[npp++] = 0;
                    int tb = cover_count(P, npp);
                    if (tb == N) { nvalid++; printf("VALID S = %d %d %d %d %d %d\n", S[0], S[1], S[2], S[3], S[4], S[5]); fflush(stdout); }
                    else if (N - tb < 4) printf("ASIDE S = %d %d %d %d %d %d Bunc=%d\n", S[0], S[1], S[2], S[3], S[4], S[5], N - tb);
                }
            }
        }
        total += pl;
        if (pminA == 0) gminA = 0;
        printf("PAIR %d r=%d r2=%d acovers=%ld\n", p, S[1], S[2], pl); fflush(stdout);
    }
    printf("DONE N=%d pairs=%d..%d prefixes=%ld Acovered=%ld valid=%ld minA=%d\n", N, p0, p1, nprefix, naside, nvalid, gminA);
    return 0;
}
