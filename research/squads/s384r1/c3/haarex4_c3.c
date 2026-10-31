/* haarex4.c: haarex3 (research/s65/tools/haarex3.c, exhaustive orderly Haar search at (6,5)) made faster for
 * order-384 groups (job six-five-384). The enumeration (pair classes, orderly pruning by bad(), prefixes
 * {e, r, r2, a, b}, last element c > b solved exactly) is unchanged, so the PAIR / ASIDE / VALID / DONE output is
 * identical to haarex3's (checked on calibration groups). Changes, all in the per-prefix work:
 *   - the x-independent products s q^-1, s q (s in the prefix, q in Q5 = prefix^-1 prefix) are computed once per
 *     prefix, and a transposed table gives the c = (s q^-1) x and c = (s q) x^-1 solutions with one lookup each;
 *   - missed targets x are taken in move-to-front order (a target that empties the candidate set moves forward);
 *   - Q5 Q5 is not built; a target x is tested lazily (x in Q5 Q5 iff q x in Q5 for some q in Q5);
 *   - once at most SMALL candidates remain, each candidate c is tested directly against the remaining targets
 *     (is x the value of a word containing c?) instead of building the full solution set of the next target.
 * Word forms for x missed by Q5 Q5 (q in Q5, s, t in the prefix; words with c):
 *   q c^-1 s, q s^-1 c, c^-1 s q, s^-1 c q, c^-1 s c^-1 t, s^-1 c t^-1 c, c^-1 s t^-1 c (s != t).
 * input: as haarex2/haarex3 (N, table, k, k automorphism permutations). usage: haarex4 FILE [PAIRFROM PAIRTO]
 * env SMALL (default 6).
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

#define W 8
static int N, *INV, *CL;
static uint16_t *M, *MT;     /* MT[x*N + y] = M[y*N + x] */
static inline int mul(int a, int b) { return M[a * N + b]; }

static int find(int *p, int x) { while (p[x] != x) { p[x] = p[p[x]]; x = p[x]; } return x; }

/* c3: RB[u*RW + w] has bit v iff u, v >= 1, u != v and CL[u*N+v] < cur (the current pair class minimum). Pairs are
 * switched on in increasing CL order as cur increases (LST, LPTR), so RB is one 24 KB table instead of CL reads.
 * bad() returns the same decisions as the CL version: F holds the nonzero-or-zero transformed values of one
 * (t, mode); the pair test is "some u in F has a row bit hitting F" (no diagonal bit, no zero row or column bit). */
#define RW 8
static uint64_t *RB;
static int *LST; static long NLST, LPTR;
static int cmpcl(const void *a, const void *b) { int x = CL[*(const int *)a], y = CL[*(const int *)b]; return (x > y) - (x < y); }
static uint64_t *CB;            /* CB[v*RW + w] has bit u iff RB[u] has bit v (column table) */
static uint64_t F4S[4][4][RW];  /* F4S[ti][mode]: bitset of the transforms of the 4-prefix for t = P4[ti] */
static const uint16_t *RA[4], *RBm[4], *RC[4], *RD[4];  /* row pointers for t = P4[ti] (see bad()) */
/* a-level precomputation for the 4-prefix P (P[0] = 0). Then bad5(b) decides bad(P + b) given bad(P) == 0 */
static void pre4(const int *P) {
    for (int ti = 0; ti < 4; ti++) {
        int t = P[ti], tinv = INV[t];
        RA[ti] = MT + (size_t)tinv * N; RBm[ti] = M + (size_t)tinv * N; RC[ti] = MT + (size_t)t * N; RD[ti] = M + (size_t)t * N;
        for (int m = 0; m < 4; m++) {
            uint64_t *F = F4S[ti][m];
            memset(F, 0, sizeof(uint64_t) * RW);
            for (int i = 0; i < 4; i++) {
                int x = P[i], xi = INV[x];
                int v = m == 0 ? RA[ti][x] : m == 1 ? RBm[ti][x] : m == 2 ? RC[ti][xi] : RD[ti][xi];
                F[v >> 6] |= 1ULL << (v & 63);
            }
        }
    }
}
/* bad(P5) for P5 = P4 + b, given bad(P4) == 0: new pairs come from (t in P4) with the new element v = f(b) against
 * the old transformed set, and from t = b, whose transformed set is {f_{b,m}(x) : x in P4} (f_{b,m}(b) = e). */
static int bad5(const int *P, int b) {
    int ib = INV[b];
    for (int ti = 0; ti < 4; ti++) {
        int v[4] = { RA[ti][b], RBm[ti][b], RC[ti][ib], RD[ti][ib] };
        for (int m = 0; m < 4; m++) {
            const uint64_t *F = F4S[ti][m], *R = RB + (size_t)v[m] * RW, *Cc = CB + (size_t)v[m] * RW;
            uint64_t acc = 0;
            for (int w = 0; w < RW; w++) acc |= (R[w] | Cc[w]) & F[w];
            if (acc) return 1;
        }
    }
    {
        int bi = b, bi2 = ib;
        for (int m = 0; m < 4; m++) {
            uint64_t F[RW] = {0}; int T[4];
            for (int i = 0; i < 4; i++) {
                int x = P[i], xi = INV[x], v;
                switch (m) {
                    case 0: v = M[x * N + bi2]; break;      /* x b^-1 */
                    case 1: v = M[bi2 * N + x]; break;      /* b^-1 x */
                    case 2: v = M[xi * N + bi]; break;      /* x^-1 b */
                    default: v = M[bi * N + xi]; break;     /* b x^-1 */
                }
                T[i] = v; F[v >> 6] |= 1ULL << (v & 63);
            }
            uint64_t acc = 0;
            for (int i = 0; i < 4; i++) { const uint64_t *R = RB + (size_t)T[i] * RW; for (int w = 0; w < RW; w++) acc |= R[w] & F[w]; }
            if (acc) return 1;
        }
    }
    return 0;
}

static int bad(const int *P, int np, int cur) {
    (void)cur;
    int xi[6];
    for (int i = 0; i < np; i++) xi[i] = INV[P[i]];
    for (int ti = 0; ti < np; ti++) {
        int t = P[ti], tinv = INV[t];
        /* mode 0: x tinv = MT[tinv][x]; mode 1: tinv x = M[tinv][x]; mode 2: x^-1 t = MT[t][x^-1]; mode 3: t x^-1 = M[t][x^-1] */
        const uint16_t *A = MT + (size_t)tinv * N, *B = M + (size_t)tinv * N, *C = MT + (size_t)t * N, *D = M + (size_t)t * N;
        for (int mode = 0; mode < 4; mode++) {
            uint64_t F[RW] = {0}; int T[6];
            for (int i = 0; i < np; i++) {
                int v = mode == 0 ? A[P[i]] : mode == 1 ? B[P[i]] : mode == 2 ? C[xi[i]] : D[xi[i]];
                T[i] = v; F[v >> 6] |= 1ULL << (v & 63);
            }
            uint64_t acc = 0;
            for (int i = 0; i < np; i++) { const uint64_t *R = RB + (size_t)T[i] * RW; for (int w = 0; w < RW; w++) acc |= R[w] & F[w]; }
            if (acc) return 1;
        }
    }
    return 0;
}

static int cover_count(const int *Q, int nq) {
    uint64_t c[W] = {0};
    for (int i = 0; i < nq; i++) { const uint16_t *row = M + Q[i] * N; for (int j = 0; j < nq; j++) { int x = row[Q[j]]; c[x >> 6] |= 1ULL << (x & 63); } }
    int t = 0; for (int w = 0; w < W; w++) t += __builtin_popcountll(c[w]);
    return t;
}

static int *SQOFF, *SQ, *CJOFF, *CJ;
#define SET(b, c) ((b)[(c) >> 6] |= 1ULL << ((c) & 63))
#define HAS(b, c) ((b)[(c) >> 6] >> ((c) & 63) & 1)

int main(int argc, char **argv) {
    FILE *f = fopen(argv[1], "r"); if (!f) return 2;
    if (fscanf(f, "%d", &N) != 1 || N > 64 * W) return 2;
    M = malloc(sizeof(uint16_t) * N * N); MT = malloc(sizeof(uint16_t) * N * N); INV = malloc(sizeof(int) * N);
    for (int i = 0; i < N * N; i++) { int v; if (fscanf(f, "%d", &v) != 1) return 2; M[i] = v; }
    for (int a = 0; a < N; a++) for (int b = 0; b < N; b++) { MT[b * N + a] = M[a * N + b]; if (M[a * N + b] == 0) INV[a] = b; }
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
    free(par);
    RB = calloc((size_t)N * RW, sizeof(uint64_t));
    CB = calloc((size_t)N * RW, sizeof(uint64_t));
    LST = malloc(sizeof(int) * N * N); NLST = 0; LPTR = 0;
    for (int x = 1; x < N; x++) for (int y = 1; y < N; y++) if (x != y) LST[NLST++] = x * N + y;
    qsort(LST, NLST, sizeof(int), cmpcl);
    int npairs = 0; int *pr = malloc(sizeof(int) * N * N);
    for (int x = 1; x < N; x++) for (int y = 1; y < N; y++) if (x != y && CL[x * N + y] == x * N + y) pr[npairs++] = x * N + y;
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
    int SMALL = getenv("SMALL") ? atoi(getenv("SMALL")) : 6;
    int *ord = malloc(sizeof(int) * N); for (int i = 0; i < N; i++) ord[i] = i;   /* move-to-front target order */
    int p0 = argc > 3 ? atoi(argv[2]) : 0, p1 = argc > 3 ? atoi(argv[3]) : npairs;
    printf("N=%d automorphism generators=%d pair classes=%d, doing %d..%d (haarex4 c3)\n", N, k, npairs, p0, p1); fflush(stdout);
    long total = 0, nvalid = 0, naside = 0, nprefix = 0; int gminA = -1;
    for (int p = p0; p < p1 && p < npairs; p++) {
        int cur = pr[p];
        while (LPTR < NLST && CL[LST[LPTR]] < cur) { int idx = LST[LPTR++]; int u = idx / N, v = idx % N; RB[(size_t)u * RW + (v >> 6)] |= 1ULL << (v & 63); CB[(size_t)v * RW + (u >> 6)] |= 1ULL << (u & 63); }
        int S[6]; S[0] = 0; S[1] = cur / N; S[2] = cur % N;
        if (bad(S, 3, cur)) continue;
        long pl = 0; int pminA = -1;
        for (int a = 1; a < N; a++) {
            if (a == S[1] || a == S[2]) continue;
            S[3] = a; if (bad(S, 4, cur)) continue;
            pre4(S);
            for (int b = a + 1; b < N; b++) {
                if (b == S[1] || b == S[2]) continue;
                S[4] = b; if (bad5(S, b)) continue;
                nprefix++;
                int Q5[32], n5 = 0;
                for (int i = 0; i < 5; i++) for (int j = 0; j < 5; j++) if (i != j) Q5[n5++] = mul(INV[S[i]], S[j]);
                Q5[n5++] = 0;
                uint64_t q5b[W] = {0};
                for (int i = 0; i < n5; i++) SET(q5b, Q5[i]);
                /* x-independent products */
                int SQi[5 * 32], SQp[5 * 32], np = 0;     /* s q^-1 and s q */
                for (int si = 0; si < 5; si++) for (int qi = 0; qi < n5; qi++) { SQi[np] = mul(S[si], INV[Q5[qi]]); SQp[np] = mul(S[si], Q5[qi]); np++; }
                uint64_t cand[W] = {0};
                for (int c = b + 1; c < N; c++) if (c != S[1] && c != S[2]) SET(cand, c);
                int ncand = -1, clist[512];
                int empty = 0;
                for (int t = 0; t < N && !empty; t++) {
                    int x = ord[t];
                    /* x in Q5 Q5 iff q x in Q5 for some q in Q5 (Q5 = Q5^-1) */
                    { const uint16_t *colx = MT + x * N; int in = 0;
                      for (int qi = 0; qi < n5; qi++) if (HAS(q5b, colx[Q5[qi]])) { in = 1; break; }
                      if (in) continue; }
                    int xi = INV[x];
                    if (ncand < 0) {
                        uint64_t ax[W] = {0};
                        const uint16_t *colx = MT + x * N, *colxi = MT + xi * N;
                        for (int u = 0; u < np; u++) { SET(ax, colx[SQi[u]]); SET(ax, colxi[SQp[u]]); }   /* (s q^-1) x, (s q) x^-1 */
                        for (int si = 0; si < 5; si++) { int s = S[si];
                            const uint16_t *r1 = M + mul(s, xi) * N, *r2 = M + mul(s, x) * N;           /* (s x^-1) q, (s x) q^-1 */
                            for (int qi = 0; qi < n5; qi++) { SET(ax, r1[Q5[qi]]); SET(ax, r2[INV[Q5[qi]]]); }
                            for (int ti = 0; ti < 5; ti++) { int tt = S[ti];
                                int z1 = mul(mul(x, INV[tt]), s);
                                for (int u = SQOFF[z1]; u < SQOFF[z1 + 1]; u++) { int c = mul(s, INV[SQ[u]]); SET(ax, c); }
                                int z2 = mul(mul(s, x), INV[tt]);
                                for (int u = SQOFF[z2]; u < SQOFF[z2 + 1]; u++) { int c = mul(SQ[u], tt); SET(ax, c); }
                                if (ti != si) { int y = mul(s, INV[tt]);
                                    for (int u = CJOFF[y * N + x]; u < CJOFF[y * N + x + 1]; u++) SET(ax, CJ[u]); }
                            }
                        }
                        int cnt = 0; for (int w = 0; w < W; w++) { cand[w] &= ax[w]; cnt += __builtin_popcountll(cand[w]); }
                        if (cnt == 0) empty = 1;
                        else if (cnt <= SMALL) { ncand = 0; for (int w = 0; w < W; w++) { uint64_t m = cand[w]; while (m) { clist[ncand++] = w * 64 + __builtin_ctzll(m); m &= m - 1; } } }
                    } else {
                        /* test each remaining candidate c against x */
                        int keep = 0;
                        for (int ci = 0; ci < ncand; ci++) {
                            int c = clist[ci], cinv = INV[c], ok = 0;
                            for (int si = 0; si < 5 && !ok; si++) { int s = S[si], sinv = INV[s];
                                /* q c^-1 s = x: q = x s^-1 c; q s^-1 c = x: q = x c^-1 s; c^-1 s q = x: q = s^-1 c x; s^-1 c q = x: q = c^-1 s x */
                                if (HAS(q5b, mul(mul(x, sinv), c)) || HAS(q5b, mul(mul(x, cinv), s)) ||
                                    HAS(q5b, mul(mul(sinv, c), x)) || HAS(q5b, mul(mul(cinv, s), x))) { ok = 1; break; }
                                int cs = mul(cinv, s), sc = mul(sinv, c);
                                for (int ti = 0; ti < 5; ti++) { int tt = S[ti];
                                    if (mul(cs, mul(cinv, tt)) == x || mul(sc, mul(INV[tt], c)) == x || (ti != si && mul(cs, mul(INV[tt], c)) == x)) { ok = 1; break; }
                                }
                            }
                            if (ok) clist[keep++] = c;
                        }
                        ncand = keep;
                        if (!ncand) empty = 1;
                    }
                    if (empty && t) { int u = t / 2; int z = ord[t]; ord[t] = ord[u]; ord[u] = z; }
                }
                if (empty) continue;
                if (ncand < 0) { ncand = 0; for (int w = 0; w < W; w++) { uint64_t m = cand[w]; while (m) { clist[ncand++] = w * 64 + __builtin_ctzll(m); m &= m - 1; } } }
                for (int ci = 0; ci < ncand; ci++) {
                    int c = clist[ci];
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
