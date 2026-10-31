/* haarex6.c (was squad s384r2 card c1, haarex5_c1.c): haarex5 (research/six-five-384/src/haarex5.c) with c2's low-level changes
 * (squad s384r1, haarex4_c2.c) ported. Every solution set is a byte array with store-only marks (0/1 per
 * group element) instead of a 512-bit bitset with read-modify-write setb: the cached b-free A4(x), the per-b add_B
 * part, the candidate set and the cov4 / Q5 membership marks. Enumeration, move-to-front target order, the cached
 * A4(x) (per 4-prefix), bad / bad_b and the output are those of haarex5, so the output is identical.
 * usage: haarex5_c1 FILE [PAIRFROM PAIRTO]   env SMALL (default 6).
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

#define MAXN 512
static int N, *INV, *CL;
static uint16_t *M, *MT;     /* MT[x*N + y] = M[y*N + x] */
static inline int mul(int a, int b) { return M[a * N + b]; }

static int find(int *p, int x) { while (p[x] != x) { p[x] = p[p[x]]; x = p[x]; } return x; }

static int bad(const int *P, int np, int cur) {
    int T[6];
    for (int ti = 0; ti < np; ti++) {
        int t = P[ti], ti_inv = INV[t];
        for (int mode = 0; mode < 4; mode++) {
            for (int i = 0; i < np; i++) {
                int x = P[i];
                switch (mode) {
                    case 0: T[i] = mul(x, ti_inv); break;
                    case 1: T[i] = mul(ti_inv, x); break;
                    case 2: T[i] = mul(INV[x], t); break;
                    default: T[i] = mul(t, INV[x]); break;
                }
            }
            for (int i = 0; i < np; i++) { if (T[i] == 0) continue;
                for (int j = 0; j < np; j++) { if (j == i || T[j] == 0) continue;
                    if (CL[T[i] * N + T[j]] < cur) return 1; } }
        }
    }
    return 0;
}

static inline int tval(int x, int t, int tinv, int mode) {
    switch (mode) {
        case 0: return mul(x, tinv);
        case 1: return mul(tinv, x);
        case 2: return mul(INV[x], t);
        default: return mul(t, INV[x]);
    }
}
/* bad(P, 5, cur) for P[4] = b, given bad(P, 4, cur) == 0: only the terms that involve index 4 */
static int bad_b(const int *P, int cur) {
    int T[5];
    for (int mode = 0; mode < 4; mode++) {                 /* t = b: all ordered pairs (i, j) */
        int t = P[4], tinv = INV[t];
        for (int i = 0; i < 5; i++) T[i] = tval(P[i], t, tinv, mode);
        for (int i = 0; i < 5; i++) { if (T[i] == 0) continue;
            for (int j = 0; j < 5; j++) { if (j == i || T[j] == 0) continue;
                if (CL[T[i] * N + T[j]] < cur) return 1; } }
    }
    for (int ti = 0; ti < 4; ti++) {                       /* t in P4: pairs with 4 in {i, j} */
        int t = P[ti], tinv = INV[t];
        for (int mode = 0; mode < 4; mode++) {
            for (int i = 0; i < 5; i++) T[i] = tval(P[i], t, tinv, mode);
            if (T[4] == 0) continue;
            for (int j = 0; j < 4; j++) if (T[j] && CL[T[4] * N + T[j]] < cur) return 1;
            for (int i = 0; i < 4; i++) if (T[i] && CL[T[i] * N + T[4]] < cur) return 1;
        }
    }
    return 0;
}

static int cover_count(const int *Q, int nq) {
    uint64_t c[8] = {0};
    for (int i = 0; i < nq; i++) { const uint16_t *row = M + Q[i] * N; for (int j = 0; j < nq; j++) { int x = row[Q[j]]; c[x >> 6] |= 1ULL << (x & 63); } }
    int t = 0; for (int w = 0; w < 8; w++) t += __builtin_popcountll(c[w]);
    return t;
}

static int *SQOFF, *SQ, *CJOFF;
static uint16_t *CJ;

/* solutions c (marked in out) of the words with s = S[si], t = S[ti] and target x:
 *   c^-1 s c^-1 t = x   <=> c = s w^-1 with w^2 = x t^-1 s,
 *   s^-1 c t^-1 c = x   <=> c = w t with w^2 = s x t^-1,
 *   c^-1 s t^-1 c = x   <=> c in CJ[s t^-1][x] (s != t). */
static inline void forms567(const int *S, int si, int ti, int x, uint8_t *out) {
    int s = S[si], tt = S[ti];
    int z1 = mul(mul(x, INV[tt]), s);
    for (int u = SQOFF[z1]; u < SQOFF[z1 + 1]; u++) out[mul(s, INV[SQ[u]])] = 1;
    int z2 = mul(mul(s, x), INV[tt]);
    for (int u = SQOFF[z2]; u < SQOFF[z2 + 1]; u++) out[mul(SQ[u], tt)] = 1;
    if (ti != si) { int y = mul(s, INV[tt]), yx = y * N + x;
        for (int u = CJOFF[yx]; u < CJOFF[yx + 1]; u++) out[CJ[u]] = 1; }
}

/* b-free part of the solution set of x for the 4-prefix S[0..3]: s in P4, q in Q4 (the four q-forms), and the
 * forms567 with si, ti < 4. Result is independent of b and of cand. */
static void build_A4(const int *S, const int *Q4, int n4, int x, uint8_t *out) {
    int xi = INV[x];
    const uint16_t *colx = MT + x * N, *colxi = MT + xi * N;
    memset(out, 0, N);
    for (int si = 0; si < 4; si++) {
        int s = S[si];
        const uint16_t *r1 = M + mul(s, xi) * N, *r2 = M + mul(s, x) * N;
        for (int qi = 0; qi < n4; qi++) {
            int q = Q4[qi], qinv = INV[q];
            out[colx[mul(s, qinv)]] = 1;      /* q s^-1 c = x */
            out[colxi[mul(s, q)]] = 1;        /* c^-1 s q = x */
            out[r1[q]] = 1;                   /* q c^-1 s = x */
            out[r2[qinv]] = 1;                /* s^-1 c q = x */
        }
        for (int ti = 0; ti < 4; ti++) forms567(S, si, ti, x, out);
    }
}

/* b-involving part for the current b: the q-forms with (s, q) in the list bsi/bq (s = S[bsi], q = bq), and the
 * forms567 with si = 4 or ti = 4. The list is 21 pairs (s = b, q in Q5) and 32 pairs (s in P4, q in Qb). */
static int nbp, bsi[64], bq[64], bqi[64], bsqi[64], bsqp[64];
static void add_B(const int *S, int x, uint8_t *out) {
    int xi = INV[x];
    const uint16_t *colx = MT + x * N, *colxi = MT + xi * N;
    int SXN[5], SXIN[5];   /* row offsets (x-dependent) of M for the s-rows */
    for (int si = 0; si < 5; si++) { SXN[si] = mul(S[si], x) * N; SXIN[si] = mul(S[si], xi) * N; }
    for (int k = 0; k < nbp; k++) {
        out[colx[bsqi[k]]] = 1;                         /* q s^-1 c = x */
        out[colxi[bsqp[k]]] = 1;                        /* c^-1 s q = x */
        out[M[SXIN[bsi[k]] + bq[k]]] = 1;               /* q c^-1 s = x */
        out[M[SXN[bsi[k]] + bqi[k]]] = 1;               /* s^-1 c q = x */
    }
    for (int si = 0; si < 5; si++) for (int ti = 0; ti < 5; ti++)
        if (si == 4 || ti == 4) forms567(S, si, ti, x, out);
}

int main(int argc, char **argv) {
    FILE *f = fopen(argv[1], "r"); if (!f) return 2;
    if (fscanf(f, "%d", &N) != 1 || N > MAXN) return 2;
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
    int npairs = 0; int *pr = malloc(sizeof(int) * N * N);
    for (int x = 1; x < N; x++) for (int y = 1; y < N; y++) if (x != y && CL[x * N + y] == x * N + y) pr[npairs++] = x * N + y;
    SQOFF = calloc(N + 1, sizeof(int)); SQ = malloc(sizeof(int) * N);
    for (int w = 0; w < N; w++) SQOFF[mul(w, w) + 1]++;
    for (int z = 0; z < N; z++) SQOFF[z + 1] += SQOFF[z];
    { int *fill = calloc(N, sizeof(int)); for (int w = 0; w < N; w++) { int z = mul(w, w); SQ[SQOFF[z] + fill[z]++] = w; } free(fill); }
    CJOFF = calloc((size_t)N * N + 1, sizeof(int)); CJ = malloc(sizeof(uint16_t) * N * N);
    for (int y = 0; y < N; y++) for (int c = 0; c < N; c++) CJOFF[y * N + mul(mul(INV[c], y), c) + 1]++;
    for (int i = 0; i < N * N; i++) CJOFF[i + 1] += CJOFF[i];
    { int *fill = calloc((size_t)N * N, sizeof(int));
      for (int y = 0; y < N; y++) for (int c = 0; c < N; c++) { int x = mul(mul(INV[c], y), c); CJ[CJOFF[y * N + x] + fill[y * N + x]++] = (uint16_t)c; }
      free(fill); }
    int SMALL = getenv("SMALL") ? atoi(getenv("SMALL")) : 6;
    int *ord = malloc(sizeof(int) * N); for (int i = 0; i < N; i++) ord[i] = i;   /* move-to-front target order */
    int p0 = argc > 3 ? atoi(argv[2]) : 0, p1 = argc > 3 ? atoi(argv[3]) : npairs;
    printf("N=%d automorphism generators=%d pair classes=%d, doing %d..%d (haarex6)\n", N, k, npairs, p0, p1); fflush(stdout);
    uint8_t *GTb = malloc((size_t)N * N);   /* GTb[b*N + c] = (c > b) */
    for (int b = 0; b < N; b++) for (int c = 0; c < N; c++) GTb[b * N + c] = (c > b);
    uint8_t *ACH = malloc((size_t)N * N);   /* cached A4(x) per x, valid when ASTAMP[x] == pid */
    long *ASTAMP = calloc(N, sizeof(long));
    long pid = 0;
    long total = 0, nvalid = 0, naside = 0, nprefix = 0; int gminA = -1;
    for (int p = p0; p < p1 && p < npairs; p++) {
        int cur = pr[p];
        int S[6]; S[0] = 0; S[1] = cur / N; S[2] = cur % N;
        if (bad(S, 3, cur)) continue;
        long pl = 0; int pminA = -1;
        for (int a = 1; a < N; a++) {
            if (a == S[1] || a == S[2]) continue;
            S[3] = a; if (bad(S, 4, cur)) continue;
            /* new 4-prefix {e, r, r2, a}: b-free data */
            pid++;
            int Q4[16], n4 = 0;
            Q4[n4++] = 0;
            for (int i = 0; i < 4; i++) for (int j = 0; j < 4; j++) if (i != j) Q4[n4++] = mul(INV[S[i]], S[j]);
            uint8_t q4m[MAXN] = {0}, cov4[MAXN] = {0};
            for (int i = 0; i < n4; i++) q4m[Q4[i]] = 1;
            for (int i = 0; i < n4; i++) for (int j = 0; j < n4; j++) cov4[mul(Q4[i], Q4[j])] = 1;
            for (int b = a + 1; b < N; b++) {
                if (b == S[1] || b == S[2]) continue;
                S[4] = b; if (bad_b(S, cur)) continue;
                nprefix++;
                int Qb[8], nqb = 0;
                for (int si = 0; si < 4; si++) Qb[nqb++] = mul(INV[S[si]], b);   /* s^-1 b */
                for (int si = 0; si < 4; si++) Qb[nqb++] = mul(INV[b], S[si]);   /* b^-1 s */
                int Q5[32], n5 = 0;
                for (int i = 0; i < n4; i++) Q5[n5++] = Q4[i];
                for (int i = 0; i < nqb; i++) Q5[n5++] = Qb[i];
                uint8_t q5m[MAXN];
                memcpy(q5m, q4m, N);
                for (int i = 0; i < nqb; i++) q5m[Qb[i]] = 1;
                /* b-involving q-form products: (s = b, q in Q5) and (s in P4, q in Qb) */
                nbp = 0;
                for (int qi = 0; qi < n5; qi++) { int q = Q5[qi], qinv = INV[q];
                    bsi[nbp] = 4; bq[nbp] = q; bqi[nbp] = qinv; bsqi[nbp] = mul(b, qinv); bsqp[nbp] = mul(b, q); nbp++; }
                for (int si = 0; si < 4; si++) for (int kk = 0; kk < nqb; kk++) { int q = Qb[kk], qinv = INV[q], s = S[si];
                    bsi[nbp] = si; bq[nbp] = q; bqi[nbp] = qinv; bsqi[nbp] = mul(s, qinv); bsqp[nbp] = mul(s, q); nbp++; }
                uint8_t cand[MAXN];   /* c > b, c != r, r2 */
                memcpy(cand, GTb + (size_t)b * N, N);
                cand[S[1]] = 0; cand[S[2]] = 0;
                int ncand = -1, clist[512];
                int empty = 0;
                for (int t = 0; t < N && !empty; t++) {
                    int x = ord[t];
                    if (cov4[x]) continue;                  /* x in Q4 Q4 <= Q5 Q5 */
                    /* x in Q5 Q5 iff q x in Q5 for some q in Q5 (Q5 = Q5^-1) */
                    { const uint16_t *colx = MT + x * N; int in = 0;
                      for (int qi = 0; qi < n5; qi++) if (q5m[colx[Q5[qi]]]) { in = 1; break; }
                      if (in) continue; }
                    if (ncand < 0) {
                        uint8_t ax[MAXN];
                        if (ASTAMP[x] != pid) { build_A4(S, Q4, n4, x, ACH + (size_t)x * N); ASTAMP[x] = pid; }
                        memcpy(ax, ACH + (size_t)x * N, N);
                        add_B(S, x, ax);
                        int cnt = 0; for (int c = 0; c < N; c++) { cand[c] &= ax[c]; cnt += cand[c]; }
                        if (cnt == 0) empty = 1;
                        else if (cnt <= SMALL) { ncand = 0; for (int c = 0; c < N; c++) { clist[ncand] = c; ncand += cand[c]; } }
                    } else {
                        /* test each remaining candidate c against x (same word forms as build_A4 / add_B) */
                        int keep = 0;
                        for (int ci = 0; ci < ncand; ci++) {
                            int c = clist[ci], cinv = INV[c], ok = 0;
                            for (int si = 0; si < 5 && !ok; si++) { int s = S[si], sinv = INV[s];
                                /* q c^-1 s = x: q = x s^-1 c; q s^-1 c = x: q = x c^-1 s; c^-1 s q = x: q = s^-1 c x; s^-1 c q = x: q = c^-1 s x */
                                if (q5m[mul(mul(x, sinv), c)] || q5m[mul(mul(x, cinv), s)] ||
                                    q5m[mul(mul(sinv, c), x)] || q5m[mul(mul(cinv, s), x)]) { ok = 1; break; }
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
                if (ncand < 0) { ncand = 0; for (int c = 0; c < N; c++) { clist[ncand] = c; ncand += cand[c]; } }
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
