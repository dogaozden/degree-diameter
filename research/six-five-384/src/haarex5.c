/* haarex5.c (was squad card s384r1-c1, haarex4_c1.c): haarex4 (research/six-five-384/src/haarex4.c) with the work of each 4-prefix P4 = {e, r, r2, a}
 * reused across the choices of b (squad s384r1, card c1). The enumeration (pair classes, orderly pruning, prefixes
 * {e, r, r2, a, b}, last element c > b solved exactly), the move-to-front target order and the PAIR / ASIDE /
 * VALID / DONE output are those of haarex4. What changes is where the work is done:
 *   - Q4 = {s^-1 t : s != t in P4} u {e} and cov4 = Q4 Q4 depend only on P4. Q5 = Q4 u Qb with
 *     Qb = {s^-1 b, b^-1 s : s in P4}, so Q4 Q4 is inside Q5 Q5 for every b: a target x in cov4 is skipped at once.
 *   - the b-free part A4(x) of the solution set of x (words with s, t in P4 and q in Q4) does not depend on b. It is
 *     computed once per (P4, x) when x is first needed and cached (stamp = P4 counter, so no clearing per b).
 *     Per b only the b-involving words are added (add_B): s = b with any q in Q5, or s in P4 with q in Qb; and the
 *     forms with s = b or t = b (forms567 with si = 4 or ti = 4).
 *   - bad(S,5) is replaced by bad_b, which only checks the terms with index 4 (= b); the terms without b are the
 *     terms of bad(S,4), which already passed for this P4.
 * Word forms for x missed by Q5 Q5 (q in Q5, s, t in P5, c the last element; formula for c given x):
 *   q s^-1 c = x : c = (s q^-1) x             SQi table     split: A4 (s in P4, q in Q4) / add_B (rest)
 *   c^-1 s q = x : c = (s q) x^-1             SQp table     split: as above
 *   q c^-1 s = x : c = (s x^-1) q             r1 table      split: as above
 *   s^-1 c q = x : c = (s x) q^-1             r2 table      split: as above
 *   c^-1 s c^-1 t = x, s^-1 c t^-1 c = x, c^-1 s t^-1 c = x (s != t)   forms567(si, ti)
 *                                             split: A4 for si, ti < 4, add_B when si = 4 or ti = 4
 * The candidate-testing branch (at most SMALL candidates left) is unchanged, with the same forms.
 * input: as haarex2/haarex3/haarex4 (N, table, k, k automorphism permutations). usage: haarex4_c1 FILE [PAIRFROM PAIRTO]
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

/* bad(P, 5, cur) for P[4] = b, given bad(P, 4, cur) == 0: only the terms that involve index 4 */
static inline int tval(int x, int t, int tinv, int mode) {
    switch (mode) {
        case 0: return mul(x, tinv);
        case 1: return mul(tinv, x);
        case 2: return mul(INV[x], t);
        default: return mul(t, INV[x]);
    }
}
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
    uint64_t c[W] = {0};
    for (int i = 0; i < nq; i++) { const uint16_t *row = M + Q[i] * N; for (int j = 0; j < nq; j++) { int x = row[Q[j]]; c[x >> 6] |= 1ULL << (x & 63); } }
    int t = 0; for (int w = 0; w < W; w++) t += __builtin_popcountll(c[w]);
    return t;
}

static int *SQOFF, *SQ, *CJOFF, *CJ;
static inline void setb(uint64_t *b, int c) { b[c >> 6] |= 1ULL << (c & 63); }
static inline int hasb(const uint64_t *b, int c) { return (int)((b[c >> 6] >> (c & 63)) & 1); }

/* solutions c (added to out) of the words with s = S[si], t = S[ti] and target x:
 *   c^-1 s c^-1 t = x   <=> c = s w^-1 with w^2 = x t^-1 s,
 *   s^-1 c t^-1 c = x   <=> c = w t with w^2 = s x t^-1,
 *   c^-1 s t^-1 c = x   <=> c in CJ[s t^-1][x] (s != t). */
static inline void forms567(const int *S, int si, int ti, int x, uint64_t *out) {
    int s = S[si], tt = S[ti];
    int z1 = mul(mul(x, INV[tt]), s);
    for (int u = SQOFF[z1]; u < SQOFF[z1 + 1]; u++) { int c = mul(s, INV[SQ[u]]); setb(out, c); }
    int z2 = mul(mul(s, x), INV[tt]);
    for (int u = SQOFF[z2]; u < SQOFF[z2 + 1]; u++) { int c = mul(SQ[u], tt); setb(out, c); }
    if (ti != si) { int y = mul(s, INV[tt]), yx = y * N + x;
        for (int u = CJOFF[yx]; u < CJOFF[yx + 1]; u++) setb(out, CJ[u]); }
}

/* b-free part of the solution set of x for the 4-prefix S[0..3]: s in P4, q in Q4 (the four q-forms), and the
 * forms567 with si, ti < 4. Result is independent of b and of cand. */
static void build_A4(const int *S, const int *Q4, int n4, int x, uint64_t *out) {
    int xi = INV[x];
    const uint16_t *colx = MT + x * N, *colxi = MT + xi * N;
    for (int w = 0; w < W; w++) out[w] = 0;
    for (int si = 0; si < 4; si++) {
        int s = S[si];
        const uint16_t *r1 = M + mul(s, xi) * N, *r2 = M + mul(s, x) * N;
        for (int qi = 0; qi < n4; qi++) {
            int q = Q4[qi], qinv = INV[q];
            setb(out, colx[mul(s, qinv)]);      /* q s^-1 c = x */
            setb(out, colxi[mul(s, q)]);        /* c^-1 s q = x */
            setb(out, r1[q]);                   /* q c^-1 s = x */
            setb(out, r2[qinv]);                /* s^-1 c q = x */
        }
        for (int ti = 0; ti < 4; ti++) forms567(S, si, ti, x, out);
    }
}

/* b-involving part for the current b: the q-forms with (s, q) in the list bsi/bq (s = S[bsi], q = bq), and the
 * forms567 with si = 4 or ti = 4. The list is 21 pairs (s = b, q in Q5) and 32 pairs (s in P4, q in Qb). */
static int nbp, bsi[64], bq[64], bqi[64], bsqi[64], bsqp[64];
static void add_B(const int *S, int x, uint64_t *out) {
    int xi = INV[x];
    const uint16_t *colx = MT + x * N, *colxi = MT + xi * N;
    int SX[5], SXI[5];
    for (int si = 0; si < 5; si++) { SX[si] = mul(S[si], x); SXI[si] = mul(S[si], xi); }
    for (int k = 0; k < nbp; k++) {
        setb(out, colx[bsqi[k]]);                         /* q s^-1 c = x */
        setb(out, colxi[bsqp[k]]);                        /* c^-1 s q = x */
        setb(out, M[SXI[bsi[k]] * N + bq[k]]);            /* q c^-1 s = x */
        setb(out, M[SX[bsi[k]] * N + bqi[k]]);            /* s^-1 c q = x */
    }
    for (int si = 0; si < 5; si++) for (int ti = 0; ti < 5; ti++)
        if (si == 4 || ti == 4) forms567(S, si, ti, x, out);
}

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
    printf("N=%d automorphism generators=%d pair classes=%d, doing %d..%d (haarex5)\n", N, k, npairs, p0, p1); fflush(stdout);
    uint64_t *GT = calloc((size_t)N * W, sizeof(uint64_t));   /* GT[b] = {c : c > b} */
    for (int b = 0; b < N; b++) for (int c = b + 1; c < N; c++) setb(GT + (size_t)b * W, c);
    uint64_t *ACH = malloc(sizeof(uint64_t) * N * W);   /* cached A4(x) per x, valid when ASTAMP[x] == pid */
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
            uint64_t q4b[W] = {0}, cov4[W] = {0};
            for (int i = 0; i < n4; i++) setb(q4b, Q4[i]);
            for (int i = 0; i < n4; i++) for (int j = 0; j < n4; j++) setb(cov4, mul(Q4[i], Q4[j]));
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
                uint64_t q5b[W];
                memcpy(q5b, q4b, sizeof q5b);
                for (int i = 0; i < nqb; i++) setb(q5b, Qb[i]);
                /* b-involving q-form products: (s = b, q in Q5) and (s in P4, q in Qb) */
                nbp = 0;
                for (int qi = 0; qi < n5; qi++) { int q = Q5[qi], qinv = INV[q];
                    bsi[nbp] = 4; bq[nbp] = q; bqi[nbp] = qinv; bsqi[nbp] = mul(b, qinv); bsqp[nbp] = mul(b, q); nbp++; }
                for (int si = 0; si < 4; si++) for (int kk = 0; kk < nqb; kk++) { int q = Qb[kk], qinv = INV[q], s = S[si];
                    bsi[nbp] = si; bq[nbp] = q; bqi[nbp] = qinv; bsqi[nbp] = mul(s, qinv); bsqp[nbp] = mul(s, q); nbp++; }
                uint64_t cand[W];   /* c > b, c != r, r2 */
                memcpy(cand, GT + (size_t)b * W, sizeof cand);
                cand[S[1] >> 6] &= ~(1ULL << (S[1] & 63)); cand[S[2] >> 6] &= ~(1ULL << (S[2] & 63));
                int ncand = -1, clist[512];
                int empty = 0;
                for (int t = 0; t < N && !empty; t++) {
                    int x = ord[t];
                    if (hasb(cov4, x)) continue;            /* x in Q4 Q4 <= Q5 Q5 */
                    /* x in Q5 Q5 iff q x in Q5 for some q in Q5 (Q5 = Q5^-1) */
                    { const uint16_t *colx = MT + x * N; int in = 0;
                      for (int qi = 0; qi < n5; qi++) if (hasb(q5b, colx[Q5[qi]])) { in = 1; break; }
                      if (in) continue; }
                    if (ncand < 0) {
                        uint64_t ax[W];
                        if (ASTAMP[x] != pid) { build_A4(S, Q4, n4, x, ACH + (size_t)x * W); ASTAMP[x] = pid; }
                        memcpy(ax, ACH + (size_t)x * W, sizeof ax);
                        add_B(S, x, ax);
                        int cnt = 0; for (int w = 0; w < W; w++) { cand[w] &= ax[w]; cnt += __builtin_popcountll(cand[w]); }
                        if (cnt == 0) empty = 1;
                        else if (cnt <= SMALL) { ncand = 0; for (int w = 0; w < W; w++) { uint64_t m = cand[w]; while (m) { clist[ncand++] = w * 64 + __builtin_ctzll(m); m &= m - 1; } } }
                    } else {
                        /* test each remaining candidate c against x (same word forms as build_A4 / add_B) */
                        int keep = 0;
                        for (int ci = 0; ci < ncand; ci++) {
                            int c = clist[ci], cinv = INV[c], ok = 0;
                            for (int si = 0; si < 5 && !ok; si++) { int s = S[si], sinv = INV[s];
                                /* q c^-1 s = x: q = x s^-1 c; q s^-1 c = x: q = x c^-1 s; c^-1 s q = x: q = s^-1 c x; s^-1 c q = x: q = c^-1 s x */
                                if (hasb(q5b, mul(mul(x, sinv), c)) || hasb(q5b, mul(mul(x, cinv), s)) ||
                                    hasb(q5b, mul(mul(sinv, c), x)) || hasb(q5b, mul(mul(cinv, s), x))) { ok = 1; break; }
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
