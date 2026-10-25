/* place_anneal.c: card c3 of squad c157-r1 (cell (15,7)). Simulated annealing over K <= 32 freed flags (p_a, l_a),
   p_a on l_a, all p_a distinct and all l_a distinct.

   Objective: the signature deficit of regions.c, both halves together
       D = sum over nonempty signatures A of |#points with signature A - #lines with signature A|
   point u: signature {a : d(u,p_a)=4, d(u,l_a)=5};  line N: signature {a : d(N,l_a)=4, d(N,p_a)=5}.
   Moves: (a) l_a -> another line through p_a (prob 0.475); (b) p_a -> another point on l_a (0.475);
          (c) flag a -> random flag (0.05).

   Distances. If d(u,p)=4 with p on l, then d(u,l) is 3 or 5 (parity and the triangle inequality), and
   symmetrically for lines: d(N,l)=4 gives d(N,p) in {3,5}. So "d=5" can be tested as "not 3" once the
   element is known to be at distance 4, and a BFS to depth 4 is enough. Per flag a: uint8 arrays dp[a], dl[a]
   (2N entries, points first, then lines) hold the exact distances up to 4 (255 otherwise), and the lists
   P4[a] (points at distance 4 from p_a), L4[a] (lines at distance 4 from l_a).
   S'(p_a) = {u in P4[a] : dl[a][u] != 3},  S(l_a) = {N in L4[a] : dp[a][N] != 3}.

   Incremental evaluation. sigP[u] and sigL[N] keep bit a equal to membership. A move re-runs the BFS only for
   the moved endpoint and flips bit a only on the elements whose membership changes (about 30k per line or
   point move). Signature counts (points, lines) sit in an open-addressing hash table, so D changes per flip.
   A rejected move is undone by flipping the same elements again.

   Usage: place_anneal HEXBIN K SEED SECS OUT [CHECK]
     OUT gets the best flags as "p l" lines. CHECK > 0: every CHECK iterations the masks and D are rebuilt from
     scratch and compared (test mode). At the end D is recomputed with full BFS (regions.c method) for the
     initial and the best flags and printed. */

#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

typedef uint32_t sig_t;                         /* one bit per flag, K <= 32 */

static int q, N, Q1;
static int32_t *LP, *PL;                        /* line -> its q+1 points, point -> its q+1 lines */
static uint64_t rs = 88172645463325252ULL;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline int rndi(int n) { return (int)(rnd() % (uint64_t)n); }
static inline double rndu(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) { struct timespec ts; clock_gettime(CLOCK_MONOTONIC, &ts); return ts.tv_sec + 1e-9 * ts.tv_nsec; }

static void load(const char *fn) {
    FILE *f = fopen(fn, "rb");
    int32_t h[3];
    if (!f || fread(h, 4, 3, f) != 3) { fprintf(stderr, "cannot read %s\n", fn); exit(1); }
    q = h[0]; N = h[1]; Q1 = q + 1;
    LP = malloc(4L * N * Q1);
    if (fread(LP, 4, (size_t)N * Q1, f) != (size_t)N * Q1) { fprintf(stderr, "short hex file\n"); exit(1); }
    fclose(f);
    PL = malloc(4L * N * Q1);
    int *c = calloc(N, sizeof(int));
    for (int l = 0; l < N; l++) for (int t = 0; t < Q1; t++) { int p = LP[l * Q1 + t]; PL[p * Q1 + c[p]++] = l; }
    free(c);
}

static int *qq;                                 /* BFS queue, 2N entries */

/* BFS from point x (isline 0) or line x (isline 1) to depth 4: hd[v] is exact for distance <= 4, 255 otherwise.
   out4 receives the elements at distance 4 (points for a point source, lines for a line source); returns the count. */
static int bfs4(int x, int isline, uint8_t *hd, int *out4) {
    memset(hd, 255, 2 * (size_t)N);
    int h = 0, t = 0, s = isline ? N + x : x;
    hd[s] = 0; qq[t++] = s;
    while (h < t && hd[qq[h]] < 4) {            /* queue is in distance order: expand distance <= 3 only */
        int v = qq[h++], d = hd[v];
        if (v < N) {
            const int32_t *pl = PL + (size_t)v * Q1;
            for (int k = 0; k < Q1; k++) { int w = N + pl[k]; if (hd[w] == 255) { hd[w] = (uint8_t)(d + 1); qq[t++] = w; } }
        } else {
            const int32_t *lp = LP + (size_t)(v - N) * Q1;
            for (int k = 0; k < Q1; k++) { int w = lp[k]; if (hd[w] == 255) { hd[w] = (uint8_t)(d + 1); qq[t++] = w; } }
        }
    }
    int n4 = 0;
    for (int i = h; i < t; i++) { int v = qq[i]; out4[n4++] = v < N ? v : v - N; }   /* the rest is distance 4 */
    return n4;
}

/* full BFS, as in regions.c (used only for the from-scratch checks) */
static void hbfs_full(int x, int isline, uint8_t *hd) {
    memset(hd, 255, 2 * (size_t)N);
    int h = 0, t = 0, s = isline ? N + x : x;
    hd[s] = 0; qq[t++] = s;
    while (h < t) {
        int v = qq[h++];
        if (v < N) { for (int k = 0; k < Q1; k++) { int w = N + PL[v * Q1 + k]; if (hd[w] == 255) { hd[w] = (uint8_t)(hd[v] + 1); qq[t++] = w; } } }
        else { int l = v - N; for (int k = 0; k < Q1; k++) { int w = LP[l * Q1 + k]; if (hd[w] == 255) { hd[w] = (uint8_t)(hd[v] + 1); qq[t++] = w; } } }
    }
}

/* ---- signature count table: key = signature, cP = #points, cL = #lines; E = sum over keys of |cP - cL| ---- */
#define HBITS 17
#define HCAP (1u << HBITS)
#define HMASK (HCAP - 1)
typedef struct { uint32_t key; int16_t cP, cL; } hent;   /* key 0 = empty; counts are at most 14641 */
static hent *ht;
static int nkeys = 0, maxkeys = 0;
static int64_t E = 0;
static inline uint32_t hidx(uint32_t k) { return (k * 0x9E3779B1u) >> (32 - HBITS); }

static void ht_erase(uint32_t i) {              /* backward-shift deletion (linear probing) */
    uint32_t j = i;
    for (;;) {
        j = (j + 1) & HMASK;
        if (!ht[j].key) break;
        uint32_t k = hidx(ht[j].key);
        int stays = (i <= j) ? (i < k && k <= j) : (i < k || k <= j);
        if (!stays) { ht[i] = ht[j]; i = j; }
    }
    ht[i].key = 0; ht[i].cP = 0; ht[i].cL = 0; nkeys--;
}

static void adjust(sig_t k, int dP, int dL) {
    uint32_t i = hidx(k);
    while (ht[i].key && ht[i].key != k) i = (i + 1) & HMASK;
    if (!ht[i].key) {
        if (nkeys >= (int)(HCAP / 2)) { fprintf(stderr, "signature table too full\n"); exit(2); }
        ht[i].key = k; ht[i].cP = 0; ht[i].cL = 0; nkeys++;
        if (nkeys > maxkeys) maxkeys = nkeys;
    }
    int before = abs(ht[i].cP - ht[i].cL);
    ht[i].cP += dP; ht[i].cL += dL;
    E += abs(ht[i].cP - ht[i].cL) - before;
    if (!ht[i].cP && !ht[i].cL) ht_erase(i);
}

static sig_t *sigP, *sigL;                      /* per point / per line masks; the empty mask is never a key */
static inline void flipP(int u, sig_t bit) {
    sig_t o = sigP[u], n = o ^ bit;
    if (o) adjust(o, -1, 0);
    if (n) adjust(n, 1, 0);
    sigP[u] = n;
}
static inline void flipL(int x, sig_t bit) {
    sig_t o = sigL[x], n = o ^ bit;
    if (o) adjust(o, 0, -1);
    if (n) adjust(n, 0, 1);
    sigL[x] = n;
}

/* ---- flags and per-flag data ---- */
static int K;
static int *pv, *lv, *isFP, *isFL;              /* flags; isFP[p] = a+1 when p = p_a (0 if free) */
static uint8_t **dp, **dl, *tdp, *tdl;          /* per-flag distance arrays, two scratch arrays */
static int **P4, **L4, *n4P, *n4L, *tP4, *tL4;  /* distance-4 lists, scratch lists */
static int *logP, *logL, nlogP, nlogL;          /* elements flipped by the last evaluated move */
static int cpN, clN, cpc, clc, cn4P, cn4L;      /* the last evaluated move */

/* Evaluate "flag a -> (pN, lN)": new BFS data for the moved endpoint(s) go to the scratch arrays, bit a is flipped
   on the elements whose membership changes, and the change of E is returned. */
static int64_t evaluate(int a, int pN, int lN) {
    sig_t bit = (sig_t)1 << a;
    int64_t E0 = E;
    uint8_t *dpN = dp[a], *dlN = dl[a];
    int *P4N = P4[a], *L4N = L4[a];
    int n4PN = n4P[a], n4LN = n4L[a];
    cpc = pN != pv[a]; clc = lN != lv[a]; cpN = pN; clN = lN;
    if (cpc) { n4PN = bfs4(pN, 0, tdp, tP4); dpN = tdp; P4N = tP4; }
    if (clc) { n4LN = bfs4(lN, 1, tdl, tL4); dlN = tdl; L4N = tL4; }
    cn4P = n4PN; cn4L = n4LN;
    nlogP = nlogL = 0;
    for (int i = 0; i < n4P[a]; i++) {          /* points leaving S'(p_a) */
        int u = P4[a][i];
        if ((sigP[u] & bit) && !(dpN[u] == 4 && dlN[u] != 3)) { logP[nlogP++] = u; flipP(u, bit); }
    }
    for (int i = 0; i < n4PN; i++) {            /* points entering S'(p_a) */
        int u = P4N[i];
        if (dlN[u] != 3 && !(sigP[u] & bit)) { logP[nlogP++] = u; flipP(u, bit); }
    }
    for (int i = 0; i < n4L[a]; i++) {          /* lines leaving S(l_a) */
        int x = L4[a][i];
        if ((sigL[x] & bit) && !(dlN[N + x] == 4 && dpN[N + x] != 3)) { logL[nlogL++] = x; flipL(x, bit); }
    }
    for (int i = 0; i < n4LN; i++) {            /* lines entering S(l_a) */
        int x = L4N[i];
        if (dpN[N + x] != 3 && !(sigL[x] & bit)) { logL[nlogL++] = x; flipL(x, bit); }
    }
    return E - E0;
}

static void commit(int a) {                     /* keep the evaluated move */
    if (cpc) {
        uint8_t *t8 = dp[a]; dp[a] = tdp; tdp = t8;
        int *t4 = P4[a]; P4[a] = tP4; tP4 = t4; n4P[a] = cn4P;
        isFP[pv[a]] = 0; pv[a] = cpN; isFP[cpN] = a + 1;
    }
    if (clc) {
        uint8_t *t8 = dl[a]; dl[a] = tdl; tdl = t8;
        int *t4 = L4[a]; L4[a] = tL4; tL4 = t4; n4L[a] = cn4L;
        isFL[lv[a]] = 0; lv[a] = clN; isFL[clN] = a + 1;
    }
}

static void revert(int a) {                     /* undo the flips of the evaluated move */
    sig_t bit = (sig_t)1 << a;
    for (int i = 0; i < nlogP; i++) flipP(logP[i], bit);
    for (int i = 0; i < nlogL; i++) flipL(logL[i], bit);
}

static int propose(int a, int typ, int *pN, int *lN) {
    if (typ == 0) { int l = PL[pv[a] * Q1 + rndi(Q1)]; if (l == lv[a] || isFL[l]) return 0; *pN = pv[a]; *lN = l; return 1; }
    if (typ == 1) { int p = LP[lv[a] * Q1 + rndi(Q1)]; if (p == pv[a] || isFP[p]) return 0; *pN = p; *lN = lv[a]; return 1; }
    int p = rndi(N); if (isFP[p]) return 0;
    int l = PL[p * Q1 + rndi(Q1)]; if (isFL[l]) return 0;
    *pN = p; *lN = l; return 1;
}

/* ---- from-scratch evaluation ---- */
static int cmp_sig(const void *a, const void *b) { sig_t x = *(const sig_t *)a, y = *(const sig_t *)b; return x < y ? -1 : x > y; }
static int cmp_i64(const void *a, const void *b) { int64_t x = *(const int64_t *)a, y = *(const int64_t *)b; return x < y ? -1 : x > y; }

/* full = 1: exact BFS and the tests d=4, d=5 as written in the card; full = 0: the depth-4 arrays used by the search */
static void masks_from_flags(const int *fp, const int *fl, int Kc, int full, sig_t *sp, sig_t *sl) {
    uint8_t *d1 = malloc(2 * (size_t)N), *d2 = malloc(2 * (size_t)N);
    int *l4 = malloc(sizeof(int) * N);
    for (int a = 0; a < Kc; a++) {
        sig_t bit = (sig_t)1 << a;
        if (full) { hbfs_full(fp[a], 0, d1); hbfs_full(fl[a], 1, d2); }
        else { bfs4(fp[a], 0, d1, l4); bfs4(fl[a], 1, d2, l4); }
        for (int v = 0; v < N; v++) {
            int inP = full ? (d1[v] == 4 && d2[v] == 5) : (d1[v] == 4 && d2[v] != 3);
            int inL = full ? (d2[N + v] == 4 && d1[N + v] == 5) : (d2[N + v] == 4 && d1[N + v] != 3);
            if (inP) sp[v] |= bit;
            if (inL) sl[v] |= bit;
        }
    }
    free(d1); free(d2); free(l4);
}

/* regions.c merge: hP = sum over nonempty A of max(0, cP - cL), hL = sum over A of max(0, cL - cP) */
static void deficit_halves(const sig_t *sp0, const sig_t *sl0, long *hP, long *hL) {
    sig_t *sp = malloc(sizeof(sig_t) * N), *sl = malloc(sizeof(sig_t) * N);
    memcpy(sp, sp0, sizeof(sig_t) * N); memcpy(sl, sl0, sizeof(sig_t) * N);
    qsort(sp, N, sizeof(sig_t), cmp_sig); qsort(sl, N, sizeof(sig_t), cmp_sig);
    long dP = 0, dL = 0; int i = 0, j = 0;
    while (i < N || j < N) {
        sig_t s = (i < N && (j >= N || sp[i] <= sl[j])) ? sp[i] : sl[j];
        long ci = 0, cj = 0;
        while (i < N && sp[i] == s) { i++; ci++; }
        while (j < N && sl[j] == s) { j++; cj++; }
        if (s) { if (ci > cj) dP += ci - cj; if (cj > ci) dL += cj - ci; }
    }
    *hP = dP; *hL = dL;
    free(sp); free(sl);
}

static void flags_deficit(const int *fp, const int *fl, int Kc, int full, long *hP, long *hL) {
    sig_t *sp = calloc(N, sizeof(sig_t)), *sl = calloc(N, sizeof(sig_t));
    masks_from_flags(fp, fl, Kc, full, sp, sl);
    deficit_halves(sp, sl, hP, hL);
    free(sp); free(sl);
}

/* test mode: incremental masks and E must equal a fresh computation; returns nonzero on mismatch */
static int verify_state(void) {
    sig_t *sp = calloc(N, sizeof(sig_t)), *sl = calloc(N, sizeof(sig_t));
    masks_from_flags(pv, lv, K, 0, sp, sl);
    long bad = 0;
    for (int u = 0; u < N; u++) { if (sp[u] != sigP[u]) bad++; if (sl[u] != sigL[u]) bad++; }
    long hP, hL;
    deficit_halves(sp, sl, &hP, &hL);
    if (hP + hL != E) bad += 1000000;
    free(sp); free(sl);
    return bad != 0;
}

int main(int argc, char **argv) {
    if (argc < 6) { fprintf(stderr, "usage: place_anneal HEXBIN K SEED SECS OUT [CHECK]\n"); return 1; }
    load(argv[1]);
    K = atoi(argv[2]);
    uint64_t seed = strtoull(argv[3], NULL, 10);
    double secs = atof(argv[4]);
    const char *out = argv[5];
    long chk = argc > 6 ? atol(argv[6]) : 0;
    if (K < 1 || K > 32) { fprintf(stderr, "K must be 1..32\n"); return 1; }
    rs ^= seed * 0x9E3779B97F4A7C15ULL;
    for (int i = 0; i < 20; i++) rnd();

    qq = malloc(sizeof(int) * 2 * (size_t)N);
    pv = malloc(sizeof(int) * K); lv = malloc(sizeof(int) * K);
    isFP = calloc(N, sizeof(int)); isFL = calloc(N, sizeof(int));
    dp = malloc(sizeof(void *) * K); dl = malloc(sizeof(void *) * K);
    P4 = malloc(sizeof(void *) * K); L4 = malloc(sizeof(void *) * K);
    n4P = malloc(sizeof(int) * K); n4L = malloc(sizeof(int) * K);
    for (int a = 0; a < K; a++) {
        dp[a] = malloc(2 * (size_t)N); dl[a] = malloc(2 * (size_t)N);
        P4[a] = malloc(sizeof(int) * N); L4[a] = malloc(sizeof(int) * N);
    }
    tdp = malloc(2 * (size_t)N); tdl = malloc(2 * (size_t)N);
    tP4 = malloc(sizeof(int) * N); tL4 = malloc(sizeof(int) * N);
    logP = malloc(sizeof(int) * N); logL = malloc(sizeof(int) * N);
    sigP = calloc(N, sizeof(sig_t)); sigL = calloc(N, sizeof(sig_t));
    ht = calloc(HCAP, sizeof(hent));

    /* random start: p uniform, l uniform among the lines through p, all points distinct and all lines distinct */
    for (int a = 0; a < K; a++)
        for (;;) {
            int p = rndi(N), l = PL[p * Q1 + rndi(Q1)];
            if (!isFP[p] && !isFL[l]) { pv[a] = p; lv[a] = l; isFP[p] = a + 1; isFL[l] = a + 1; break; }
        }
    for (int a = 0; a < K; a++) {
        sig_t bit = (sig_t)1 << a;
        n4P[a] = bfs4(pv[a], 0, dp[a], P4[a]);
        n4L[a] = bfs4(lv[a], 1, dl[a], L4[a]);
        for (int i = 0; i < n4P[a]; i++) { int u = P4[a][i]; if (dl[a][u] != 3) sigP[u] |= bit; }
        for (int i = 0; i < n4L[a]; i++) { int x = L4[a][i]; if (dp[a][N + x] != 3) sigL[x] |= bit; }
    }
    for (int u = 0; u < N; u++) if (sigP[u]) adjust(sigP[u], 1, 0);
    for (int x = 0; x < N; x++) if (sigL[x]) adjust(sigL[x], 0, 1);
    int64_t E_init = E;
    long hP0, hL0;
    flags_deficit(pv, lv, K, 1, &hP0, &hL0);
    fprintf(stderr, "K=%d seed=%llu: D before annealing = %lld (scratch: points-half %ld + lines-half %ld = %ld)%s\n",
            K, (unsigned long long)seed, (long long)E_init, hP0, hL0, hP0 + hL0,
            (hP0 + hL0 == E_init) ? "" : "  MISMATCH");
    if (hP0 + hL0 != E_init) return 3;

    /* temperature scale: median of the uphill changes of random proposals at the start state */
    int64_t *vals = malloc(sizeof(int64_t) * 600); int nv = 0;
    for (int s = 0; s < 600; s++) {
        double r = rndu(); int typ = r < 0.475 ? 0 : (r < 0.95 ? 1 : 2);
        int a = rndi(K), pN, lN;
        if (!propose(a, typ, &pN, &lN)) continue;
        int64_t d = evaluate(a, pN, lN);
        revert(a);
        if (d > 0) vals[nv++] = d;
    }
    if (E != E_init) { fprintf(stderr, "revert mismatch\n"); return 3; }
    qsort(vals, nv, sizeof(int64_t), cmp_i64);
    double T0 = nv ? (double)vals[nv / 2] : 1.0, T1 = 0.5;
    if (T0 < T1) T0 = T1;
    fprintf(stderr, "uphill samples %d, median %.1f: T0 = %.2f, T1 = %.2f, run %.0f s\n", nv, T0, T0, T1, secs);

    /* annealing with geometric cooling in wall-clock time */
    int *bestP = malloc(sizeof(int) * K), *bestL = malloc(sizeof(int) * K);
    memcpy(bestP, pv, sizeof(int) * K); memcpy(bestL, lv, sizeof(int) * K);
    int64_t bestE = E;
    long it = 0, nvalid = 0, nacc = 0;
    double t0 = now(), tlast = t0, T = T0, el = 0;
    for (;;) {
        el = now() - t0;
        if (el >= secs) break;
        T = T0 * pow(T1 / T0, el / secs);
        it++;
        double r = rndu();
        int typ = r < 0.475 ? 0 : (r < 0.95 ? 1 : 2);
        int a = rndi(K), pN, lN;
        if (propose(a, typ, &pN, &lN)) {
            nvalid++;
            int64_t d = evaluate(a, pN, lN);
            if (d <= 0 || rndu() < exp(-(double)d / T)) {
                commit(a); nacc++;
                if (E < bestE) {
                    bestE = E;
                    memcpy(bestP, pv, sizeof(int) * K); memcpy(bestL, lv, sizeof(int) * K);
                }
            } else revert(a);
        }
        if (chk && it % chk == 0 && verify_state()) { fprintf(stderr, "VERIFY FAILED at iteration %ld\n", it); return 3; }
        if (now() - tlast >= 30) {
            tlast = now();
            fprintf(stderr, "t=%.0fs it=%ld valid=%ld acc=%.3f T=%.2f D=%lld best=%lld keys=%d\n",
                    el, it, nvalid, nvalid ? (double)nacc / nvalid : 0.0, T, (long long)E, (long long)bestE, nkeys);
        }
    }

    FILE *f = fopen(out, "w");
    if (!f) { fprintf(stderr, "cannot write %s\n", out); return 1; }
    for (int a = 0; a < K; a++) fprintf(f, "%d %d\n", bestP[a], bestL[a]);
    fclose(f);

    long vP, vL;
    flags_deficit(bestP, bestL, K, 1, &vP, &vL);
    printf("RESULT K=%d seed=%llu iterations=%ld valid=%ld accepted=%ld (%.2f ms per iteration) max signature keys=%d\n",
           K, (unsigned long long)seed, it, nvalid, nacc, it ? 1000.0 * el / it : 0.0, maxkeys);
    printf("D before=%lld  D best(incremental)=%lld  D best(scratch)=%ld+%ld=%ld%s\n",
           (long long)E_init, (long long)bestE, vP, vL, vP + vL, (vP + vL == bestE) ? "" : "  MISMATCH");
    printf("flags written to %s\n", out);
    return (vP + vL == bestE) ? 0 : 3;
}
