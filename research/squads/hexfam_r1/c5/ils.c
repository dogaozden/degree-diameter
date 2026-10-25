/* c5: ARW-style iterated local search for large partial ovoids of Q(6,q), q odd prime.
   Usage: ils HEXBIN SEEDFILE OUTDIR SECONDS RNGSEED [PLATEAU=20] [TABU=7] [PMAX=2]
   Conflict graph: x ~ y iff B(x,y) == 0 (orthogonal). A partial ovoid is an independent set.
   tight[x] = number of solution points orthogonal to x; sumid[x] = sum of their ids (so a 1-tight x
   has its unique solution neighbour = sumid[x]). Every add/remove is one full scan of the N points. */
#include "/home/user/degree-diameter/research/projects/hexagon-family/tools/q6.h"
#include <time.h>

static int N, Q;
static uint8_t *Cr;            /* N*7 coordinates (from hex_load) */
static uint8_t *Xc[7];         /* the same, one array per coordinate */
static uint32_t MAGIC;         /* Lemire divisibility constant for Q */
static int *tight;
static uint32_t *sumid;
static uint8_t *inS;
static int *Sl, *posS, nS;     /* solution list */
static int *lg_v; static uint8_t *lg_op; static int nlog, logcap;
static int logging = 1;
static int *Lbuf, *Fbuf, *nxt, *head;
static int64_t *tabu;
static int *bestS, nbest;
static uint64_t rs = 88172645463325252ull;
static long nplat = 0;

static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline int rndint(int n) { return (int)(rnd() % (uint64_t)n); }
static inline double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }

/* 1 iff a and b are opposite (B != 0) */
static inline int opp(int a, int b) {
    const uint8_t *x = Cr + 7 * (size_t)a, *y = Cr + 7 * (size_t)b;
    int s = x[0]*y[4] + x[4]*y[0] + x[1]*y[5] + x[5]*y[1] + x[2]*y[6] + x[6]*y[2] - 2*x[3]*y[3];
    return s % Q != 0;
}

/* delta = +1 (v added) or -1 (v removed): update tight/sumid of all points */
static void upd(int v, int delta) {
    const uint8_t *c = Cr + 7 * (size_t)v;
    /* B(x,v) = x0 v4 + x4 v0 + x1 v5 + x5 v1 + x2 v6 + x6 v2 - 2 x3 v3 */
    int w0 = c[4], w1 = c[5], w2 = c[6], w3 = (Q - (2 * c[3]) % Q) % Q, w4 = c[0], w5 = c[1], w6 = c[2];
    const uint8_t *restrict x0 = Xc[0], *restrict x1 = Xc[1], *restrict x2 = Xc[2], *restrict x3 = Xc[3],
                          *restrict x4 = Xc[4], *restrict x5 = Xc[5], *restrict x6 = Xc[6];
    int *restrict tg = tight; uint32_t *restrict sd = sumid;
    const uint32_t M = MAGIC;   /* s % Q == 0  <=>  s * M <= M - 1  for 0 <= s < 2^32 (Lemire) */
    const uint32_t uv = (uint32_t)v;
#pragma GCC ivdep
    for (int x = 0; x < N; x++) {
        uint32_t s = (uint32_t)(x0[x]*w0 + x1[x]*w1 + x2[x]*w2 + x3[x]*w3 + x4[x]*w4 + x5[x]*w5 + x6[x]*w6);
        uint32_t z = (s * M <= M - 1) ? 1u : 0u;
        tg[x] += delta * (int)z;
        sd[x] += (uint32_t)(delta * (int)z) * uv;
    }
    /* v is orthogonal to itself (it lies on Q): remove its own contribution */
    tight[v] -= delta;
    sumid[v] -= (uint32_t)delta * (uint32_t)v;
}

static void logpush(uint8_t op, int v) {
    if (nlog == logcap) {
        logcap = logcap ? 2 * logcap : 4096;
        lg_v = realloc(lg_v, sizeof(int) * logcap); lg_op = realloc(lg_op, logcap);
    }
    lg_v[nlog] = v; lg_op[nlog] = op; nlog++;
}
static void add_v(int v) {
    inS[v] = 1; posS[v] = nS; Sl[nS++] = v; upd(v, +1);
    if (logging) logpush(1, v);
}
static void rem_v(int v) {
    inS[v] = 0; int p = posS[v]; int last = Sl[--nS]; Sl[p] = last; posS[last] = p; upd(v, -1);
    if (logging) logpush(0, v);
}
static void undo(void) {
    logging = 0;
    for (int i = nlog - 1; i >= 0; i--) { if (lg_op[i]) rem_v(lg_v[i]); else add_v(lg_v[i]); }
    logging = 1; nlog = 0;
}
static void shuffle(int *a, int n) { for (int i = n - 1; i > 0; i--) { int j = rndint(i + 1); int t = a[i]; a[i] = a[j]; a[j] = t; } }

/* insert all free points (tight 0, not in S) in random order */
static int fill_free(void) {
    int nf = 0;
    for (int x = 0; x < N; x++) if (!inS[x] && tight[x] == 0) Fbuf[nf++] = x;
    shuffle(Fbuf, nf);
    int added = 0;
    for (int i = 0; i < nf; i++) { int x = Fbuf[i]; if (!inS[x] && tight[x] == 0) { add_v(x); added++; } }
    return added;
}
/* collect all 1-tight points into Lbuf */
static int collect1(void) {
    int n = 0;
    for (int x = 0; x < N; x++) if (!inS[x] && tight[x] == 1) Lbuf[n++] = x;
    return n;
}
/* (1,2)-swap: a solution point r whose 1-tight neighbours contain two opposite points a, b */
static int try12(int n1) {
    for (int i = 0; i < n1; i++) { int x = Lbuf[i]; int r = (int)sumid[x]; nxt[x] = head[r]; head[r] = x; }
    int fr = -1, fa = -1, fb = -1;
    int off = nS ? rndint(nS) : 0;
    for (int k = 0; k < nS && fr < 0; k++) {
        int r = Sl[(k + off) % nS];
        for (int a = head[r]; a != -1 && fr < 0; a = nxt[a])
            for (int b = nxt[a]; b != -1; b = nxt[b])
                if (opp(a, b)) { fr = r; fa = a; fb = b; break; }
    }
    for (int i = 0; i < n1; i++) head[(int)sumid[Lbuf[i]]] = -1;
    if (fr >= 0) { rem_v(fr); add_v(fa); add_v(fb); return 1; }
    return 0;
}
/* (1,1)-swap to a random non-tabu 1-tight point */
static int plateau_move(int n1, int64_t step, int tt) {
    for (int t = 0; t < 30; t++) {
        int x = Lbuf[rndint(n1)];
        if (tabu[x] > step) continue;
        int r = (int)sumid[x];
        rem_v(r); tabu[r] = step + tt; add_v(x);
        nplat++;
        return 1;
    }
    return 0;
}
static void local_search(int P, int64_t step, int tt) {
    int plateau = P;
    for (;;) {
        fill_free();
        int n1 = collect1();
        if (n1 >= 2 && try12(n1)) continue;
        if (plateau > 0 && n1 > 0 && plateau_move(n1, step, tt)) { plateau--; continue; }
        break;
    }
}
static void save_set(const char *path, const int *ids, int n) {
    int *c = malloc(sizeof(int) * (n > 0 ? n : 1)); memcpy(c, ids, sizeof(int) * n);
    int cmp(const void *a, const void *b) { return (*(const int *)a > *(const int *)b) - (*(const int *)a < *(const int *)b); }
    qsort(c, n, sizeof(int), cmp);
    FILE *f = fopen(path, "w"); if (!f) { fprintf(stderr, "cannot write %s\n", path); exit(1); }
    for (int i = 0; i < n; i++) fprintf(f, "%d\n", c[i]);
    fclose(f); free(c);
}
static int check_indep(const int *ids, int n) {
    for (int i = 0; i < n; i++) for (int j = i + 1; j < n; j++) if (!opp(ids[i], ids[j])) return 0;
    return 1;
}
static void rebuild(const int *ids, int n) {
    memset(tight, 0, sizeof(int) * N); memset(sumid, 0, sizeof(uint32_t) * N); memset(inS, 0, N);
    nS = 0; logging = 0;
    for (int i = 0; i < n; i++) add_v(ids[i]);
    logging = 1; nlog = 0;
}
static void hist(const char *tag) {
    int mn = 1 << 30, mx = 0; long n1 = 0, n2 = 0, n3 = 0, nmin = 0;
    for (int x = 0; x < N; x++) if (!inS[x]) { int t = tight[x]; if (t < mn) mn = t; if (t > mx) mx = t;
        n1 += t == 1; n2 += t == 2; n3 += t == 3; }
    for (int x = 0; x < N; x++) if (!inS[x] && tight[x] == mn) nmin++;
    printf("%s |S|=%d nonsolution: min tight=%d (count %ld) max tight=%d; 1-tight=%ld 2-tight=%ld 3-tight=%ld\n",
           tag, nS, mn, nmin, mx, n1, n2, n3);
    fflush(stdout);
}

int main(int argc, char **argv) {
    if (argc < 6) { fprintf(stderr, "usage: ils HEXBIN SEEDFILE OUTDIR SECONDS RNGSEED [PLATEAU] [TABU] [PMAX]\n"); return 1; }
    Hex h = hex_load(argv[1]);
    Q = h.q; N = h.N; Cr = h.C;
    if (Q % 2 == 0) { fprintf(stderr, "q must be odd\n"); return 1; }
    for (int i = 0; i < 7; i++) { Xc[i] = malloc(N); for (int x = 0; x < N; x++) Xc[i][x] = Cr[7 * (size_t)x + i]; }
    MAGIC = 0xFFFFFFFFu / (uint32_t)Q + 1;
    for (int s = 0; s <= 7 * (Q - 1) * (Q - 1); s++) if (((s * MAGIC) <= MAGIC - 1) != (s % Q == 0)) { fprintf(stderr, "magic fails\n"); return 1; }
    tight = calloc(N, sizeof(int)); sumid = calloc(N, sizeof(uint32_t)); inS = calloc(N, 1);
    Sl = malloc(sizeof(int) * N); posS = malloc(sizeof(int) * N);
    Lbuf = malloc(sizeof(int) * N); Fbuf = malloc(sizeof(int) * N);
    nxt = malloc(sizeof(int) * N); head = malloc(sizeof(int) * N); memset(head, 0xff, sizeof(int) * N);
    tabu = calloc(N, sizeof(int64_t)); bestS = malloc(sizeof(int) * N);
    double secs = atof(argv[4]);
    rs = (strtoull(argv[5], NULL, 10) + 1) * 0x9E3779B97F4A7C15ull;
    int P = argc > 6 ? atoi(argv[6]) : 20;
    int TT = argc > 7 ? atoi(argv[7]) : 7;
    int PMAX = argc > 8 ? atoi(argv[8]) : 0;   /* slack above the minimum tightness for the perturbation */
    const char *outdir = argv[3];

    for (int v = 0; v < N; v++) if (opp(v, v)) { fprintf(stderr, "point %d not singular\n", v); return 1; }

    int *seed; int ns = read_ids(argv[2], &seed);
    if (!check_indep(seed, ns)) { fprintf(stderr, "seed is not a partial ovoid\n"); return 1; }
    rebuild(seed, ns);
    printf("q=%d N=%d seed=%d (%s) P=%d TT=%d PMAX=%d secs=%.0f\n", Q, N, ns, argv[2], P, TT, PMAX, secs);
    hist("seed");
    /* self-check of the incremental counts */
    for (int x = 0; x < N; x++) if (!inS[x]) {
        int c = 0; for (int k = 0; k < nS; k++) if (!opp(Sl[k], x)) c++;
        if (c != tight[x]) { fprintf(stderr, "tight mismatch at %d: %d vs %d\n", x, c, tight[x]); return 1; }
    }
    printf("self-check ok\n"); fflush(stdout);

    nbest = nS; memcpy(bestS, Sl, sizeof(int) * nS);
    char path[1024];
    snprintf(path, sizeof path, "%s/best_q%d_%d.txt", outdir, Q, nbest); save_set(path, bestS, nbest);

    double t0 = now(), tlast = t0;
    long iters = 0, nrebuild = 0, nundo = 0, nacc_worse = 0;
    int64_t step = 1;
    const int RD = 3;
    while (now() - t0 < secs) {
        iters++; step++;
        nlog = 0; logging = 1;
        int before = nS;
        /* min-conflict perturbation: v uniform among non-tabu outside points with tight <= min + PMAX */
        int mn = 1 << 30;
        for (int x = 0; x < N; x++) if (!inS[x] && tabu[x] <= step && tight[x] < mn) mn = tight[x];
        int nc = 0;
        for (int x = 0; x < N; x++) if (!inS[x] && tabu[x] <= step && tight[x] <= mn + PMAX) Fbuf[nc++] = x;
        int v = Fbuf[rndint(nc)];
        for (int k = nS - 1; k >= 0; k--) { int r = Sl[k]; if (!opp(r, v)) { rem_v(r); tabu[r] = step + TT; } }
        add_v(v);
        local_search(P, step, TT);
        if (nS > nbest) {
            nbest = nS; memcpy(bestS, Sl, sizeof(int) * nS);
            if (!check_indep(bestS, nbest)) { fprintf(stderr, "BUG: not independent\n"); return 1; }
            snprintf(path, sizeof path, "%s/best_q%d_%d.txt", outdir, Q, nbest); save_set(path, bestS, nbest);
            printf("improved to %d at t=%.1fs iter=%ld\n", nbest, now() - t0, iters); fflush(stdout);
        }
        if (nS < before) {
            double p = 1.0 / (1.0 + (double)(before - nS) * (double)(nbest - nS));
            if (rnd01() >= p) { undo(); nundo++; }
            else nacc_worse++;
        }
        if (nS < nbest - RD) { rebuild(bestS, nbest); nrebuild++; }
        if (now() - tlast > 10.0) {
            tlast = now();
            printf("t=%.0fs iter=%ld cur=%d best=%d plateau=%ld undo=%ld rebuild=%ld rate=%.1f/s\n",
                   tlast - t0, iters, nS, nbest, nplat, nundo, nrebuild, iters / (tlast - t0));
            fflush(stdout);
        }
    }
    if (!check_indep(bestS, nbest)) { fprintf(stderr, "BUG: final not independent\n"); return 1; }
    printf("FINAL q=%d best=%d iters=%ld time=%.1f\n", Q, nbest, iters, now() - t0);
    snprintf(path, sizeof path, "%s/best_q%d_%d.txt", outdir, Q, nbest); save_set(path, bestS, nbest);
    printf("saved %s\n", path);
    return 0;
}
