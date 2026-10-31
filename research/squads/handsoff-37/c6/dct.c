/* c6: simulated annealing over M = symmetric 0/1 matrix, m x m, row sums 3 (loops count once).
   Double cover C(M): A_i ~ B_j iff M_ij = 1, n = 2m. Cost = #unordered pairs {i,j}, i != j, with no even walk
   of length <= 6 in M (far of the cover = 2 * cost). Cover diameter <= 7 iff cost = 0.
   Usage: dc m seed seconds T0 T1 iters_per_restart outprefix [initfile]
   initfile: a cover edge list (n, then pairs) of the form written by this program; M is read back from it.
   Writes outprefix_best.edges (cover, n = 2m) whenever the global best improves; prints progress on stdout. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <time.h>

#define MAXM 128
static int m;
static uint64_t adj[MAXM][2];           /* bit j of row i set iff M_ij = 1 (diagonal = loop) */
static int nedge, EA[MAXM * 2], EB[MAXM * 2], eidx[MAXM][MAXM];
static int nloop, LP[MAXM], lpos[MAXM];

static uint64_t rs = 88172645463325252ULL;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline int rndi(int n) { return (int)(rnd() % (uint64_t)n); }
static inline double rndu(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }
static inline int getadj(int i, int j) { return (adj[i][j >> 6] >> (j & 63)) & 1; }
static inline int hasloop(int i) { return getadj(i, i); }

/* ---- primitive operations with an undo log ---- */
enum { OP_AE, OP_RE, OP_AL, OP_RL };
static int logn, logt[64], loga[64], logbb[64];
static void raw_op(int t, int a, int b) {
    switch (t) {
    case OP_AE:
        adj[a][b >> 6] |= 1ULL << (b & 63); adj[b][a >> 6] |= 1ULL << (a & 63);
        EA[nedge] = a; EB[nedge] = b; eidx[a][b] = eidx[b][a] = nedge; nedge++; break;
    case OP_RE: {
        int k = eidx[a][b], last = nedge - 1;
        adj[a][b >> 6] &= ~(1ULL << (b & 63)); adj[b][a >> 6] &= ~(1ULL << (a & 63));
        if (k != last) { EA[k] = EA[last]; EB[k] = EB[last]; eidx[EA[k]][EB[k]] = eidx[EB[k]][EA[k]] = k; }
        nedge--; break; }
    case OP_AL:
        adj[a][a >> 6] |= 1ULL << (a & 63); LP[nloop] = a; lpos[a] = nloop; nloop++; break;
    case OP_RL: {
        int k = lpos[a], last = nloop - 1;
        adj[a][a >> 6] &= ~(1ULL << (a & 63));
        if (k != last) { LP[k] = LP[last]; lpos[LP[k]] = k; }
        nloop--; break; }
    }
}
static void do_op(int t, int a, int b) {
    logt[logn] = t; loga[logn] = a; logbb[logn] = b; logn++;
    raw_op(t, a, b);
}
static void undo_all(void) {
    while (logn > 0) {
        logn--;
        int t = logt[logn];
        int inv = (t == OP_AE) ? OP_RE : (t == OP_RE) ? OP_AE : (t == OP_AL) ? OP_RL : OP_AL;
        raw_op(inv, loga[logn], logbb[logn]);
    }
}

/* ---- moves: each returns 1 if it applied ops ---- */
static int move_E(void) { /* 2-switch on two non-loop edges: ab, cd -> ac, bd */
    if (nedge < 2) return 0;
    int k1 = rndi(nedge), k2 = rndi(nedge);
    if (k1 == k2) return 0;
    int a = EA[k1], b = EB[k1], c = EA[k2], d = EB[k2];
    if (rnd() & 1) { int t = c; c = d; d = t; }
    if (a == c || b == d || getadj(a, c) || getadj(b, d)) return 0;
    do_op(OP_RE, a, b); do_op(OP_RE, c, d);
    do_op(OP_AE, a, c); do_op(OP_AE, b, d);
    return 1;
}
static int move_L2E(void) { /* loops at u, v -> edge uv */
    if (nloop < 2) return 0;
    int u = LP[rndi(nloop)], v = LP[rndi(nloop)];
    if (u == v || getadj(u, v)) return 0;
    do_op(OP_RL, u, u); do_op(OP_RL, v, v); do_op(OP_AE, u, v);
    return 1;
}
static int move_E2L(void) { /* edge ab -> loops at a and b */
    if (nedge < 1) return 0;
    int k = rndi(nedge), a = EA[k], b = EB[k];
    if (hasloop(a) || hasloop(b)) return 0;
    do_op(OP_RE, a, b); do_op(OP_AL, a, a); do_op(OP_AL, b, b);
    return 1;
}
static int move_LS(void) { /* loop at a, edge cd -> edge ac, loop at d */
    if (nloop < 1 || nedge < 1) return 0;
    int a = LP[rndi(nloop)], k = rndi(nedge), c = EA[k], d = EB[k];
    if (rnd() & 1) { int t = c; c = d; d = t; }
    if (c == a || d == a || getadj(a, c) || hasloop(d)) return 0;
    do_op(OP_RL, a, a); do_op(OP_RE, c, d); do_op(OP_AE, a, c); do_op(OP_AL, d, d);
    return 1;
}

/* ---- cost: unordered pairs {i,j} with no even walk of length <= 6 ---- */
static uint64_t Bw[MAXM][2], H2[MAXM][2], COV[MAXM][2];
static int defic[MAXM];
static int cost_full(void) {
    int j, i, w;
    for (j = 0; j < m; j++) {
        uint64_t r0 = 0, r1 = 0;
        for (w = 0; w < 2; w++) {
            uint64_t x = adj[j][w];
            while (x) { int t = __builtin_ctzll(x); x &= x - 1; int k = w * 64 + t; r0 |= adj[k][0]; r1 |= adj[k][1]; }
        }
        Bw[j][0] = r0; Bw[j][1] = r1;
    }
    for (j = 0; j < m; j++) {
        uint64_t r0 = 0, r1 = 0;
        for (w = 0; w < 2; w++) {
            uint64_t x = Bw[j][w];
            while (x) { int t = __builtin_ctzll(x); x &= x - 1; int k = w * 64 + t; r0 |= Bw[k][0]; r1 |= Bw[k][1]; }
        }
        H2[j][0] = r0; H2[j][1] = r1;
    }
    long total = 0;
    for (i = 0; i < m; i++) {
        uint64_t r0 = 0, r1 = 0;
        for (w = 0; w < 2; w++) {
            uint64_t x = Bw[i][w];
            while (x) { int t = __builtin_ctzll(x); x &= x - 1; int k = w * 64 + t; r0 |= H2[k][0]; r1 |= H2[k][1]; }
        }
        COV[i][0] = r0; COV[i][1] = r1;
        int cov = __builtin_popcountll(r0) + __builtin_popcountll(r1);
        defic[i] = m - cov;
        total += m - cov;
    }
    return (int)(total / 2);
}

static void clear_all(void) { memset(adj, 0, sizeof adj); nedge = 0; nloop = 0; logn = 0; }

/* random M with the right loop parity: random configuration model with restarts */
static void random_init(void) {
    int L = (m & 1) ? 1 : 0;
    for (;;) {
        clear_all();
        int ok = 1;
        int stubs[3 * MAXM], ns = 0;
        for (int i = 0; i < L; i++) raw_op(OP_AL, i, i);
        for (int i = 0; i < m; i++) { int need = 3 - (i < L ? 1 : 0); for (int t = 0; t < need; t++) stubs[ns++] = i; }
        int tries = 0;
        while (ns > 0 && tries < 100000) {
            tries++;
            int p = rndi(ns), q = rndi(ns);
            if (p == q) continue;
            int a = stubs[p], b = stubs[q];
            if (a == b || getadj(a, b)) continue;
            raw_op(OP_AE, a, b);
            /* remove the two stubs (higher index first) */
            int hi = p > q ? p : q, lo = p > q ? q : p;
            stubs[hi] = stubs[ns - 1]; ns--;
            stubs[lo] = stubs[ns - 1]; ns--;
        }
        if (ns == 0) break;
        ok = 0; (void)ok;
    }
    logn = 0;
}

static void load_init(const char *fn) {
    FILE *f = fopen(fn, "r");
    if (!f) { perror(fn); exit(2); }
    long n; if (fscanf(f, "%ld", &n) != 1) exit(2);
    clear_all();
    int a, b; int cnt = 0;
    /* cover edge list: (i, m+j) with M_ij = 1; M_ij = 1 for each such pair (each M edge appears twice unless loop) */
    static int seen[MAXM][MAXM];
    memset(seen, 0, sizeof seen);
    while (fscanf(f, "%d %d", &a, &b) == 2) {
        int i = a, j = b - m; if (i >= m) { int t = i; i = b; j = a - m; (void)t; }
        if (i < 0 || j < 0 || i >= m || j >= m) continue;
        if (!seen[i][j]) { seen[i][j] = seen[j][i] = 1; cnt++; }
    }
    fclose(f);
    for (int i = 0; i < m; i++) for (int j = i; j < m; j++) if (seen[i][j]) {
        if (i == j) raw_op(OP_AL, i, i); else raw_op(OP_AE, i, j);
    }
    logn = 0;
    (void)cnt;
}

static void write_cover(const char *fn) {
    FILE *f = fopen(fn, "w");
    if (!f) { perror(fn); return; }
    fprintf(f, "%d\n", 2 * m);
    for (int i = 0; i < m; i++) for (int j = 0; j < m; j++) if (getadj(i, j)) fprintf(f, "%d %d\n", i, m + j);
    fclose(f);
}


static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }

/* tabu search: focused candidate moves around a random uncovered pair */
static long tabu_until[MAXM][MAXM];

static int rand_near(int x) { /* random vertex within M-distance <= 2 of x (random walk, lazy) */
    int steps = rndi(3);
    for (int s = 0; s < steps; s++) {
        int deg = 0, nb[3];
        for (int w = 0; w < 2; w++) { uint64_t y = adj[x][w]; while (y) { int t = __builtin_ctzll(y); y &= y - 1; nb[deg++] = w * 64 + t; } }
        if (deg == 0) break;
        x = nb[rndi(deg)];
    }
    return x;
}
static int pick_bad(int *pi, int *pj) {
    int tot = 0; for (int i = 0; i < m; i++) if (defic[i] > 0) tot++;
    if (tot == 0) return 0;
    int r = rndi(tot), i = 0;
    for (i = 0; i < m; i++) if (defic[i] > 0) { if (r == 0) break; r--; }
    /* uncovered j != i */
    int cand[MAXM], nc = 0;
    for (int j = 0; j < m; j++) if (j != i && !((COV[i][j >> 6] >> (j & 63)) & 1)) cand[nc++] = j;
    if (nc == 0) return 0;
    *pi = i; *pj = cand[rndi(nc)];
    return 1;
}
/* generate one focused move for bad pair (i,j); apply it, return 1 if applied (ops in log) */
static int gen_focus(int i, int j) {
    double r = rndu();
    int a, b, c, d;
    if (r < 0.85) {
        if (nedge < 2) return 0;
        /* pick a non-loop edge near i and one near j */
        int x = rand_near(i), y = rand_near(j);
        if (adj[x][0] == 0 && adj[x][1] == 0) return 0;
        /* choose a random non-loop neighbour of x as edge endpoint */
        int nb[3], deg = 0;
        for (int w = 0; w < 2; w++) { uint64_t z = adj[x][w]; while (z) { int t = __builtin_ctzll(z); z &= z - 1; int k = w * 64 + t; if (k != x) nb[deg++] = k; } }
        if (deg == 0) return 0;
        a = x; b = nb[rndi(deg)];
        deg = 0;
        for (int w = 0; w < 2; w++) { uint64_t z = adj[y][w]; while (z) { int t = __builtin_ctzll(z); z &= z - 1; int k = w * 64 + t; if (k != y) nb[deg++] = k; } }
        if (deg == 0) return 0;
        c = y; d = nb[rndi(deg)];
        if (rnd() & 1) { int t = c; c = d; d = t; }
        if (a == c || b == d || a == d || b == c || getadj(a, c) || getadj(b, d)) return 0;
        do_op(OP_RE, a, b); do_op(OP_RE, c, d); do_op(OP_AE, a, c); do_op(OP_AE, b, d);
        return 1;
    } else if (r < 0.92) {
        /* loop slide: loop near i moved to a vertex near j */
        if (nloop < 1) return 0;
        return move_LS();
    } else {
        return move_E2L();
    }
}
static void apply_ops_log(int n, int *t, int *aa, int *bb) { for (int k = 0; k < n; k++) do_op(t[k], aa[k], bb[k]); }


static uint64_t snapA[MAXM][2];
static void snap_save(void) { memcpy(snapA, adj, sizeof adj); }
static void snap_restore(void) {
    clear_all();
    for (int i = 0; i < m; i++) for (int j = i; j < m; j++) if ((snapA[i][j >> 6] >> (j & 63)) & 1) {
        if (i == j) raw_op(OP_AL, i, i); else raw_op(OP_AE, i, j);
    }
}

int main(int argc, char **argv) {
    if (argc < 8) { fprintf(stderr, "usage: dct m seed seconds K tenure stall outprefix [initfile]\n"); return 2; }
    m = atoi(argv[1]);
    rs ^= (uint64_t)atoll(argv[2]) * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 10; i++) rnd();
    double tlim = atof(argv[3]);
    int K = atoi(argv[4]), tenure = atoi(argv[5]); long stall_lim = atol(argv[6]);
    const char *outp = argv[7];
    double t0 = now();
    if (argc > 8) load_init(argv[8]); else random_init();
    int cur = cost_full();
    int best = cur, gbest = cur;
    char fn[512];
    snap_save();
    printf("m=%d n=%d init cost=%d K=%d tenure=%d stall=%ld\n", m, 2 * m, cur, K, tenure, stall_lim); fflush(stdout);
    long it = 0, last_imp = 0; int restarts = 0;
    while (now() - t0 < tlim) {
        it++;
        int i, j;
        if (!pick_bad(&i, &j)) { printf("ZERO COST m=%d\n", m); break; }
        /* generate K candidates, evaluate each, keep best admissible */
        int bc = 1 << 30, bn = -1; int bt[8], ba[8], bb[8], blen = 0;
        for (int k = 0; k < K; k++) {
            logn = 0;
            if (!gen_focus(i, j)) { undo_all(); continue; }
            int nc = cost_full();
            /* tabu check: any added item that is tabu and not aspirating */
            int tabu = 0;
            for (int q = 0; q < logn; q++) {
                if ((logt[q] == OP_AE || logt[q] == OP_AL) && tabu_until[loga[q]][logbb[q]] > it) tabu = 1;
            }
            if (tabu && nc >= gbest) { undo_all(); continue; }
            if (nc < bc || (nc == bc && (rnd() & 1))) {
                bc = nc; blen = logn;
                for (int q = 0; q < logn; q++) { bt[q] = logt[q]; ba[q] = loga[q]; bb[q] = logbb[q]; }
                bn = k;
            }
            undo_all();
        }
        if (bn < 0) { continue; }
        /* replay best */
        for (int q = 0; q < blen; q++) {
            if (bt[q] == OP_RE) tabu_until[ba[q]][bb[q]] = tabu_until[bb[q]][ba[q]] = it + tenure + rndi(tenure + 1);
            if (bt[q] == OP_RL) tabu_until[ba[q]][ba[q]] = it + tenure;
            do_op(bt[q], ba[q], bb[q]);
        }
        logn = 0;
        cur = cost_full();
        if (cur < best) { best = cur; last_imp = it; }
        if (cur < gbest) {
            gbest = cur; snap_save();
            snprintf(fn, sizeof fn, "%s_best.edges", outp); write_cover(fn);
            printf("  new best cost=%d far=%d loops=%d it=%ld t=%.1f\n", gbest, 2 * gbest, nloop, it, now() - t0); fflush(stdout);
            if (gbest == 0) { printf("ZERO COST m=%d\n", m); break; }
        }
        if (it - last_imp > stall_lim) { /* perturb: random focused moves */
            restarts++;
            snap_restore(); logn = 0;
            for (int p = 0; p < 4; p++) { int ok = 0; for (int tries = 0; tries < 20 && !ok; tries++) ok = move_E(); }
            logn = 0;
            cur = cost_full(); best = cur; last_imp = it;
            if (restarts % 20 == 0) { printf("  perturb %d cur=%d gbest=%d it=%ld t=%.0f\n", restarts, cur, gbest, it, now() - t0); fflush(stdout); }
        }
    }
    printf("FINAL m=%d best cost=%d far=%d it=%ld t=%.0f\n", m, gbest, 2 * gbest, it, now() - t0);
    return 0;
}
