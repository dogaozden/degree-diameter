/* arw.c: ARW iterated local search (Andrade-Resende-Werneck 2012) for a maximum independent set of the
   collinearity graph of H(9) = a set of points with no two on a common line (the q=9 "ncol" problem).
   Adjacency: explicit, 90 neighbours per point, sorted rows.
   Local search: (1,2)-swaps using 1-tight vertices (tight = number of solution neighbours; sumS = sum of ids of
   solution neighbours, so the unique solution neighbour of a 1-tight vertex is sumS).
   Perturbation: force 1 random non-solution vertex in (occasionally more), chosen as the oldest of 4 samples.
   Acceptance: worse solutions kept with prob 1/(1+d*d*) (d = cur-new, d* = best-new), else undo via a log.
   usage: arw HEXBIN OUTFILE SEEDFILE|- SECONDS RNG [RESTART_ITERS] */
#include "/home/user/degree-diameter/research/projects/hexagon-family/tools/q6.h"
#include <time.h>
#include <limits.h>

#define D 90
static int NV, Q1;
static int32_t *adj, *tight, *sumS, *sol, *pos, *freest, *queue, *lastmv, *bestsol, *logv;
static int8_t *logt;
static uint8_t *inS, *inq, *infree;
static int solsz, freesz, qh, qt, qsz, bestsz;
static long long iter = 0, last_imp = 0, RESTART = 1000000;
static int logging = 0;
static long loglen = 0, logcap = 0;
static uint64_t rs = 88172645463325252ULL;
static double t0;
static char *outfile; static double PK = -1;

static inline uint64_t rnd64(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline double rndu(void) { return (rnd64() >> 11) * (1.0 / 9007199254740992.0); }
static inline int rndi(int n) { return (int)(rnd64() % (uint64_t)n); }
static double now(void) { struct timespec ts; clock_gettime(CLOCK_MONOTONIC, &ts); return ts.tv_sec + 1e-9 * ts.tv_nsec; }

static void logop(int v, int8_t t) {
    if (loglen == logcap) {
        logcap = logcap ? 2 * logcap : (1 << 16);
        logv = realloc(logv, sizeof(int32_t) * logcap); logt = realloc(logt, logcap);
    }
    logv[loglen] = v; logt[loglen] = t; loglen++;
}
static inline void push_q(int x) { if (!inq[x]) { inq[x] = 1; queue[qt] = x; qt = (qt + 1) % NV; qsz++; } }
static inline void push_f(int u) { if (!infree[u]) { infree[u] = 1; freest[freesz++] = u; } }

static void add_v(int v) {
    inS[v] = 1; pos[v] = solsz; sol[solsz++] = v; lastmv[v] = iter;
    const int32_t *a = adj + (size_t)v * D;
    for (int k = 0; k < D; k++) { int u = a[k]; tight[u]++; sumS[u] += v; }
    push_q(v);
    if (logging) logop(v, 1);
}
static void remove_v(int v) {
    inS[v] = 0; int p = pos[v]; int last = sol[--solsz]; sol[p] = last; pos[last] = p; lastmv[v] = iter;
    const int32_t *a = adj + (size_t)v * D;
    for (int k = 0; k < D; k++) {
        int u = a[k]; tight[u]--; sumS[u] -= v;
        if (!inS[u]) {
            if (tight[u] == 0) push_f(u);
            else if (tight[u] == 1) push_q(sumS[u]);
        }
    }
    if (logging) logop(v, -1);
}
static void process_free(void) {
    while (freesz) {
        int u = freest[--freesz]; infree[u] = 0;
        if (!inS[u] && tight[u] == 0) add_v(u);
    }
}
static int isadj(int a, int b) {
    const int32_t *x = adj + (size_t)a * D; int lo = 0, hi = D - 1;
    while (lo <= hi) { int m = (lo + hi) >> 1; if (x[m] == b) return 1; if (x[m] < b) lo = m + 1; else hi = m - 1; }
    return 0;
}
static int32_t Lbuf[D];
static void local_search(void) {
    process_free();
    while (qsz) {
        int x = queue[qh]; qh = (qh + 1) % NV; qsz--; inq[x] = 0;
        if (!inS[x]) continue;
        int nl = 0; const int32_t *a = adj + (size_t)x * D;
        for (int k = 0; k < D; k++) { int u = a[k]; if (!inS[u] && tight[u] == 1) Lbuf[nl++] = u; }
        if (nl < 2) continue;
        for (int i = nl - 1; i > 0; i--) { int j = rndi(i + 1); int32_t t = Lbuf[i]; Lbuf[i] = Lbuf[j]; Lbuf[j] = t; }
        int fu = -1, fw = -1;
        for (int i = 0; i < nl && fu < 0; i++)
            for (int j = i + 1; j < nl; j++)
                if (!isadj(Lbuf[i], Lbuf[j])) { fu = Lbuf[i]; fw = Lbuf[j]; break; }
        if (fu < 0) continue;
        remove_v(x); add_v(fu); add_v(fw); process_free();
    }
}
static int pick_out(void) {
    int best = -1; long long bt = LLONG_MAX;
    for (int c = 0; c < 4; c++) {
        int v; do { v = rndi(NV); } while (inS[v]);
        if (lastmv[v] < bt) { bt = lastmv[v]; best = v; }
    }
    return best;
}
static void perturb(void) {
    int k = 1;
    double pk = PK > 0 ? PK : 1.0 / (2.0 * solsz);
    if (rndu() < pk) { k = 2; while (rndu() < 0.5 && k < 20) k++; }
    for (int t = 0; t < k; t++) {
        int v = pick_out();
        const int32_t *a = adj + (size_t)v * D;
        for (int j = 0; j < D; j++) { int u = a[j]; if (inS[u]) remove_v(u); }
        add_v(v);
    }
    local_search();
}
static void drain(void) {
    while (qsz) { int x = queue[qh]; qh = (qh + 1) % NV; qsz--; inq[x] = 0; }
    while (freesz) { int u = freest[--freesz]; infree[u] = 0; }
}
static void revert(void) {
    logging = 0;
    for (long i = loglen - 1; i >= 0; i--) { if (logt[i] == 1) remove_v(logv[i]); else add_v(logv[i]); }
    drain();
}
static void write_best(void) {
    char tmp[4096]; snprintf(tmp, sizeof tmp, "%s.tmp", outfile);
    FILE *f = fopen(tmp, "w"); if (!f) return;
    for (int i = 0; i < bestsz; i++) fprintf(f, "%d\n", bestsol[i]);
    fclose(f); rename(tmp, outfile);
}
static void save_best(void) {
    bestsz = solsz; memcpy(bestsol, sol, sizeof(int32_t) * solsz);
}
static void restore_best(void) {
    logging = 0;
    while (solsz) remove_v(sol[solsz - 1]);
    drain();
    for (int i = 0; i < bestsz; i++) add_v(bestsol[i]);
    local_search();
}
static void status(const char *tag, int cur) {
    fprintf(stderr, "%s iter=%lld cur=%d best=%d t=%.0fs\n", tag, iter, cur, bestsz, now() - t0);
}

int main(int argc, char **argv) {
    if (argc < 6) { fprintf(stderr, "usage: arw HEXBIN OUTFILE SEEDFILE|- SECONDS RNG [RESTART]\n"); return 1; }
    outfile = argv[2];
    double tlim = atof(argv[4]);
    rs ^= (uint64_t)atoll(argv[5]) * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 10; i++) rnd64();
    if (argc > 6) RESTART = atoll(argv[6]);
    PK = (argc > 7) ? atof(argv[7]) : -1;
    Hex h = hex_load(argv[1]);
    NV = h.N; Q1 = h.q + 1;
    adj = malloc(sizeof(int32_t) * (size_t)NV * D);
    for (int x = 0; x < NV; x++) {
        int k = 0;
        for (int i = 0; i < Q1; i++) {
            int l = h.PL[(size_t)x * Q1 + i];
            for (int t = 0; t < Q1; t++) { int y = h.LP[(size_t)l * Q1 + t]; if (y != x) { if (k >= D) { fprintf(stderr, "degree > 90 at %d\n", x); return 1; } adj[(size_t)x * D + k++] = y; } }
        }
        if (k != D) { fprintf(stderr, "degree %d at %d\n", k, x); return 1; }
        int32_t *r = adj + (size_t)x * D;
        for (int i = 1; i < D; i++) { int32_t v = r[i]; int j = i - 1; while (j >= 0 && r[j] > v) { r[j + 1] = r[j]; j--; } r[j + 1] = v; }
        for (int i = 1; i < D; i++) if (r[i] == r[i - 1]) { fprintf(stderr, "dup neighbour\n"); return 1; }
    }
    inS = calloc(NV, 1); inq = calloc(NV, 1); infree = calloc(NV, 1);
    tight = calloc(NV, sizeof(int32_t)); sumS = calloc(NV, sizeof(int32_t));
    sol = malloc(sizeof(int32_t) * NV); pos = malloc(sizeof(int32_t) * NV);
    freest = malloc(sizeof(int32_t) * NV); queue = malloc(sizeof(int32_t) * NV);
    lastmv = calloc(NV, sizeof(int32_t)); bestsol = malloc(sizeof(int32_t) * NV);
    t0 = now();
    if (strcmp(argv[3], "-")) {
        int *ids; int n = read_ids(argv[3], &ids); int skipped = 0;
        for (int i = 0; i < n; i++) { int v = ids[i]; if (v < 0 || v >= NV) { skipped++; continue; } if (!inS[v] && tight[v] == 0) add_v(v); else skipped++; }
        fprintf(stderr, "seed %s: %d ids, %d skipped\n", argv[3], n, skipped);
    } else {
        int *perm = malloc(sizeof(int) * NV);
        for (int i = 0; i < NV; i++) perm[i] = i;
        for (int i = NV - 1; i > 0; i--) { int j = rndi(i + 1); int t = perm[i]; perm[i] = perm[j]; perm[j] = t; }
        for (int i = 0; i < NV; i++) if (!inS[perm[i]] && tight[perm[i]] == 0) add_v(perm[i]);
        fprintf(stderr, "random greedy start size %d\n", solsz);
    }
    for (int v = 0; v < NV; v++) if (!inS[v] && tight[v] == 0) push_f(v);
    for (int i = 0; i < solsz; i++) push_q(sol[i]);
    local_search();
    save_best(); write_best();
    int cursz = solsz;
    status("init", cursz);
    double lastprint = now(), lastwrite = now();
    long long saves = 0;
    while (1) {
        if ((iter & 1023) == 0) {
            double t = now();
            if (t - t0 > tlim) break;
            if (t - lastprint > 15) { status("prog", cursz); lastprint = t; }
        }
        iter++;
        logging = 1; loglen = 0;
        perturb();
        logging = 0;
        int ns = solsz;
        if (ns > bestsz) {
            save_best(); last_imp = iter;
            if (now() - lastwrite > 2.0 || 1) { write_best(); lastwrite = now(); saves++; fprintf(stderr, "NEW BEST %d at iter %lld t=%.0fs\n", bestsz, iter, now() - t0); }
        }
        if (ns >= cursz) cursz = ns;
        else {
            int d = cursz - ns, ds = bestsz - ns;
            double pacc = 1.0 / (1.0 + (double)d * ds);
            if (rndu() < pacc) cursz = ns; else revert();
        }
        if (iter - last_imp > RESTART && cursz < bestsz) {
            restore_best(); cursz = solsz; last_imp = iter;
            fprintf(stderr, "restart to best at iter %lld\n", iter);
        }
    }
    write_best();
    status("final", cursz);
    /* final independence check */
    for (int i = 0; i < bestsz; i++) for (int j = i + 1; j < bestsz; j++) if (isadj(bestsol[i], bestsol[j])) { fprintf(stderr, "BUG: adjacent pair\n"); return 2; }
    printf("BEST %d %s\n", bestsz, outfile);
    return 0;
}
