/* baselift.c: diameter check and annealing for Z_k-lifts of an arbitrary base multigraph (k <= 64).

   Lift: vertex (x, g), x a base vertex 0..V-1, g in Z_k. A base edge "x y c cls" gives (x, g) ~ (y, g + c) for all g.
   Base file (text): header "V k E", then E lines "x y c cls" (0 <= c < k; cls = edge class, 0 = fixed; the annealer
   may change the voltage of edges with cls >= 1, and swap the y ends of two edges of the same class cls >= 100). Loops x == x with c != 0 are allowed (they give (x,g) ~ (x,g+c)).

   The check counts uncovered (vertex, sheet) pairs: for each source s, the pairs (y, g) with no walk of length <= D
   from (s, 0). By the Z_k symmetry the lift has diameter <= D iff the count is 0 over all base vertices as sources.
   For a bipartite lift this is exactly "same side within D, other side within D-1" when D is even.
   Sources are packed floor(64/k) per 64-bit word, so one pass serves several sources.

   Usage:
     baselift eval BASE D [nsrc|all] [seed]        uncovered pairs; "VALID(all sources)" when 0 from all sources
     baselift diag BASE D [nsrc]                     uncovered pairs by source vertex class (first 8 classes of x/BLK)
     baselift anneal BASE D secs seed OUT            simulated annealing (moves on edges with cls >= 1)
   env: THREADS (default 1), NSRC (anneal sources; default all), SRCFILE (list of sources), MOVES (v = new voltage on
        one movable edge, M = swap the targets of two movable edges of the same class), T0, T1, BLK (diag grouping). */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <time.h>
#ifdef _OPENMP
#include <omp.h>
#endif
typedef uint64_t u64;

static int V, k, E, P;                 /* P = sources per word */
static int *ex, *ey, *ec, *ecls;       /* edges */
static int *off, *nb, *sh;             /* CSR adjacency: x -> nb with shift sh */
static u64 HI[64], LO[64], USED;
static int nthr = 1;

static uint64_t rs = 88172645463325252ULL;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline int rndi(int n) { return (int)(rnd() % (uint64_t)n); }
static double now(void) { struct timespec ts; clock_gettime(CLOCK_MONOTONIC, &ts); return ts.tv_sec + 1e-9 * ts.tv_nsec; }

static void setup_masks(void) {
    P = 64 / k; USED = 0;
    for (int i = 0; i < P * k; i++) USED |= 1ULL << i;
    for (int c = 0; c < k; c++) {
        HI[c] = LO[c] = 0;
        for (int i = 0; i < P * k; i++) { if (i % k >= c) HI[c] |= 1ULL << i; else LO[c] |= 1ULL << i; }
    }
}
static inline u64 rot(u64 x, int c) {
    if (!c) return x;
    return ((x << c) & HI[c]) | ((x >> (k - c)) & LO[c]);
}

static void build_adj(void) {
    int *deg = calloc(V, sizeof(int));
    for (int e = 0; e < E; e++) { deg[ex[e]]++; deg[ey[e]]++; }
    if (!off) off = malloc(sizeof(int) * (V + 1));
    off[0] = 0; for (int x = 0; x < V; x++) off[x + 1] = off[x] + deg[x];
    if (!nb) { nb = malloc(sizeof(int) * off[V]); sh = malloc(sizeof(int) * off[V]); }
    int *fill = calloc(V, sizeof(int));
    for (int e = 0; e < E; e++) {
        int x = ex[e], y = ey[e], c = ec[e];
        nb[off[x] + fill[x]] = y; sh[off[x] + fill[x]++] = c;
        nb[off[y] + fill[y]] = x; sh[off[y] + fill[y]++] = (k - c) % k;
    }
    free(deg); free(fill);
}

static void read_base(const char *fn) {
    FILE *f = fopen(fn, "r"); if (!f) { fprintf(stderr, "cannot open %s\n", fn); exit(1); }
    if (fscanf(f, "%d %d %d", &V, &k, &E) != 3) { fprintf(stderr, "bad header\n"); exit(1); }
    if (k < 1 || k > 64) { fprintf(stderr, "need 1 <= k <= 64\n"); exit(1); }
    ex = malloc(sizeof(int) * E); ey = malloc(sizeof(int) * E); ec = malloc(sizeof(int) * E); ecls = malloc(sizeof(int) * E);
    for (int e = 0; e < E; e++) {
        if (fscanf(f, "%d %d %d %d", &ex[e], &ey[e], &ec[e], &ecls[e]) != 4) { fprintf(stderr, "short base file at edge %d\n", e); exit(1); }
        if (ex[e] < 0 || ex[e] >= V || ey[e] < 0 || ey[e] >= V || ec[e] < 0 || ec[e] >= k) { fprintf(stderr, "bad edge %d\n", e); exit(1); }
    }
    fclose(f);
    setup_masks(); build_adj();
}
static void write_base(const char *fn) {
    char tmpn[1024]; snprintf(tmpn, sizeof tmpn, "%s.tmp", fn);
    FILE *f = fopen(tmpn, "w"); fprintf(f, "%d %d %d\n", V, k, E);
    for (int e = 0; e < E; e++) fprintf(f, "%d %d %d %d\n", ex[e], ey[e], ec[e], ecls[e]);
    fclose(f); rename(tmpn, fn);
}

typedef struct { u64 *R, *F, *X; } Scratch;
static Scratch *new_scratch(void) {
    Scratch *s = malloc(sizeof(Scratch));
    s->R = malloc(sizeof(u64) * V); s->F = malloc(sizeof(u64) * V); s->X = malloc(sizeof(u64) * V);
    return s;
}
/* BFS from up to P sources at once (source i at bit block i, sheet 0); returns uncovered pairs */
static long bfs_batch(const int *src, int ns, int D, Scratch *S) {
    u64 *R = S->R, *F = S->F, *X = S->X;
    memset(R, 0, sizeof(u64) * V); memset(F, 0, sizeof(u64) * V);
    for (int i = 0; i < ns; i++) { R[src[i]] |= 1ULL << (i * k); F[src[i]] |= 1ULL << (i * k); }
    for (int d = 1; d <= D; d++) {
        for (int x = 0; x < V; x++) {
            u64 acc = 0;
            for (int j = off[x]; j < off[x + 1]; j++) { u64 f = F[nb[j]]; if (f) acc |= rot(f, (k - sh[j]) % k); }
            X[x] = acc & ~R[x];
        }
        for (int x = 0; x < V; x++) R[x] |= X[x];
        u64 *tp = F; F = X; X = tp;
    }
    S->F = F; S->X = X;
    long miss = 0;
    for (int x = 0; x < V; x++) miss += (long)ns * k - __builtin_popcountll(R[x]);
    return miss;
}

static int *srcs, nsrc;
static Scratch **SC;
static long eval_all(int D, long limit) {
    long tot = 0; int stop = 0, nb_ = (nsrc + P - 1) / P;
    #pragma omp parallel for schedule(dynamic, 1) num_threads(nthr)
    for (int b = 0; b < nb_; b++) {
        int st;
        #pragma omp atomic read
        st = stop;
        if (st) continue;
        int tid = 0;
#ifdef _OPENMP
        tid = omp_get_thread_num();
#endif
        int ns = nsrc - b * P < P ? nsrc - b * P : P;
        long u = bfs_batch(srcs + (size_t)b * P, ns, D, SC[tid]);
        long nt;
        #pragma omp atomic capture
        { tot += u; nt = tot; }
        if (limit >= 0 && nt > limit) {
            #pragma omp atomic write
            stop = 1;
        }
    }
    return tot;
}
static void pick_sources(int ns) {
    srcs = malloc(sizeof(int) * (V > 1 ? V : 1));
    if (getenv("SRCFILE")) {
        FILE *f = fopen(getenv("SRCFILE"), "r"); if (!f) { fprintf(stderr, "no SRCFILE\n"); exit(1); }
        nsrc = 0; int x;
        while (nsrc < V && fscanf(f, "%d", &x) == 1) srcs[nsrc++] = x;
        fclose(f); return;
    }
    if (ns <= 0 || ns >= V) { nsrc = V; for (int i = 0; i < V; i++) srcs[i] = i; return; }
    nsrc = ns; for (int i = 0; i < ns; i++) srcs[i] = rndi(V);
}

int main(int argc, char **argv) {
    if (argc < 4) { fprintf(stderr, "usage: baselift eval|diag|anneal BASE D ...\n"); return 1; }
    if (getenv("THREADS")) nthr = atoi(getenv("THREADS"));
    read_base(argv[2]);
    int D = atoi(argv[3]);
    SC = malloc(sizeof(Scratch *) * nthr); for (int i = 0; i < nthr; i++) SC[i] = new_scratch();
    if (!strcmp(argv[1], "eval")) {
        int ns = (argc > 4 && strcmp(argv[4], "all")) ? atoi(argv[4]) : 0;
        if (argc > 5) { rs ^= (uint64_t)atoll(argv[5]) * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 10; i++) rnd(); }
        pick_sources(ns);
        double t0 = now(); long u = eval_all(D, -1);
        printf("V=%d k=%d E=%d D=%d lift_vertices=%lld sources=%d uncovered=%ld time=%.2fs%s\n", V, k, E, D,
               (long long)V * k, nsrc, u, now() - t0, (u == 0 && nsrc == V && !getenv("SRCFILE")) ? " VALID(all sources)" : "");
        return 0;
    }
    if (!strcmp(argv[1], "diag")) {
        int ns = argc > 4 ? atoi(argv[4]) : 0; pick_sources(ns);
        int blk = getenv("BLK") ? atoi(getenv("BLK")) : V;
        long cls[64] = {0}, tot = 0;
        for (int i = 0; i < nsrc; i++) {
            long u = bfs_batch(srcs + i, 1, D, SC[0]); int c = srcs[i] / blk; if (c > 63) c = 63; cls[c] += u; tot += u;
        }
        printf("uncovered %ld over %d sources; by source block (x/%d):", tot, nsrc, blk);
        for (int c = 0; c < 64; c++) if (cls[c]) printf(" [%d]=%ld", c, cls[c]);
        printf("\n");
        return 0;
    }
    if (!strcmp(argv[1], "anneal")) {
        double secs = atof(argv[4]);
        rs ^= (uint64_t)atoll(argv[5]) * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 10; i++) rnd();
        const char *out = argv[6];
        const char *moves = getenv("MOVES") ? getenv("MOVES") : "v";
        int nmv = strlen(moves);
        double T0 = getenv("T0") ? atof(getenv("T0")) : 2.0, T1 = getenv("T1") ? atof(getenv("T1")) : 0.05;
        pick_sources(getenv("NSRC") ? atoi(getenv("NSRC")) : 0);
        int fixmod = getenv("FIXMOD") ? atoi(getenv("FIXMOD")) : 1;
        if (fixmod > 1 && k % fixmod) { fprintf(stderr, "FIXMOD must divide k\n"); return 1; }
        int *mov = malloc(sizeof(int) * E), nm = 0;
        for (int e = 0; e < E; e++) if (ecls[e] >= 1) mov[nm++] = e;
        if (!nm) { fprintf(stderr, "no movable edges\n"); return 1; }
        long cur = eval_all(D, -1), best = cur;
        write_base(out);
        double t0 = now(), last = t0; long it = 0, acc = 0;
        fprintf(stderr, "start cost %ld (sources %d, movable edges %d)\n", cur, nsrc, nm);
        while (best > 0 && now() - t0 < secs) {
            double fr = (now() - t0) / secs, T = T0 * pow(T1 / T0, fr);
            char mv = moves[rndi(nmv)];
            int e1 = mov[rndi(nm)], e2 = -1, old = 0;
            if (mv == 'v') {
                old = ec[e1]; int nv = rndi(k);
                if (fixmod > 1) nv = old % fixmod + fixmod * rndi(k / fixmod);   /* keep the Z_fixmod part */
                if (nv == old) continue;
                ec[e1] = nv;
            }
            else {
                e2 = mov[rndi(nm)]; if (e2 == e1 || ecls[e2] != ecls[e1] || ecls[e1] < 100) continue;
                int y = ey[e1]; ey[e1] = ey[e2]; ey[e2] = y;
            }
            build_adj();
            double u = (rnd() >> 11) * (1.0 / 9007199254740992.0) + 1e-300;
            long lim = cur + (long)floor(-T * log(u));
            long c = eval_all(D, lim); it++;
            if (c <= lim) { cur = c; acc++; if (c < best) { best = c; write_base(out); } }
            else {
                if (mv == 'v') ec[e1] = old; else { int y = ey[e1]; ey[e1] = ey[e2]; ey[e2] = y; }
            }
            if (now() - last > 15) { last = now(); fprintf(stderr, "t=%.0f it=%ld acc=%ld T=%.3f cur=%ld best=%ld\n", now() - t0, it, acc, T, cur, best); }
        }
        build_adj();
        printf("RESULT V=%d k=%d D=%d best=%ld it=%ld sources=%d out=%s\n", V, k, D, best, it, nsrc, out);
        return 0;
    }
    fprintf(stderr, "unknown command\n"); return 1;
}
