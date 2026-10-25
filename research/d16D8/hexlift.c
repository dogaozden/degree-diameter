/* hexlift.c: search and check Z_m-lifts of H(q) + t point-line matchings at diameter D (bipartite).

   Design (text file): first line "q m t", then N lines for points p = 0..N-1:
       M_1(p) v_1(p) ... M_t(p) v_t(p)  s_0 ... s_q
   where M_k(p) is a line index 0..N-1, v_k(p) in Z_m the level shift of the extra edge (p,i)~(M_k(p),i+v_k(p)),
   and s_j the shift of the hexagon flag (p, j-th line through p in hex.pl order).

   Usage:
     hexlift eval HEX DESIGN D [nsrc]          count (vertex,level) pairs not within distance from sources
     hexlift anneal HEX m t D secs seed OUT [opts via env]
   env: SIG=1 also anneal hexagon flag shifts; NSRC=k evaluate on k random sources (0 = all, default);
        INC=1 extra edges must be incident flags (M_k(p) through p), JUMPDIST=d require d(p,M_k(p)) == d;
        T0, T1 temperatures; INIT=file start design.
*/
#include "hexlift.h"
#include <math.h>
#include <time.h>

static Hex *H;
static int q1, N, V, m, t, deg;
static int *Mk;    /* t*N : line index */
static int *vk;    /* t*N */
static int *sg;    /* N*q1 */
static Adj A;
static u64 *R, *F, *X;

static uint64_t rs = 88172645463325252ULL;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline int rndi(int n) { return (int)(rnd() % (uint64_t)n); }
static double now(void) { struct timespec ts; clock_gettime(CLOCK_MONOTONIC, &ts); return ts.tv_sec + 1e-9 * ts.tv_nsec; }

static void build_adj(void) {
    deg = q1 + t;
    A.V = V; A.deg = deg; A.m = m;
    if (!A.nb) { A.nb = malloc(sizeof(int) * (size_t)V * deg); A.sh = malloc(sizeof(int) * (size_t)V * deg); }
    int *fill = calloc(V, sizeof(int));
    for (int p = 0; p < N; p++) {
        for (int j = 0; j < q1; j++) {
            int l = H->pl[(size_t)p * q1 + j], s = sg[(size_t)p * q1 + j];
            A.nb[(size_t)p * deg + fill[p]] = N + l; A.sh[(size_t)p * deg + fill[p]] = s; fill[p]++;
            A.nb[(size_t)(N + l) * deg + fill[N + l]] = p; A.sh[(size_t)(N + l) * deg + fill[N + l]] = s ? m - s : 0; fill[N + l]++;
        }
        for (int k = 0; k < t; k++) {
            int l = Mk[(size_t)k * N + p], s = vk[(size_t)k * N + p];
            A.nb[(size_t)p * deg + fill[p]] = N + l; A.sh[(size_t)p * deg + fill[p]] = s; fill[p]++;
            A.nb[(size_t)(N + l) * deg + fill[N + l]] = p; A.sh[(size_t)(N + l) * deg + fill[N + l]] = s ? m - s : 0; fill[N + l]++;
        }
    }
    for (int x = 0; x < V; x++) if (fill[x] != deg) { fprintf(stderr, "degree error at %d: %d != %d (matching not a bijection?)\n", x, fill[x], deg); exit(1); }
    free(fill);
}

static int *srcs; static int nsrc;
static long evaluate(int D) {
    long tot = 0;
    for (int i = 0; i < nsrc; i++) tot += bfs_uncovered(&A, srcs[i], D, R, F, X, srcs[i] < N);
    return tot;
}

static void alloc_design(void) {
    Mk = malloc(sizeof(int) * (size_t)t * N); vk = malloc(sizeof(int) * (size_t)t * N);
    sg = calloc((size_t)N * q1, sizeof(int));
}

static int read_design(const char *fn) {
    FILE *f = fopen(fn, "r"); if (!f) { fprintf(stderr, "cannot open %s\n", fn); exit(1); }
    int qq; if (fscanf(f, "%d %d %d", &qq, &m, &t) != 3 || qq != H->q) { fprintf(stderr, "bad design header\n"); exit(1); }
    alloc_design();
    for (int p = 0; p < N; p++) {
        for (int k = 0; k < t; k++) if (fscanf(f, "%d %d", &Mk[(size_t)k * N + p], &vk[(size_t)k * N + p]) != 2) { fprintf(stderr, "short design\n"); exit(1); }
        for (int j = 0; j < q1; j++) if (fscanf(f, "%d", &sg[(size_t)p * q1 + j]) != 1) { fprintf(stderr, "short design\n"); exit(1); }
    }
    fclose(f);
    return 0;
}
static void write_design(const char *fn) {
    FILE *f = fopen(fn, "w");
    fprintf(f, "%d %d %d\n", H->q, m, t);
    for (int p = 0; p < N; p++) {
        for (int k = 0; k < t; k++) fprintf(f, "%d %d ", Mk[(size_t)k * N + p], vk[(size_t)k * N + p]);
        for (int j = 0; j < q1; j++) fprintf(f, "%d%c", sg[(size_t)p * q1 + j], j == q1 - 1 ? '\n' : ' ');
    }
    fclose(f);
}

/* hexagon distances from a vertex (plain BFS on H(q)) */
static int *hdist_buf;
static void hex_bfs(int src, int *dist) {
    int *qu = malloc(sizeof(int) * V); int h = 0, tl = 0;
    for (int x = 0; x < V; x++) dist[x] = -1;
    dist[src] = 0; qu[tl++] = src;
    while (h < tl) {
        int x = qu[h++];
        if (x < N) { for (int j = 0; j < q1; j++) { int y = N + H->pl[(size_t)x * q1 + j]; if (dist[y] < 0) { dist[y] = dist[x] + 1; qu[tl++] = y; } } }
        else { int l = x - N; for (int j = 0; j < q1; j++) { int y = H->lp[(size_t)l * q1 + j]; if (dist[y] < 0) { dist[y] = dist[x] + 1; qu[tl++] = y; } } }
    }
    free(qu);
}

static void random_matchings(int jumpdist) {
    /* random bijections P->L; if jumpdist>0 try to make d(p, M_k(p)) == jumpdist by random repair */
    int *perm = malloc(sizeof(int) * N);
    for (int k = 0; k < t; k++) {
        for (int i = 0; i < N; i++) perm[i] = i;
        for (int i = N - 1; i > 0; i--) { int j = rndi(i + 1); int x = perm[i]; perm[i] = perm[j]; perm[j] = x; }
        for (int p = 0; p < N; p++) Mk[(size_t)k * N + p] = perm[p];
    }
    free(perm);
    (void)jumpdist;
}

int main(int argc, char **argv) {
    if (argc < 4) { fprintf(stderr, "usage: see header\n"); return 1; }
    H = hex_load(argv[2]); q1 = H->q + 1; N = H->N; V = H->V;
    R = malloc(sizeof(u64) * V); F = malloc(sizeof(u64) * V); X = malloc(sizeof(u64) * V);
    if (!strcmp(argv[1], "eval")) {
        read_design(argv[3]);
        int D = atoi(argv[4]);
        nsrc = argc > 5 ? atoi(argv[5]) : V;
        srcs = malloc(sizeof(int) * V);
        if (nsrc >= V) { nsrc = V; for (int i = 0; i < V; i++) srcs[i] = i; }
        else for (int i = 0; i < nsrc; i++) srcs[i] = rndi(V);
        build_adj();
        double t0 = now();
        long u = evaluate(D);
        printf("q=%d m=%d t=%d D=%d sources=%d uncovered=%ld time=%.2fs %s\n", H->q, m, t, D, nsrc, u, now() - t0,
               u == 0 && nsrc == V ? "VALID(all sources)" : "");
        return 0;
    }

    if (!strcmp(argv[1], "diag")) {
        read_design(argv[3]);
        int D = atoi(argv[4]); int ns = argc > 5 ? atoi(argv[5]) : V;
        build_adj();
        int *dist = malloc(sizeof(int) * V);
        long hist[2][8] = {{0}}; long tot = 0;
        for (int i = 0; i < ns; i++) {
            int s = (ns >= V) ? i : rndi(V);
            bfs_uncovered(&A, s, D, R, F, X, s < N);
            hex_bfs(s, dist);
            for (int x = 0; x < V; x++) { int u = m - __builtin_popcountll(R[x]); if (u) { hist[(s < N) == (x < N) ? 0 : 1][dist[x]] += u; tot += u; } }
        }
        printf("uncovered %ld by hexagon distance (same side / cross):\n", tot);
        for (int d = 0; d <= 6; d++) printf("  d=%d  same %ld  cross %ld\n", d, hist[0][d], hist[1][d]);
        return 0;
    }
    if (!strcmp(argv[1], "anneal")) {
        m = atoi(argv[3]); t = atoi(argv[4]); int D = atoi(argv[5]); double secs = atof(argv[6]);
        rs ^= (uint64_t)atoll(argv[7]) * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 10; i++) rnd();
        const char *out = argv[8];
        int SIG = getenv("SIG") ? atoi(getenv("SIG")) : 0;
        double T0 = getenv("T0") ? atof(getenv("T0")) : 2.0, T1 = getenv("T1") ? atof(getenv("T1")) : 0.05;
        int ns = getenv("NSRC") ? atoi(getenv("NSRC")) : 0;
        if (getenv("INIT")) { read_design(getenv("INIT")); }
        else {
            alloc_design();
            random_matchings(0);
            for (size_t i = 0; i < (size_t)t * N; i++) vk[i] = rndi(m);
            if (SIG) for (size_t i = 0; i < (size_t)N * q1; i++) sg[i] = rndi(m);
        }
        srcs = malloc(sizeof(int) * V);
        if (ns <= 0 || ns >= V) { nsrc = V; for (int i = 0; i < V; i++) srcs[i] = i; }
        else { nsrc = ns; for (int i = 0; i < nsrc; i++) srcs[i] = rndi(V); }
        build_adj();
        long cur = evaluate(D), best = cur;
        write_design(out);
        double t0 = now(), last = t0; long it = 0, acc = 0;
        fprintf(stderr, "start cost %ld\n", cur);
        while (now() - t0 < secs && best > 0) {
            double fr = (now() - t0) / secs; double T = T0 * pow(T1 / T0, fr);
            int mv = rndi(SIG ? 3 : 2);
            int k = rndi(t), p = rndi(N), p2 = -1, oldv = 0, j = 0;
            if (mv == 0) { oldv = vk[(size_t)k * N + p]; int nv = rndi(m); if (nv == oldv) continue; vk[(size_t)k * N + p] = nv; }
            else if (mv == 1) { p2 = rndi(N); if (p2 == p) continue; int x = Mk[(size_t)k * N + p]; Mk[(size_t)k * N + p] = Mk[(size_t)k * N + p2]; Mk[(size_t)k * N + p2] = x; }
            else { j = rndi(q1); oldv = sg[(size_t)p * q1 + j]; int nv = rndi(m); if (nv == oldv) continue; sg[(size_t)p * q1 + j] = nv; }
            build_adj();
            long c = evaluate(D); it++;
            if (c <= cur || exp((double)(cur - c) / T) * 4294967296.0 > (double)(rnd() & 0xffffffffULL)) {
                cur = c; acc++;
                if (c < best) { best = c; write_design(out); }
            } else {
                if (mv == 0) vk[(size_t)k * N + p] = oldv;
                else if (mv == 1) { int x = Mk[(size_t)k * N + p]; Mk[(size_t)k * N + p] = Mk[(size_t)k * N + p2]; Mk[(size_t)k * N + p2] = x; }
                else sg[(size_t)p * q1 + j] = oldv;
            }
            if (now() - last > 10) { last = now(); fprintf(stderr, "t=%.0f it=%ld acc=%ld T=%.3f cur=%ld best=%ld\n", now() - t0, it, acc, T, cur, best); }
        }
        printf("RESULT q=%d m=%d t=%d D=%d best=%ld it=%ld nsrc=%d out=%s\n", H->q, m, t, D, best, it, nsrc, out);
        return 0;
    }
    fprintf(stderr, "unknown mode\n");
    return 1;
}
