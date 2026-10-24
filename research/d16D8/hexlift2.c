/* hexlift2.c: check and anneal lifts of H(q) + t point-line matchings, voltage group Z_m1 x Z_m2 (m1*m2 <= 64).

   Lift: vertex (x, g), x a hexagon point (0..N-1) or line (N..2N-1), g in G = Z_m1 x Z_m2.
   Hexagon flag (p,l): (p,g) ~ (l, g + s_flag).  Extra edge k of point p: (p,g) ~ (M_k(p), g + v_k(p)).
   A shift is stored as one integer c = c1 + m1*c2 (c1 in Z_m1, c2 in Z_m2); the level index of g = (g1,g2) is g1 + m1*g2.

   Design file (text): header "q m1 m2 t", then N rows (points p = 0..N-1):
       M_1(p) v_1(p) ... M_t(p) v_t(p)  s_0 ... s_q
   M_k(p): line index 0..N-1 (hex/hex_q*.bin numbering); s_j: shift of the flag (p, j-th line of p), where the lines of
   p are listed in increasing line index (the order in which hexgen's line table first mentions p).
   Old hexlift designs ("q m t" header) are read with m1 = m, m2 = 1.

   Usage:
     hexlift2 eval HEX DESIGN D [nsrc|all] [seed]     uncovered (vertex,level) pairs from the sources; VALID if 0 from all
     hexlift2 diag HEX DESIGN D [nsrc]               uncovered pairs by hexagon distance and side
     hexlift2 anneal HEX DESIGN_IN D secs seed OUT   simulated annealing from DESIGN_IN (cost = uncovered over sources)
   env: THREADS (default 1), NSRC (anneal: number of random sources, default all), MOVES (string of letters:
        v = jump shift, s = flag shift, M = swap two matching targets; default "vM"), T0, T1 (temperature range),
        SRCFILE (file of source vertex ids instead of random/all).
   Distances: the lift is bipartite (points | lines), so D steps reach the same side within D and the other side
   within D-1; the count is over all (vertex, level) pairs not reached. */
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

static int q, q1, N, V, t, m1, m2, m, deg;
static int *lp, *pl;            /* line->points, point->lines (line index) */
static int *Mk, *vk, *sg;       /* t*N, t*N, N*q1 */
static int *nb, *sh;            /* V*deg adjacency: neighbour, shift code (x -> nb) */
static int *neg;                /* neg[c] = code of -c */
static u64 FULL, *segA;         /* segA[c1]: bits with i1 >= c1 */

static uint64_t rs = 88172645463325252ULL;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline int rndi(int n) { return (int)(rnd() % (uint64_t)n); }
static double now(void) { struct timespec ts; clock_gettime(CLOCK_MONOTONIC, &ts); return ts.tv_sec + 1e-9 * ts.tv_nsec; }

static void load_hex(const char *fn) {
    FILE *f = fopen(fn, "rb"); if (!f) { fprintf(stderr, "cannot open %s\n", fn); exit(1); }
    int32_t h[3]; if (fread(h, 4, 3, f) != 3) exit(1);
    q = h[0]; N = h[1]; q1 = q + 1; V = 2 * N;
    int32_t *tmp = malloc(4 * (size_t)N * q1);
    if (fread(tmp, 4, (size_t)N * q1, f) != (size_t)N * q1) { fprintf(stderr, "short hex file\n"); exit(1); }
    fclose(f);
    lp = malloc(sizeof(int) * (size_t)N * q1); pl = malloc(sizeof(int) * (size_t)N * q1);
    int *cnt = calloc(N, sizeof(int));
    for (size_t i = 0; i < (size_t)N * q1; i++) lp[i] = tmp[i];
    for (int l = 0; l < N; l++) for (int j = 0; j < q1; j++) { int p = lp[(size_t)l * q1 + j]; pl[(size_t)p * q1 + cnt[p]++] = l; }
    for (int p = 0; p < N; p++) if (cnt[p] != q1) { fprintf(stderr, "bad hexagon\n"); exit(1); }
    free(cnt); free(tmp);
}

static void setup_group(void) {
    m = m1 * m2; if (m > 64 || m < 1) { fprintf(stderr, "need m1*m2 <= 64\n"); exit(1); }
    FULL = (m == 64) ? ~0ULL : ((1ULL << m) - 1);
    neg = malloc(sizeof(int) * m);
    for (int c = 0; c < m; c++) { int c1 = c % m1, c2 = c / m1; neg[c] = ((m1 - c1) % m1) + m1 * ((m2 - c2) % m2); }
    segA = malloc(sizeof(u64) * m1);
    for (int c1 = 0; c1 < m1; c1++) { u64 a = 0; for (int i = 0; i < m; i++) if (i % m1 >= c1) a |= 1ULL << i; segA[c1] = a; }
}
/* apply shift code c to a level mask */
static inline u64 shiftm(u64 x, int c) {
    if (!c) return x;
    int c1 = c % m1, c2 = c / m1;
    if (c2) { int r = m1 * c2; x = ((x << r) | (x >> (m - r))) & FULL; }
    if (c1) { u64 hi = (x << c1) & segA[c1], lo = (x >> (m1 - c1)) & ~segA[c1] & FULL; x = hi | lo; }
    return x;
}

static void build_adj(void) {
    deg = q1 + t;
    if (!nb) { nb = malloc(sizeof(int) * (size_t)V * deg); sh = malloc(sizeof(int) * (size_t)V * deg); }
    int *fill = calloc(V, sizeof(int));
    for (int p = 0; p < N; p++) {
        for (int j = 0; j < q1; j++) {
            int l = N + pl[(size_t)p * q1 + j], s = sg[(size_t)p * q1 + j];
            nb[(size_t)p * deg + fill[p]] = l; sh[(size_t)p * deg + fill[p]++] = s;
            nb[(size_t)l * deg + fill[l]] = p; sh[(size_t)l * deg + fill[l]++] = neg[s];
        }
        for (int k = 0; k < t; k++) {
            int l = N + Mk[(size_t)k * N + p], s = vk[(size_t)k * N + p];
            nb[(size_t)p * deg + fill[p]] = l; sh[(size_t)p * deg + fill[p]++] = s;
            nb[(size_t)l * deg + fill[l]] = p; sh[(size_t)l * deg + fill[l]++] = neg[s];
        }
    }
    for (int x = 0; x < V; x++) if (fill[x] != deg) { fprintf(stderr, "degree error at vertex %d (matching not a bijection?)\n", x); exit(1); }
    free(fill);
}

/* BFS from (src, 0) for D steps; returns uncovered count; abort early (returning > limit) if count of
   uncovered after the final step would exceed limit -- only checked at the end, cheap enough. */
typedef struct { u64 *R, *F, *X; int *list, *list2; } Scratch;
static Scratch *new_scratch(void) {
    Scratch *s = malloc(sizeof(Scratch));
    s->R = malloc(sizeof(u64) * V); s->F = malloc(sizeof(u64) * V); s->X = malloc(sizeof(u64) * V);
    s->list = malloc(sizeof(int) * V); s->list2 = malloc(sizeof(int) * V);
    return s;
}
static long bfs(int src, int D, Scratch *S) {
    u64 *R = S->R, *F = S->F, *X = S->X;
    memset(R, 0, sizeof(u64) * V); memset(F, 0, sizeof(u64) * V); memset(X, 0, sizeof(u64) * V);
    R[src] = 1; F[src] = 1;
    int nl = 1; S->list[0] = src;           /* frontier vertex list while sparse */
    int sparse = 1;
    for (int d = 1; d <= D; d++) {
        if (sparse && (long)nl * deg < V / 4) {
            int nl2 = 0;
            for (int i = 0; i < nl; i++) {
                int y = S->list[i]; u64 f = F[y];
                const int *n = nb + (size_t)y * deg, *s = sh + (size_t)y * deg;
                for (int j = 0; j < deg; j++) {
                    int x = n[j]; u64 add = shiftm(f, s[j]) & ~R[x];
                    if (add) { if (!X[x]) S->list2[nl2++] = x; X[x] |= add; }
                }
            }
            for (int i = 0; i < nl; i++) F[S->list[i]] = 0;
            for (int i = 0; i < nl2; i++) { int x = S->list2[i]; R[x] |= X[x]; F[x] = X[x]; X[x] = 0; }
            int *tl = S->list; S->list = S->list2; S->list2 = tl; nl = nl2;
        } else {
            sparse = 0;
            for (int x = 0; x < V; x++) {
                u64 acc = 0; const int *n = nb + (size_t)x * deg, *s = sh + (size_t)x * deg;
                for (int j = 0; j < deg; j++) { u64 f = F[n[j]]; if (f) acc |= shiftm(f, neg[s[j]]); }
                X[x] = acc & ~R[x];
            }
            for (int x = 0; x < V; x++) R[x] |= X[x];
            u64 *tp = F; F = X; X = tp;
        }
    }
    S->F = F; S->X = X;
    long miss = 0;
    for (int x = 0; x < V; x++) miss += m - __builtin_popcountll(R[x]);
    return miss;
}

static int *srcs, nsrc, nthr = 1;
static Scratch **SC;
/* total uncovered over the sources; with limit >= 0 it stops as soon as the running total exceeds limit
   (then the returned value is > limit but not the full count) */
static long eval_all(int D, long limit) {
    long tot = 0; int stop = 0;
    #pragma omp parallel for schedule(dynamic, 1) num_threads(nthr)
    for (int i = 0; i < nsrc; i++) {
        int st;
        #pragma omp atomic read
        st = stop;
        if (st) continue;
        int tid = 0;
#ifdef _OPENMP
        tid = omp_get_thread_num();
#endif
        long u = bfs(srcs[i], D, SC[tid]);
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

static void alloc_design(void) {
    Mk = malloc(sizeof(int) * (size_t)t * N); vk = malloc(sizeof(int) * (size_t)t * N); sg = calloc((size_t)N * q1, sizeof(int));
}
static void read_design(const char *fn) {
    FILE *f = fopen(fn, "r"); if (!f) { fprintf(stderr, "cannot open %s\n", fn); exit(1); }
    char line[256]; if (!fgets(line, sizeof line, f)) exit(1);
    int a[4]; int n = sscanf(line, "%d %d %d %d", &a[0], &a[1], &a[2], &a[3]);
    if (n == 4) { m1 = a[1]; m2 = a[2]; t = a[3]; } else if (n == 3) { m1 = a[1]; m2 = 1; t = a[2]; } else { fprintf(stderr, "bad header\n"); exit(1); }
    if (a[0] != q) { fprintf(stderr, "design is for q=%d, hexagon q=%d\n", a[0], q); exit(1); }
    setup_group(); alloc_design();
    for (int p = 0; p < N; p++) {
        for (int k = 0; k < t; k++) if (fscanf(f, "%d %d", &Mk[(size_t)k * N + p], &vk[(size_t)k * N + p]) != 2) { fprintf(stderr, "short design\n"); exit(1); }
        for (int j = 0; j < q1; j++) if (fscanf(f, "%d", &sg[(size_t)p * q1 + j]) != 1) { fprintf(stderr, "short design\n"); exit(1); }
    }
    fclose(f);
    for (size_t i = 0; i < (size_t)t * N; i++) { if (vk[i] < 0 || vk[i] >= m || Mk[i] < 0 || Mk[i] >= N) { fprintf(stderr, "bad entry\n"); exit(1); } }
    for (size_t i = 0; i < (size_t)N * q1; i++) if (sg[i] < 0 || sg[i] >= m) { fprintf(stderr, "bad flag shift\n"); exit(1); }
}
static void write_design(const char *fn) {
    char tmpn[512]; snprintf(tmpn, sizeof tmpn, "%s.tmp", fn);
    FILE *f = fopen(tmpn, "w");
    fprintf(f, "%d %d %d %d\n", q, m1, m2, t);
    for (int p = 0; p < N; p++) {
        for (int k = 0; k < t; k++) fprintf(f, "%d %d ", Mk[(size_t)k * N + p], vk[(size_t)k * N + p]);
        for (int j = 0; j < q1; j++) fprintf(f, "%d%c", sg[(size_t)p * q1 + j], j == q1 - 1 ? '\n' : ' ');
    }
    fclose(f); rename(tmpn, fn);
}
static void hex_dist(int src, int *dist) {
    int *qu = malloc(sizeof(int) * V), h = 0, tl = 0;
    for (int x = 0; x < V; x++) dist[x] = -1;
    dist[src] = 0; qu[tl++] = src;
    while (h < tl) {
        int x = qu[h++];
        for (int j = 0; j < q1; j++) {
            int y = x < N ? N + pl[(size_t)x * q1 + j] : lp[(size_t)(x - N) * q1 + j];
            if (dist[y] < 0) { dist[y] = dist[x] + 1; qu[tl++] = y; }
        }
    }
    free(qu);
}
static void pick_sources(int ns) {
    srcs = malloc(sizeof(int) * V);
    if (getenv("SRCFILE")) {
        FILE *f = fopen(getenv("SRCFILE"), "r"); nsrc = 0; int x;
        while (nsrc < V && fscanf(f, "%d", &x) == 1) srcs[nsrc++] = x;
        fclose(f); return;
    }
    if (ns <= 0 || ns >= V) { nsrc = V; for (int i = 0; i < V; i++) srcs[i] = i; return; }
    nsrc = ns; for (int i = 0; i < ns; i++) srcs[i] = rndi(V);
}

int main(int argc, char **argv) {
    if (argc < 5) { fprintf(stderr, "usage: hexlift2 eval|diag|anneal HEX DESIGN D ...\n"); return 1; }
    if (getenv("THREADS")) nthr = atoi(getenv("THREADS"));
    load_hex(argv[2]); read_design(argv[3]); build_adj();
    int D = atoi(argv[4]);
    SC = malloc(sizeof(Scratch *) * nthr); for (int i = 0; i < nthr; i++) SC[i] = new_scratch();
    if (!strcmp(argv[1], "eval")) {
        int ns = (argc > 5 && strcmp(argv[5], "all")) ? atoi(argv[5]) : 0;
        if (argc > 6) { rs ^= (uint64_t)atoll(argv[6]) * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 10; i++) rnd(); }
        pick_sources(ns);
        double t0 = now(); long u = eval_all(D, -1);
        printf("q=%d G=Z%d x Z%d (m=%d) t=%d D=%d vertices=%lld sources=%d uncovered=%ld time=%.2fs%s\n", q, m1, m2, m, t, D,
               (long long)m * V, nsrc, u, now() - t0, (u == 0 && nsrc == V) ? " VALID(all sources)" : "");
        return 0;
    }
    if (!strcmp(argv[1], "diag")) {
        int ns = argc > 5 ? atoi(argv[5]) : 0; pick_sources(ns);
        int *dist = malloc(sizeof(int) * V); long hist[2][8] = {{0}}, tot = 0;
        for (int i = 0; i < nsrc; i++) {
            int s = srcs[i]; bfs(s, D, SC[0]); hex_dist(s, dist);
            for (int x = 0; x < V; x++) { int u = m - __builtin_popcountll(SC[0]->R[x]); if (u) { hist[(s < N) == (x < N) ? 0 : 1][dist[x]] += u; tot += u; } }
        }
        printf("uncovered %ld over %d sources, by hexagon distance (same side / other side):\n", tot, nsrc);
        for (int d = 0; d <= 6; d++) printf("  d=%d  same %ld  cross %ld\n", d, hist[0][d], hist[1][d]);
        return 0;
    }
    if (!strcmp(argv[1], "anneal")) {
        double secs = atof(argv[5]);
        rs ^= (uint64_t)atoll(argv[6]) * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 10; i++) rnd();
        const char *out = argv[7];
        const char *moves = getenv("MOVES") ? getenv("MOVES") : "vM";
        int nmv = strlen(moves);
        double T0 = getenv("T0") ? atof(getenv("T0")) : 2.0, T1 = getenv("T1") ? atof(getenv("T1")) : 0.05;
        pick_sources(getenv("NSRC") ? atoi(getenv("NSRC")) : 0);
        long cur = eval_all(D, -1), best = cur;
        write_design(out);
        double t0 = now(), last = t0; long it = 0, acc = 0;
        fprintf(stderr, "start cost %ld (sources %d)\n", cur, nsrc);
        while (best > 0 && now() - t0 < secs) {
            double fr = (now() - t0) / secs, T = T0 * pow(T1 / T0, fr);
            char mv = moves[rndi(nmv)];
            int k = rndi(t), p = rndi(N), p2 = 0, j = 0, old = 0;
            if (mv == 'v') { old = vk[(size_t)k * N + p]; int nv = rndi(m); if (nv == old) continue; vk[(size_t)k * N + p] = nv; }
            else if (mv == 's') { j = rndi(q1); old = sg[(size_t)p * q1 + j]; int nv = rndi(m); if (nv == old) continue; sg[(size_t)p * q1 + j] = nv; }
            else { p2 = rndi(N); if (p2 == p) continue; int x = Mk[(size_t)k * N + p]; Mk[(size_t)k * N + p] = Mk[(size_t)k * N + p2]; Mk[(size_t)k * N + p2] = x; }
            build_adj();
            double u = (rnd() >> 11) * (1.0 / 9007199254740992.0) + 1e-300;
            long lim = cur + (long)floor(-T * log(u));      /* accept iff cost <= lim */
            long c = eval_all(D, lim); it++;
            if (c <= lim) { cur = c; acc++; if (c < best) { best = c; write_design(out); } }
            else {
                if (mv == 'v') vk[(size_t)k * N + p] = old;
                else if (mv == 's') sg[(size_t)p * q1 + j] = old;
                else { int x = Mk[(size_t)k * N + p]; Mk[(size_t)k * N + p] = Mk[(size_t)k * N + p2]; Mk[(size_t)k * N + p2] = x; }
            }
            if (now() - last > 15) { last = now(); fprintf(stderr, "t=%.0f it=%ld acc=%ld T=%.3f cur=%ld best=%ld\n", now() - t0, it, acc, T, cur, best); }
        }
        build_adj();
        printf("RESULT q=%d m=%d (Z%d x Z%d) t=%d D=%d best=%ld it=%ld sources=%d out=%s\n", q, m, m1, m2, t, D, best, it, nsrc, out);
        return 0;
    }
    return 1;
}
