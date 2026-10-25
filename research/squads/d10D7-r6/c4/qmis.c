/* qmis.c (squad r6 c4): k-fixed style tabu (swap moves) for a maximum independent set in an orbit conflict graph.
   Same move rules as r4/c4 mis.c, but on a generic graph given in binary CSR form.
   usage: qmis GRAPH OUT SECONDS SEED INIT|- [TT_BASE] [STAG]
   GRAPH (written by build_quot.py): int32 n, s, m2; int32 indptr[n+1]; int32 indices[m2]; int32 members[n*s].
   Vertices = self-compatible orbits of s points; an edge joins two orbits that have collinear points.
   INIT: text list of vertex (orbit) ids to start from, or '-' for an empty start.
   OUT: point ids of the best independent set (members of its orbits), rewritten after every improvement. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

static int n, s, D, KB, W;
static int *indptr, *indices, *members;
static uint8_t *adjb;
static uint64_t rs;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline int rndn(int m) { return (int)(rnd() % (uint64_t)m); }
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }
static inline int adj(int u, int v) { return (adjb[(size_t)u * W + (v >> 3)] >> (v & 7)) & 1; }

static int *tight, *sol, *spos, nS, *head, *nxt, *prv, *bkey;
static char *inS;
static long long *tabu, iter, f;
static int TTB = 7;
static long long STAG = 200000;

static void load_graph(const char *fn) {
    FILE *fp = fopen(fn, "rb"); if (!fp) { perror(fn); exit(2); }
    int32_t h[3];
    if (fread(h, 4, 3, fp) != 3) exit(2);
    n = h[0]; s = h[1];
    int m2 = h[2];
    indptr = malloc(sizeof(int) * (size_t)(n + 1));
    indices = malloc(sizeof(int) * (size_t)(m2 > 0 ? m2 : 1));
    members = malloc(sizeof(int) * (size_t)n * s);
    if (fread(indptr, 4, (size_t)n + 1, fp) != (size_t)n + 1) exit(2);
    if (m2 && fread(indices, 4, (size_t)m2, fp) != (size_t)m2) exit(2);
    if (fread(members, 4, (size_t)n * s, fp) != (size_t)n * s) exit(2);
    fclose(fp);
    D = 0;
    for (int v = 0; v < n; v++) { int d = indptr[v + 1] - indptr[v]; if (d > D) D = d; }
    KB = D + 1;
    W = (n + 7) >> 3;
    adjb = calloc((size_t)n * W, 1);
    for (int v = 0; v < n; v++)
        for (int j = indptr[v]; j < indptr[v + 1]; j++) { int w = indices[j]; adjb[(size_t)v * W + (w >> 3)] |= (uint8_t)(1 << (w & 7)); }
    fprintf(stderr, "graph n=%d s=%d maxdeg=%d m2=%d\n", n, s, D, m2);
}

/* bucket lists over all vertices, key = inS*KB + tight */
static inline void bins(int v) {
    int k = inS[v] * KB + tight[v];
    bkey[v] = k; prv[v] = -1; nxt[v] = head[k];
    if (head[k] >= 0) prv[head[k]] = v;
    head[k] = v;
}
static inline void bdel(int v) {
    int k = bkey[v];
    if (prv[v] >= 0) nxt[prv[v]] = nxt[v]; else head[k] = nxt[v];
    if (nxt[v] >= 0) prv[nxt[v]] = prv[v];
}
static inline void bump(int w, int d) { bdel(w); tight[w] += d; bins(w); }

static void add_vertex(int v) {
    f += tight[v];
    bdel(v); inS[v] = 1; spos[v] = nS; sol[nS++] = v; bins(v);
    for (int j = indptr[v]; j < indptr[v + 1]; j++) bump(indices[j], +1);
}
static void remove_vertex(int u) {
    bdel(u); inS[u] = 0;
    int p = spos[u], last = sol[--nS]; sol[p] = last; spos[last] = p;
    f -= tight[u];
    bins(u);
    for (int j = indptr[u]; j < indptr[u + 1]; j++) bump(indices[j], -1);
}

static void rebuild(void) {
    for (int k = 0; k < 2 * KB; k++) head[k] = -1;
    nS = 0;
    for (int v = 0; v < n; v++) if (inS[v]) { spos[v] = nS; sol[nS++] = v; }
    for (int v = 0; v < n; v++) {
        int t = 0;
        for (int j = indptr[v]; j < indptr[v + 1]; j++) t += inS[indices[j]];
        tight[v] = t;
    }
    f = 0; for (int i = 0; i < nS; i++) f += tight[sol[i]];
    f /= 2;
    for (int v = 0; v < n; v++) bins(v);
}

/* u: solution vertex with most conflicts (non-tabu, random among the first 64 scanned) */
static int pick_u(void) {
    for (int t = D; t >= 0; t--) {
        int k = KB + t, cnt = 0, chosen = -1, m = 0;
        for (int x = head[k]; x >= 0 && cnt < 64; x = nxt[x], cnt++)
            if (tabu[x] <= iter) { m++; if (rndn(m) == 0) chosen = x; }
        if (chosen >= 0) return chosen;
    }
    return sol[rndn(nS)];
}

/* v: outside vertex minimising tight[v] - adj(u,v) (u removed first), non-tabu, random ties */
static int pick_v(int u) {
    int best = -1, bs = 1 << 30, nt = 0;
    for (int j = indptr[u]; j < indptr[u + 1]; j++) {
        int w = indices[j];
        if (inS[w] || tabu[w] > iter) continue;
        int sc = tight[w] - 1;
        if (sc < bs) { bs = sc; best = w; nt = 1; } else if (sc == bs && rndn(++nt) == 0) best = w;
    }
    for (int t = 0; t <= D; t++) {
        int cnt = 0, any = 0;
        for (int x = head[t]; x >= 0 && cnt < 32; x = nxt[x], cnt++) {
            if (tabu[x] > iter) continue;
            any = 1;
            int sc = tight[x] - adj(u, x);
            if (sc < bs) { bs = sc; best = x; nt = 1; } else if (sc == bs && rndn(++nt) == 0) best = x;
        }
        if (any) break;
    }
    if (best < 0) { do { best = rndn(n); } while (inS[best]); }
    return best;
}

static void add_min_out(void) {
    for (int t = 0; t <= D; t++) {
        int cnt = 0, chosen = -1, m = 0;
        for (int x = head[t]; x >= 0 && cnt < 64; x = nxt[x], cnt++) { m++; if (rndn(m) == 0) chosen = x; }
        if (chosen >= 0) { add_vertex(chosen); return; }
    }
}

static void perturb(int P) {
    for (int r = 0; r < P; r++) {
        int u = sol[rndn(nS)], v = -1, vt = 1 << 30;
        for (int k = 0; k < 20; k++) {
            int w = rndn(n);
            if (inS[w]) continue;
            if (tight[w] < vt) { vt = tight[w]; v = w; }
        }
        if (v < 0) continue;
        remove_vertex(u); add_vertex(v);
        tabu[u] = iter + 10; tabu[v] = iter + 10;
    }
}

static void save(const char *fn) {
    char tmp[1100]; snprintf(tmp, sizeof tmp, "%s.tmp", fn);
    FILE *o = fopen(tmp, "w"); if (!o) { perror(tmp); return; }
    for (int i = 0; i < nS; i++) {
        int v = sol[i];
        for (int k = 0; k < s; k++) fprintf(o, "%d\n", members[(size_t)v * s + k]);
    }
    fclose(o); rename(tmp, fn);
}

int main(int argc, char **argv) {
    if (argc < 6) { fprintf(stderr, "usage: qmis GRAPH OUT SECONDS SEED INIT|- [TT_BASE] [STAG]\n"); return 2; }
    load_graph(argv[1]);
    const char *out = argv[2];
    double secs = atof(argv[3]);
    uint64_t seed = strtoull(argv[4], 0, 10);
    rs = seed * 0x9E3779B97F4A7C15ULL + 0x1234567ULL; if (!rs) rs = 1;
    for (int i = 0; i < 20; i++) rnd();
    if (argc > 6) TTB = atoi(argv[6]);
    if (argc > 7) STAG = atoll(argv[7]);

    tight = calloc(n, sizeof(int)); sol = malloc(sizeof(int) * n); spos = malloc(sizeof(int) * n);
    head = malloc(sizeof(int) * 2 * KB); nxt = malloc(sizeof(int) * n); prv = malloc(sizeof(int) * n);
    bkey = malloc(sizeof(int) * n); inS = calloc(n, 1); tabu = calloc(n, sizeof(long long));
    if (strcmp(argv[5], "-")) {
        FILE *fi = fopen(argv[5], "r"); if (!fi) { perror(argv[5]); return 2; }
        int x; while (fscanf(fi, "%d", &x) == 1) if (x >= 0 && x < n) inS[x] = 1;
        fclose(fi);
    }
    rebuild();
    fprintf(stderr, "start %d orbits (%d points), conflicts %lld\n", nS, nS * s, f);
    double t0 = now();
    int bestSize = -1;
    if (f == 0) { bestSize = nS; save(out); add_min_out(); }
    long long lastImp = 0, fbest = f;
    iter = 0;
    while (1) {
        if (f == 0) {
            if (nS > bestSize) {
                bestSize = nS; save(out);
                fprintf(stderr, "size %d orbits = %d points, iter %lld t=%.1f\n", nS, nS * s, iter, now() - t0);
            }
            add_min_out(); fbest = f; lastImp = iter; continue;
        }
        if ((iter & 4095) == 0 && now() - t0 > secs) break;
        if ((iter & ((1 << 20) - 1)) == 0 && iter)
            fprintf(stderr, "  iter %lld t=%.0f size %d f %lld fbest %lld best %d\n", iter, now() - t0, nS, f, fbest, bestSize);
        iter++;
        int u = pick_u();
        int v = pick_v(u);
        remove_vertex(u);
        add_vertex(v);
        tabu[u] = iter + TTB + rndn(10);
        tabu[v] = iter + 1 + rndn(3);
        if (f < fbest) { fbest = f; lastImp = iter; }
        if (iter - lastImp > STAG) { perturb(2); fbest = f; lastImp = iter; }
    }
    long long chk = 0;
    for (int i = 0; i < nS; i++) for (int j = i + 1; j < nS; j++) if (adj(sol[i], sol[j])) chk++;
    fprintf(stderr, "end: best saved %d orbits (%d points), current %d orbits, conflicts %lld (check %lld), iters %lld\n",
            bestSize, bestSize * s, nS, f, chk, iter);
    return 0;
}
