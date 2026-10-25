/* c4 (squad r4, d10D7): largest set of points of H(9) with no two on a common line.
   = maximum independent set of the collinearity graph (degree 90, N = 66430).
   Method: min-degree greedy start, then k-fixed tabu search (swap moves, cost = number of
   collinear pairs inside the set; k grows by one each time the cost reaches 0).
   usage: mis HEXBIN OUT SECONDS SEED [INIT|-] [TT_BASE] [STAG]
   OUT is rewritten (plain ids, one per line) after every improvement. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

static int q, N, Q1, D;
static int32_t *LP, *PL, *NB;
static uint64_t rs;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline int rndn(int n) { return (int)(rnd() % (uint64_t)n); }
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }

static void load(const char *fn) {
    FILE *f = fopen(fn, "rb");
    if (!f) { perror(fn); exit(2); }
    int32_t h[3];
    if (fread(h, 4, 3, f) != 3) exit(2);
    q = h[0]; N = h[1]; Q1 = q + 1; D = q * (q + 1);
    LP = malloc(sizeof(int32_t) * (size_t)N * Q1);
    if (fread(LP, 4, (size_t)N * Q1, f) != (size_t)N * Q1) { fprintf(stderr, "short read\n"); exit(2); }
    fclose(f);
    PL = malloc(sizeof(int32_t) * (size_t)N * Q1);
    int *c = calloc(N, sizeof(int));
    for (int l = 0; l < N; l++) for (int k = 0; k < Q1; k++) {
        int p = LP[(size_t)l * Q1 + k];
        if (c[p] >= Q1) { fprintf(stderr, "point %d on too many lines\n", p); exit(2); }
        PL[(size_t)p * Q1 + c[p]++] = l;          /* lines through p, ascending */
    }
    NB = malloc(sizeof(int32_t) * (size_t)N * D);
    for (int p = 0; p < N; p++) {
        int idx = 0;
        for (int k = 0; k < Q1; k++) {
            int l = PL[(size_t)p * Q1 + k];
            for (int m = 0; m < Q1; m++) { int x = LP[(size_t)l * Q1 + m]; if (x != p) NB[(size_t)p * D + idx++] = x; }
        }
        if (idx != D) { fprintf(stderr, "degree mismatch at %d\n", p); exit(2); }
    }
    free(c);
}

/* collinear iff they share a line (PL lists are sorted) */
static inline int adjacent(int u, int v) {
    const int32_t *a = PL + (size_t)u * Q1, *b = PL + (size_t)v * Q1;
    int i = 0, j = 0;
    while (i < Q1 && j < Q1) { if (a[i] == b[j]) return 1; if (a[i] < b[j]) i++; else j++; }
    return 0;
}

/* ---- search state ---- */
static int *tight, *sol, *spos, nS, *head, *nxt, *prv, *bkey;
static char *inS;
static long long *tabu, iter, f;

/* bucket lists over all vertices, key = inS*(D+1) + tight */
static inline void bins(int v) {
    int k = inS[v] * (D + 1) + tight[v];
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
    const int32_t *nb = NB + (size_t)v * D;
    for (int j = 0; j < D; j++) bump(nb[j], +1);
}
static void remove_vertex(int u) {
    bdel(u); inS[u] = 0;
    int p = spos[u], last = sol[--nS]; sol[p] = last; spos[last] = p;
    f -= tight[u];
    bins(u);
    const int32_t *nb = NB + (size_t)u * D;
    for (int j = 0; j < D; j++) bump(nb[j], -1);
}

static void rebuild(void) {
    for (int k = 0; k < 2 * (D + 1); k++) head[k] = -1;
    nS = 0;
    for (int v = 0; v < N; v++) if (inS[v]) { spos[v] = nS; sol[nS++] = v; }
    for (int v = 0; v < N; v++) {
        int t = 0; const int32_t *nb = NB + (size_t)v * D;
        for (int j = 0; j < D; j++) t += inS[nb[j]];
        tight[v] = t;
    }
    f = 0; for (int i = 0; i < nS; i++) f += tight[sol[i]];
    f /= 2;
    for (int v = 0; v < N; v++) bins(v);
}

/* min-degree greedy (dynamic degrees) with random tie-breaking */
static int *gdeg, *gh, *gn, *gp, *gk; static char *galive;
static void gins(int v) { int k = gdeg[v]; gk[v] = k; gp[v] = -1; gn[v] = gh[k]; if (gh[k] >= 0) gp[gh[k]] = v; gh[k] = v; }
static void gdel(int v) { int k = gk[v]; if (gp[v] >= 0) gn[gp[v]] = gn[v]; else gh[k] = gn[v]; if (gn[v] >= 0) gp[gn[v]] = gp[v]; }
static void greedy(void) {
    gdeg = malloc(sizeof(int) * N); gh = malloc(sizeof(int) * (D + 1)); gn = malloc(sizeof(int) * N);
    gp = malloc(sizeof(int) * N); gk = malloc(sizeof(int) * N); galive = malloc(N);
    int *perm = malloc(sizeof(int) * N);
    for (int k = 0; k <= D; k++) gh[k] = -1;
    for (int i = 0; i < N; i++) perm[i] = i;
    for (int i = N - 1; i > 0; i--) { int j = rndn(i + 1); int t = perm[i]; perm[i] = perm[j]; perm[j] = t; }
    for (int i = 0; i < N; i++) { int v = perm[i]; gdeg[v] = D; galive[v] = 1; }
    for (int i = 0; i < N; i++) gins(perm[i]);
    int minb = 0, remaining = N;
    while (remaining > 0) {
        while (gh[minb] < 0) minb++;
        int v = gh[minb];
        gdel(v); galive[v] = 0; remaining--; inS[v] = 1;
        const int32_t *nb = NB + (size_t)v * D;
        for (int j = 0; j < D; j++) {
            int w = nb[j];
            if (!galive[w]) continue;
            gdel(w); galive[w] = 0; remaining--;
            const int32_t *nw = NB + (size_t)w * D;
            for (int i = 0; i < D; i++) {
                int x = nw[i];
                if (!galive[x]) continue;
                gdel(x); gdeg[x]--; gins(x);
                if (gdeg[x] < minb) minb = gdeg[x];
            }
        }
    }
    free(perm); free(gdeg); free(gh); free(gn); free(gp); free(gk); free(galive);
}

static void load_init(const char *fn) {
    FILE *f = fopen(fn, "r"); if (!f) { perror(fn); exit(2); }
    int x;
    while (fscanf(f, "%d", &x) == 1) if (x >= 0 && x < N) inS[x] = 1;
    fclose(f);
}

static void save(const char *fn) {
    char tmp[1024]; snprintf(tmp, sizeof tmp, "%s.tmp", fn);
    FILE *o = fopen(tmp, "w"); if (!o) { perror(tmp); return; }
    for (int i = 0; i < nS; i++) fprintf(o, "%d\n", sol[i]);
    fclose(o); rename(tmp, fn);
}

static int TTB = 7; static long long STAG = 1000000;

/* u: a solution vertex with most conflicts (non-tabu, random among scanned) */
static int pick_u(void) {
    for (int t = D; t >= 0; t--) {
        int k = (D + 1) + t, cnt = 0, chosen = -1, m = 0;
        for (int x = head[k]; x >= 0 && cnt < 64; x = nxt[x], cnt++)
            if (tabu[x] <= iter) { m++; if (rndn(m) == 0) chosen = x; }
        if (chosen >= 0) return chosen;
    }
    return sol[rndn(nS)];
}

/* v: outside vertex minimising tight[v] - adjacent(u,v) (removing u first), non-tabu, random ties */
static int pick_v(int u) {
    int best = -1, bs = 1 << 30, nt = 0;
    const int32_t *nb = NB + (size_t)u * D;
    for (int j = 0; j < D; j++) {
        int w = nb[j];
        if (inS[w] || tabu[w] > iter) continue;
        int s = tight[w] - 1;
        if (s < bs) { bs = s; best = w; nt = 1; } else if (s == bs && rndn(++nt) == 0) best = w;
    }
    for (int t = 0; t <= D; t++) {          /* lowest non-empty outside bucket with a non-tabu member */
        int cnt = 0, any = 0;
        for (int x = head[t]; x >= 0 && cnt < 32; x = nxt[x], cnt++) {
            if (tabu[x] > iter) continue;
            any = 1;
            int s = tight[x] - adjacent(u, x);
            if (s < bs) { bs = s; best = x; nt = 1; } else if (s == bs && rndn(++nt) == 0) best = x;
        }
        if (any) break;
    }
    if (best < 0) { do { best = rndn(N); } while (inS[best]); }
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
        for (int s = 0; s < 20; s++) {          /* light outside vertex: best of 20 random samples */
            int w = rndn(N);
            if (inS[w]) continue;
            if (tight[w] < vt) { vt = tight[w]; v = w; }
        }
        if (v < 0) continue;
        remove_vertex(u); add_vertex(v);
        tabu[u] = iter + 10; tabu[v] = iter + 10;
    }
}

int main(int argc, char **argv) {
    if (argc < 5) { fprintf(stderr, "usage: mis HEXBIN OUT SECONDS SEED [INIT|-] [TT_BASE] [STAG]\n"); return 2; }
    load(argv[1]);
    const char *out = argv[2];
    double secs = atof(argv[3]);
    uint64_t seed = strtoull(argv[4], 0, 10);
    rs = seed * 0x9E3779B97F4A7C15ULL + 0x1234567ULL; if (!rs) rs = 1;
    for (int i = 0; i < 20; i++) rnd();
    if (argc > 6) TTB = atoi(argv[6]);
    if (argc > 7) STAG = atoll(argv[7]);

    tight = calloc(N, sizeof(int)); sol = malloc(sizeof(int) * N); spos = malloc(sizeof(int) * N);
    head = malloc(sizeof(int) * 2 * (D + 1)); nxt = malloc(sizeof(int) * N); prv = malloc(sizeof(int) * N);
    bkey = malloc(sizeof(int) * N); inS = calloc(N, 1); tabu = calloc(N, sizeof(long long));
    if (argc > 5 && strcmp(argv[5], "-")) load_init(argv[5]); else greedy();
    rebuild();
    fprintf(stderr, "start size %d conflicts %lld\n", nS, f);
    double t0 = now();
    int bestSize = -1;
    if (f == 0) { bestSize = nS; save(out); add_min_out(); }
    long long lastImp = 0, fbest = f;
    iter = 0;
    while (1) {
        if (f == 0) {
            if (nS > bestSize) { bestSize = nS; save(out); fprintf(stderr, "size %d iter %lld t=%.1f\n", nS, iter, now() - t0); }
            add_min_out(); fbest = f; lastImp = iter; continue;
        }
        if ((iter & 4095) == 0 && now() - t0 > secs) break;
        if ((iter & ((1 << 20) - 1)) == 0 && iter) fprintf(stderr, "  iter %lld t=%.0f size %d f %lld fbest %lld\n", iter, now() - t0, nS, f, fbest);
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
    /* verify */
    long long chk = 0;
    for (int i = 0; i < nS; i++) for (int j = i + 1; j < nS; j++) if (adjacent(sol[i], sol[j])) chk++;
    fprintf(stderr, "end: best saved %d, current size %d, conflicts %lld (check %lld)\n", bestSize, nS, f, chk);
    return 0;
}
