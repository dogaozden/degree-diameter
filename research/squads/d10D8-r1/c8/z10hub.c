/* z10hub.c (squad d10D8-r1, card c8): the Z10 hexagon lift at q = 3 (Delta = 6, D = 8) plus hub vertices.

   Base graph: vertices (v,i), v a point or line of H(q), i in Z10 (7280 vertices at q = 3).
     (p,i) ~ (l,i)                  for p on l                  (hexagon edges, every level)
     (p,i) ~ (s1(p), i+1)           s1: points -> lines, random bijection
     (p,i) ~ (s2(p), i+4)           s2: points -> lines, random bijection
   Every vertex has degree q+3 = 6; the graph is bipartite with parts {points at all levels} and {lines at all levels}.

   Hubs are appended after the base vertices. A hub is put on the side opposite to all its neighbours, so the
   result stays bipartite (apsp.c only reports VALID for bipartite graphs).

   Violations: number of ordered pairs (s,t) with dist(s,t) > D (or unreachable), counted by a bit-parallel BFS
   from all sources (64 at a time). Violations = 0 means diameter <= D.

   Usage:  z10hub HEXBIN SEED MODE [K T DMIN DMAX OUT]
     MODE 0: base only. Prints violations at D = 8 and the exact diameter.
     MODE 1: free K random points (delete all 20 matching edges of each) and print violations. No hubs.
     MODE 2: free K random points, then greedy hub insertion for T proposals. A proposal is a hub on a random side
             whose degree is uniform in [DMIN, DMAX] and whose neighbours are random free slots on the other side.
             It is kept iff violations do not increase. If the final violations are 0, the edge list goes to OUT
             (format: "n" then "u v" lines, the input of research/lifts/coordinator_check/apsp.c). */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>

#define MAXD 6
#define MAXV 8000
#define LVL 10
#define DIAM 8

static int q, N, *LP;
static int nv;
static int adj[MAXV][MAXD], deg[MAXV], side[MAXV];
static int sig1[1000], sig2[1000];
static uint64_t vis[MAXV], fr[MAXV], nx[MAXV];
static int cand[MAXV];
static int freed_list[256], nfreed = 0;
static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndi(int n) { return (int)(rnd() % (uint64_t)n); }
/* base vertex ids: point (p,i) = i*2N + p, line (l,i) = i*2N + N + l */
static int VP(int p, int i) { return i * 2 * N + p; }
static int VL(int l, int i) { return i * 2 * N + N + l; }

static void load_hex(const char *fn) {
    FILE *f = fopen(fn, "rb");
    if (!f) { perror(fn); exit(1); }
    int32_t hdr[3];
    if (fread(hdr, 4, 3, f) != 3) exit(1);
    q = hdr[0]; N = hdr[1];
    if (hdr[2] != N) { fprintf(stderr, "points != lines\n"); exit(1); }
    LP = malloc(sizeof(int) * (size_t)N * (q + 1));
    int32_t *tmp = malloc(4 * (size_t)N * (q + 1));
    if (fread(tmp, 4, (size_t)N * (q + 1), f) != (size_t)N * (q + 1)) exit(1);
    for (size_t k = 0; k < (size_t)N * (q + 1); k++) LP[k] = tmp[k];
    free(tmp); fclose(f);
    int *cnt = calloc(N, sizeof(int));
    for (int l = 0; l < N; l++) for (int k = 0; k < q + 1; k++) cnt[LP[l * (q + 1) + k]]++;
    for (int p = 0; p < N; p++) if (cnt[p] != q + 1) { fprintf(stderr, "point %d on %d lines\n", p, cnt[p]); exit(1); }
    free(cnt);
}

static void add_edge(int a, int b) {
    if (a == b || deg[a] >= MAXD || deg[b] >= MAXD) { fprintf(stderr, "bad add_edge %d %d\n", a, b); exit(2); }
    adj[a][deg[a]++] = b;
    adj[b][deg[b]++] = a;
}

static void del_edge(int a, int b) {
    int ok = 0;
    for (int k = 0; k < deg[a] && !ok; k++) if (adj[a][k] == b) { adj[a][k] = adj[a][--deg[a]]; ok = 1; }
    for (int k = 0; k < deg[b] && !(ok & 2); k++) if (adj[b][k] == a) { adj[b][k] = adj[b][--deg[b]]; ok |= 2; }
    if (ok != 3) { fprintf(stderr, "missing edge %d %d\n", a, b); exit(2); }
}

static void perm(int *a) {
    for (int i = 0; i < N; i++) a[i] = i;
    for (int i = N - 1; i > 0; i--) { int j = rndi(i + 1), t = a[i]; a[i] = a[j]; a[j] = t; }
}

static void build_base(void) {
    nv = LVL * 2 * N;
    for (int v = 0; v < nv; v++) deg[v] = 0;
    for (int l = 0; l < N; l++) for (int k = 0; k < q + 1; k++) {
        int p = LP[l * (q + 1) + k];
        for (int i = 0; i < LVL; i++) add_edge(VP(p, i), VL(l, i));
    }
    for (int p = 0; p < N; p++) for (int i = 0; i < LVL; i++) {
        add_edge(VP(p, i), VL(sig1[p], (i + 1) % LVL));
        add_edge(VP(p, i), VL(sig2[p], (i + 4) % LVL));
    }
    for (int v = 0; v < nv; v++) side[v] = ((v % (2 * N)) >= N);   /* 0 = point side, 1 = line side */
}

/* delete the 20 matching edges of point p (two per level) */
static void free_point(int p) {
    for (int i = 0; i < LVL; i++) {
        del_edge(VP(p, i), VL(sig1[p], (i + 1) % LVL));
        del_edge(VP(p, i), VL(sig2[p], (i + 4) % LVL));
    }
    freed_list[nfreed++] = p;
}

static void free_random(int K) {
    for (int k = 0; k < K; k++) {
        int p, dup;
        do { p = rndi(N); dup = 0; for (int j = 0; j < nfreed; j++) if (freed_list[j] == p) dup = 1; } while (dup);
        free_point(p);
    }
}

/* hub on side s adjacent to nb[0..d-1] (all of side 1-s, with a free slot) */
static int add_hub(int s, const int *nb, int d) {
    int h = nv++;
    side[h] = s; deg[h] = 0;
    for (int t = 0; t < d; t++) add_edge(h, nb[t]);
    return h;
}

static void remove_last_hub(void) {
    int h = nv - 1;
    while (deg[h] > 0) del_edge(h, adj[h][0]);
    nv--;
}

/* ordered pairs at distance > D (or unreachable), bit-parallel BFS from all sources */
static long violations(int D) {
    long bad = 0;
    for (int s0 = 0; s0 < nv; s0 += 64) {
        int ns = (nv - s0 < 64) ? nv - s0 : 64;
        uint64_t full = (ns == 64) ? ~0ULL : ((1ULL << ns) - 1);
        for (int v = 0; v < nv; v++) { vis[v] = 0; fr[v] = 0; }
        for (int k = 0; k < ns; k++) { vis[s0 + k] |= 1ULL << k; fr[s0 + k] |= 1ULL << k; }
        for (int lev = 0; lev < D; lev++) {
            for (int v = 0; v < nv; v++) {
                uint64_t acc = 0;
                for (int t = 0; t < deg[v]; t++) acc |= fr[adj[v][t]];
                nx[v] = acc & ~vis[v];
            }
            for (int v = 0; v < nv; v++) { vis[v] |= nx[v]; fr[v] = nx[v]; }
        }
        for (int v = 0; v < nv; v++) bad += __builtin_popcountll(full & ~vis[v]);
    }
    return bad;
}

/* exact diameter, or -1 if disconnected */
static int exact_diam(void) {
    int diam = 0;
    for (int s0 = 0; s0 < nv; s0 += 64) {
        int ns = (nv - s0 < 64) ? nv - s0 : 64;
        uint64_t full = (ns == 64) ? ~0ULL : ((1ULL << ns) - 1);
        for (int v = 0; v < nv; v++) { vis[v] = 0; fr[v] = 0; }
        for (int k = 0; k < ns; k++) { vis[s0 + k] |= 1ULL << k; fr[s0 + k] |= 1ULL << k; }
        int lev = 0;
        for (;;) {
            int any = 0;
            for (int v = 0; v < nv; v++) {
                uint64_t acc = 0;
                for (int t = 0; t < deg[v]; t++) acc |= fr[adj[v][t]];
                nx[v] = acc & ~vis[v];
                if (nx[v]) any = 1;
            }
            if (!any) break;
            lev++;
            for (int v = 0; v < nv; v++) { vis[v] |= nx[v]; fr[v] = nx[v]; }
        }
        for (int v = 0; v < nv; v++) if ((vis[v] & full) != full) return -1;
        if (lev > diam) diam = lev;
    }
    return diam;
}

static long nedges(void) { long m = 0; for (int v = 0; v < nv; v++) m += deg[v]; return m / 2; }

static int maxdeg(void) { int m = 0; for (int v = 0; v < nv; v++) if (deg[v] > m) m = deg[v]; return m; }

static void dump(const char *fn) {
    FILE *f = fopen(fn, "w");
    if (!f) { perror(fn); exit(1); }
    fprintf(f, "%d\n", nv);
    for (int v = 0; v < nv; v++) for (int t = 0; t < deg[v]; t++) if (adj[v][t] > v) fprintf(f, "%d %d\n", v, adj[v][t]);
    fclose(f);
}

static int greedy(int T, int dmin, int dmax, long *Vout) {
    long V = violations(DIAM);
    int hubs = 0, acc_count = 0;
    for (int t = 0; t < T; t++) {
        int s = rndi(2);                       /* side of the new hub */
        int nc = 0;
        for (int v = 0; v < nv; v++) if (side[v] == 1 - s && deg[v] < MAXD) cand[nc++] = v;
        if (nc == 0) continue;
        int d = dmin + rndi(dmax - dmin + 1);
        if (d > nc) d = nc;
        if (d < 1) continue;
        int nb[MAXD];
        for (int a = 0; a < d; a++) { int j = a + rndi(nc - a), tmp = cand[a]; cand[a] = cand[j]; cand[j] = tmp; nb[a] = cand[a]; }
        add_hub(s, nb, d);
        long V2 = violations(DIAM);
        if (V2 <= V) { V = V2; hubs++; acc_count++; }
        else remove_last_hub();
        if (acc_count > 0 && (t % 200) == 0) fprintf(stderr, "  t=%d hubs=%d V=%ld nv=%d\n", t, hubs, V, nv);
    }
    *Vout = V;
    return hubs;
}

int main(int argc, char **argv) {
    if (argc < 4) { fprintf(stderr, "usage: z10hub HEXBIN SEED MODE [K T DMIN DMAX OUT]\n"); return 1; }
    load_hex(argv[1]);
    rs ^= (uint64_t)strtoull(argv[2], 0, 10) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int r = 0; r < 20; r++) rnd();
    int mode = atoi(argv[3]);
    int K = argc > 4 ? atoi(argv[4]) : 1;
    int T = argc > 5 ? atoi(argv[5]) : 0;
    int DMIN = argc > 6 ? atoi(argv[6]) : 1;
    int DMAX = argc > 7 ? atoi(argv[7]) : 6;
    const char *out = argc > 8 ? argv[8] : NULL;
    clock_t t0 = clock();

    perm(sig1); perm(sig2);
    build_base();
    printf("base: q=%d N=%d n=%d edges=%ld maxdeg=%d\n", q, N, nv, nedges(), maxdeg());
    if (mode == 0) {
        printf("base violations(D=8)=%ld exact_diam=%d\n", violations(DIAM), exact_diam());
        if (out) dump(out);
        return 0;
    }
    free_random(K);
    long V = violations(DIAM);
    printf("freed %d point(s) [", nfreed);
    for (int j = 0; j < nfreed; j++) printf(" %d", freed_list[j]);
    printf(" ] no hubs: violations(D=8)=%ld\n", V);
    if (mode == 1) return 0;
    long Vf = V;
    int hubs = greedy(T, DMIN, DMAX, &V);
    printf("greedy: hubs=%d violations(D=8)=%ld (before hubs %ld) n=%d maxdeg=%d edges=%ld time=%.1fs\n",
           hubs, V, Vf, nv, maxdeg(), nedges(), (double)(clock() - t0) / CLOCKS_PER_SEC);
    if (V == 0) {
        printf("exact_diam=%d\n", exact_diam());
        if (out) { dump(out); printf("wrote %s\n", out); }
    }
    return 0;
}
