/* ga.c: simulated annealing on a whole bipartite graph by degree-preserving 2-switches, cost = number of ordered
 * vertex pairs at distance > D (bit-parallel BFS, 64 sources at a time). Used for surgery: start from a record graph
 * with a few vertices added (degrees <= Delta), and repair the diameter.
 *
 * usage: ga EDGES     (first line n, then "u v" lines; the 2-colouring is computed)
 * env: D (5), DELTA (max degree, for the add-edge move), SECS (60), SEED (1), T0 (2), T1 (0.05), ITERS (1e6 per run),
 *      FOCUS (probability that one switched edge touches a vertex with a far pair, 0.7), OUT (edge list of the best),
 *      ADD (probability of an add-edge move between two deficient vertices of opposite colour, 0.05)
 * Output: "RESULT best <far pairs> n <n> ..." and OUT when best improves; DIAMETER_OK when 0.
 */
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 8192
#define MAXD 24
static int n, D = 5, DELTA = 64;
static int deg[MAXN], adj[MAXN][MAXD], col[MAXN];
static uint64_t *vis, *fr, *nx;
static long farcnt[MAXN];
static uint64_t rs = 88172645463325252ULL;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }

static int has(int u, int v) { for (int i = 0; i < deg[u]; i++) if (adj[u][i] == v) return 1; return 0; }
static void del1(int u, int v) { for (int i = 0; i < deg[u]; i++) if (adj[u][i] == v) { adj[u][i] = adj[u][--deg[u]]; return; } }
static void addE(int u, int v) { adj[u][deg[u]++] = v; adj[v][deg[v]++] = u; }
static void delE(int u, int v) { del1(u, v); del1(v, u); }

/* far pairs; if rec, fill farcnt[] (per vertex). abort when > limit */
static long cost(long limit, int rec) {
    long c = 0;
    if (rec) memset(farcnt, 0, sizeof(long) * n);
    for (int s0 = 0; s0 < n; s0 += 64) {
        int ns = n - s0 < 64 ? n - s0 : 64;
        memset(vis, 0, 8 * n); memset(fr, 0, 8 * n);
        for (int k = 0; k < ns; k++) vis[s0 + k] = fr[s0 + k] = 1ULL << k;
        for (int lev = 0; lev < D; lev++) {
            for (int x = 0; x < n; x++) { uint64_t a = 0; for (int i = 0; i < deg[x]; i++) a |= fr[adj[x][i]]; nx[x] = a & ~vis[x]; }
            for (int x = 0; x < n; x++) vis[x] |= nx[x];
            uint64_t *t = fr; fr = nx; nx = t;
        }
        uint64_t full = ns == 64 ? ~0ULL : ((1ULL << ns) - 1);
        for (int x = 0; x < n; x++) { uint64_t miss = full & ~vis[x]; if (miss) { int k = __builtin_popcountll(miss); c += k;
            if (rec) { farcnt[x] += k; for (uint64_t mm = miss; mm; mm &= mm - 1) farcnt[s0 + __builtin_ctzll(mm)]++; } } }
        if (c > limit) return c;
    }
    return c;
}

static void write_edges(const char *path) {
    if (!path) return;
    char tmp[1024]; snprintf(tmp, sizeof tmp, "%s.tmp", path);
    FILE *f = fopen(tmp, "w"); fprintf(f, "%d\n", n);
    for (int u = 0; u < n; u++) for (int i = 0; i < deg[u]; i++) if (adj[u][i] > u) fprintf(f, "%d %d\n", u, adj[u][i]);
    fclose(f); rename(tmp, path);
}

int main(int argc, char **argv) {
    if (argc < 2) return 2;
    if (getenv("D")) D = atoi(getenv("D"));
    if (getenv("DELTA")) DELTA = atoi(getenv("DELTA"));
    double SECS = getenv("SECS") ? atof(getenv("SECS")) : 60, T0 = getenv("T0") ? atof(getenv("T0")) : 2,
           T1 = getenv("T1") ? atof(getenv("T1")) : 0.05, FOCUS = getenv("FOCUS") ? atof(getenv("FOCUS")) : 0.7,
           ADD = getenv("ADD") ? atof(getenv("ADD")) : 0.05;
    long ITERS = getenv("ITERS") ? atol(getenv("ITERS")) : 1000000;
    rs ^= getenv("SEED") ? (uint64_t)atoll(getenv("SEED")) * 0x9E3779B97F4A7C15ULL : 0; for (int i = 0; i < 20; i++) rnd();
    const char *OUT = getenv("OUT");
    FILE *f = fopen(argv[1], "r"); if (!f || fscanf(f, "%d", &n) != 1 || n > MAXN) return 2;
    int a, b;
    while (fscanf(f, "%d %d", &a, &b) == 2) { if (a == b || has(a, b)) continue; if (deg[a] >= MAXD || deg[b] >= MAXD) return 3; addE(a, b); }
    fclose(f);
    for (int i = 0; i < n; i++) col[i] = -1;
    for (int s = 0; s < n; s++) if (col[s] < 0) { col[s] = 0; int q[MAXN], h = 0, t = 0; q[t++] = s;
        while (h < t) { int x = q[h++]; for (int i = 0; i < deg[x]; i++) { int y = adj[x][i]; if (col[y] < 0) { col[y] = 1 - col[x]; q[t++] = y; }
            else if (col[y] == col[x]) { fprintf(stderr, "not bipartite\n"); return 4; } } } }
    vis = malloc(8 * n); fr = malloc(8 * n); nx = malloc(8 * n);
    long cur = cost(1L << 60, 1), best = cur;
    fprintf(stderr, "start far pairs %ld\n", cur);
    write_edges(OUT);
    double t0 = now(), tend = t0 + SECS; long it = 0;
    int *hot = malloc(sizeof(int) * n), nhot = 0;
    for (int run = 0; best > 0 && now() < tend; run++) {
        for (long k = 0; k < ITERS && best > 0; k++) {
            if ((k & 63) == 0) { if (now() > tend) break;
                cost(1L << 60, 1); nhot = 0; for (int x = 0; x < n; x++) if (farcnt[x]) hot[nhot++] = x; }
            double T = T0 * pow(T1 / T0, (double)k / ITERS);
            double r = rnd01(); if (r < 1e-300) r = 1e-300;
            long limit = cur + (long)floor(-T * log(r));
            if (ADD > 0 && rnd01() < ADD) {   /* add an edge between deficient vertices */
                int u = rnd() % n, v = rnd() % n;
                if (col[u] == col[v] || deg[u] >= DELTA || deg[v] >= DELTA || has(u, v)) continue;
                addE(u, v); long c = cost(limit, 0); if (c <= limit) cur = c; else delE(u, v);
            } else {
                int x = (nhot > 0 && rnd01() < FOCUS) ? hot[rnd() % nhot] : (int)(rnd() % n);
                if (deg[x] == 0) continue;
                int y = adj[x][rnd() % deg[x]];
                int u = rnd() % n; if (deg[u] == 0 || col[u] != col[x] || u == x) continue;
                int v = adj[u][rnd() % deg[u]];
                if (v == y || has(x, v) || has(u, y)) continue;
                delE(x, y); delE(u, v); addE(x, v); addE(u, y);
                long c = cost(limit, 0);
                if (c <= limit) cur = c; else { delE(x, v); delE(u, y); addE(x, y); addE(u, v); }
            }
            it++;
            if (cur < best) { best = cur; write_edges(OUT); fprintf(stderr, "  t=%.1f it %ld best %ld\n", now() - t0, it, best); }
        }
    }
    int maxd = 0; for (int x = 0; x < n; x++) if (deg[x] > maxd) maxd = deg[x];
    printf("RESULT best %ld n %d maxdeg %d iters %ld secs %.1f%s\n", best, n, maxd, it, now() - t0, best == 0 ? " DIAMETER_OK" : "");
    return 0;
}
