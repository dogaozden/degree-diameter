// e16: add ONE new vertex w to a bipartite graph G (diameter 5, max degree 17).
// w joins a set N (|N| = k) of spare-slot vertices (degree <= 16) on side T (color T).
// Since G is bipartite, the new vertex w has ecc <= 5 iff every vertex x of G has dist(N, x) <= 4
// (for opposite-side x this is dist <= 3, for same-side x dist <= 4). Adding w only shortens
// distances, so G + w keeps diameter 5 and the new max degree is <= 17.
// Usage: addv IN.edges T k iters seed OUT.edges
//   T: colour class (0 or 1; colour 0 = side of vertex 0) that N must lie in.
// Simulated annealing on cost = #vertices x with dist(N,x) > 4. Writes OUT.edges only if cost 0.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

static int n, m;
static int *eu, *ev;
static int *deg, *adj;   // adj[v*18 + j]
static int *col;
static int *vis, stamp = 0, *q;
static uint64_t rs_state = 88172645463325252ULL;
static uint64_t rnd(void) { rs_state ^= rs_state << 13; rs_state ^= rs_state >> 7; rs_state ^= rs_state << 17; return rs_state; }

static void build(void) {
    deg = calloc(n, sizeof(int));
    adj = malloc((size_t)n * 18 * sizeof(int));
    for (int i = 0; i < m; i++) {
        int u = eu[i], v = ev[i];
        adj[u * 18 + deg[u]++] = v;
        adj[v * 18 + deg[v]++] = u;
    }
    col = malloc(n * sizeof(int));
    for (int i = 0; i < n; i++) col[i] = -1;
    q = malloc(n * sizeof(int));
    int h = 0, t = 0;
    col[0] = 0; q[t++] = 0;
    while (h < t) {
        int u = q[h++];
        for (int j = 0; j < deg[u]; j++) {
            int v = adj[u * 18 + j];
            if (col[v] < 0) { col[v] = 1 - col[u]; q[t++] = v; }
        }
    }
    vis = calloc(n, sizeof(int));
}

// BFS from src to depth 4, set bits of reached vertices (distance <= 4).
static void ball4(int src, uint64_t *bits) {
    stamp++;
    int h = 0, t = 0, dep_end = 1, d = 0;
    q[t++] = src; vis[src] = stamp;
    int level_end = t;
    while (h < t && d < 4) {
        while (h < level_end) {
            int u = q[h++];
            for (int j = 0; j < deg[u]; j++) {
                int v = adj[u * 18 + j];
                if (vis[v] != stamp) { vis[v] = stamp; q[t++] = v; }
            }
        }
        level_end = t; d++;
    }
    (void)dep_end;
    for (int i = 0; i < t; i++) { int x = q[i]; bits[x >> 6] |= 1ULL << (x & 63); }
}

static int W;
static int P;
static int *pool;          // vertex ids
static uint64_t *balls;    // P * W words
static int *cnt;
static int cost;

static void apply_ball(int idx, int sgn) {
    uint64_t *b = balls + (size_t)idx * W;
    for (int j = 0; j < W; j++) {
        uint64_t bits = b[j];
        while (bits) {
            int x = (j << 6) | __builtin_ctzll(bits);
            bits &= bits - 1;
            if (sgn > 0) { if (cnt[x] == 0) cost--; cnt[x]++; }
            else { cnt[x]--; if (cnt[x] == 0) cost++; }
        }
    }
}

int main(int argc, char **argv) {
    if (argc < 7) { fprintf(stderr, "usage: addv IN.edges T k iters seed OUT.edges\n"); return 1; }
    FILE *f = fopen(argv[1], "r");
    if (!f) return 1;
    int T = atoi(argv[2]), k = atoi(argv[3]);
    long iters = atol(argv[4]);
    rs_state ^= (uint64_t)atoll(argv[5]) * 0x9E3779B97F4A7C15ULL; if (!rs_state) rs_state = 1;
    const char *outp = argv[6];
    if (fscanf(f, "%d", &n) != 1) return 1;
    int cap = 1 << 16; eu = malloc(cap * sizeof(int)); ev = malloc(cap * sizeof(int)); m = 0;
    int a, b;
    while (fscanf(f, "%d %d", &a, &b) == 2) {
        if (m == cap) { cap *= 2; eu = realloc(eu, cap * sizeof(int)); ev = realloc(ev, cap * sizeof(int)); }
        eu[m] = a; ev[m] = b; m++;
    }
    fclose(f);
    build();
    W = (n + 63) / 64;
    // pool: side T, degree <= 16
    pool = malloc(n * sizeof(int)); P = 0;
    for (int v = 0; v < n; v++) if (col[v] == T && deg[v] <= 16) pool[P++] = v;
    fprintf(stderr, "n=%d m=%d pool=%d (side %d, spare slots) k=%d\n", n, m, P, T, k);
    if (P < k) { fprintf(stderr, "pool too small\n"); return 2; }
    balls = calloc((size_t)P * W, sizeof(uint64_t));
    for (int p = 0; p < P; p++) ball4(pool[p], balls + (size_t)p * W);
    cnt = calloc(n, sizeof(int));
    cost = n;  // all uncovered initially
    // initial random N
    int *N = malloc(k * sizeof(int));
    char *inN = calloc(P, 1);
    for (int i = 0; i < k; i++) {
        int c;
        do { c = rnd() % P; } while (inN[c]);
        inN[c] = 1; N[i] = c;
        apply_ball(c, +1);
    }
    int best = cost;
    int *bestN = malloc(k * sizeof(int)); memcpy(bestN, N, k * sizeof(int));
    clock_t t0 = clock();
    double tlim = getenv("TLIM") ? atof(getenv("TLIM")) : 80.0;
    double T0 = 1.5, T1 = 0.02;
    for (long it = 0; it < iters && cost > 0; it++) {
        double temp = T0 * pow(T1 / T0, (double)it / iters);
        int i = rnd() % k;
        int c = rnd() % P;
        if (inN[c]) continue;
        int old = N[i];
        int c0 = cost;
        apply_ball(old, -1);
        apply_ball(c, +1);
        int delta = cost - c0;
        double u = (rnd() >> 11) * (1.0 / 9007199254740992.0);
        if (delta <= 0 || u < exp(-delta / temp)) {
            N[i] = c; inN[old] = 0; inN[c] = 1;
            if (cost < best) { best = cost; memcpy(bestN, N, k * sizeof(int)); }
        } else {
            apply_ball(c, -1);
            apply_ball(old, +1);
        }
        if ((it & 0x3ffff) == 0) fprintf(stderr, "it=%ld cost=%d best=%d T=%.3f t=%.1fs\n", it, cost, best, temp,
                                         (double)(clock() - t0) / CLOCKS_PER_SEC);
        if ((double)(clock() - t0) / CLOCKS_PER_SEC > tlim) { fprintf(stderr, "time stop\n"); break; }
    }
    printf("best_cost=%d k=%d P=%d\n", best, k, P);
    if (best == 0) {
        FILE *g = fopen(outp, "w");
        fprintf(g, "%d\n", n + 1);
        for (int i = 0; i < m; i++) fprintf(g, "%d %d\n", eu[i], ev[i]);
        for (int i = 0; i < k; i++) fprintf(g, "%d %d\n", n, pool[bestN[i]]);
        fclose(g);
        printf("WROTE %s new vertex %d\n", outp, n);
    }
    return 0;
}
