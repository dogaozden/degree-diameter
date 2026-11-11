/* vlift: annealing over voltages of a circulant bipartite base graph, lifted over a metacyclic group.
 *
 * Base graph (k + k vertices, degree DEG = 16): A_i ~ B_{(i+t) mod k} for t = 0..15 (multi-edges when k < 16).
 * Voltage x[i][t] in G = Z_m x|_r Z_n. Lift: vertices (u, g), u in 0..2k-1 (A: 0..k-1, B: k..2k-1), g in G;
 * edge (i, g) ~ (k + (i+t) mod k, g x[i][t]). Left multiplication by G is an automorphism, so
 * dist((u,g),(w,h)) = dist((u,e),(w,g^-1 h)) and only the 2k sources (u,e) need a BFS.
 *
 * Gauge: a spanning tree of the base gets voltage e (t = 0 for all i, and t = 1 for i < k-1; for k = 1 only t = 0).
 * Parallel base edges (same i and same target) must have distinct voltages, so the lift is simple.
 *
 * Cost = #(source u, lift vertex v) with dist((u,e), v) > DIAM, summed over the 2k sources. Cost 0 = valid.
 *
 * Usage: vlift k m n r iters seed T0 T1 outfile
 *   G = Z_m x|_r Z_n with element index a*n + j, (a1,j1)(a2,j2) = (a1 + r^j1 a2, j1 + j2); r^n = 1 mod m.
 *   Writes an edge list "N" then "u v" lines (apsp format) to outfile if cost reaches 0.
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>

#define DEG 16
#define DIAM 5
#define MAXU 64

static int k, m, n, r, G;
static int *pw, *ga, *gj;
static int x[MAXU / 2][DEG];      /* voltages of base edges (i, t) */
static int fixedv[MAXU / 2][DEG]; /* 1 if gauge-fixed to e */
static int *invt;
static uint64_t rs;

static uint64_t rnd(void) {
    rs += 0x9E3779B97F4A7C15ULL; uint64_t z = rs;
    z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ULL; z = (z ^ (z >> 27)) * 0x94D049BB133111EBULL;
    return z ^ (z >> 31);
}
static inline int mul(int g, int h) {
    int a = (ga[g] + pw[gj[g]] * ga[h]) % m;
    int j = gj[g] + gj[h]; if (j >= n) j -= n;
    return a * n + j;
}

static int nbT[MAXU][DEG], nbX[MAXU][DEG]; /* base adjacency: target base vertex, voltage (inverse on B side) */
static uint32_t *vis; static uint32_t stamp = 0;
static int *queue;

static void build_base(void) {
    int cnt[MAXU];
    memset(cnt, 0, sizeof cnt);
    for (int i = 0; i < k; i++) for (int t = 0; t < DEG; t++) {
        int j = (i + t) % k, a = i, b = k + j;
        nbT[a][cnt[a]] = b; nbX[a][cnt[a]++] = x[i][t];
        nbT[b][cnt[b]] = a; nbX[b][cnt[b]++] = invt[x[i][t]];
    }
}

static int64_t evalcost(void) {
    int64_t V = 2LL * k * G, cost = 0;
    build_base();
    for (int s = 0; s < 2 * k; s++) {
        stamp++;
        int head = 0, tail = 0;
        int src = s * G; vis[src] = stamp; queue[tail++] = src;
        int64_t reached = 1;
        for (int lev = 0; lev < DIAM && head < tail; lev++) {
            int end = tail;
            for (; head < end; head++) {
                int v = queue[head]; int u = v / G, g = v - u * G;
                for (int d = 0; d < DEG; d++) {
                    int w = nbT[u][d]; int nv = w * G + mul(g, nbX[u][d]);
                    if (vis[nv] != stamp) { vis[nv] = stamp; queue[tail++] = nv; }
                }
            }
            reached = tail;
        }
        cost += V - reached;
    }
    return cost;
}

/* free slots: all (i,t) except gauge-fixed ones; slots of the same pair (i,j) must keep distinct voltages */
static int slotsI[MAXU * DEG], slotsT[MAXU * DEG], nslots;

static int conflicts(int i, int t, int val) {
    int j = (i + t) % k;
    for (int t2 = 0; t2 < DEG; t2++) if (t2 != t && (i + t2) % k == j && x[i][t2] == val) return 1;
    return 0;
}

int main(int argc, char **argv) {
    if (argc < 10) { fprintf(stderr, "usage: vlift k m n r iters seed T0 T1 outfile\n"); return 2; }
    k = atoi(argv[1]); m = atoi(argv[2]); n = atoi(argv[3]); r = atoi(argv[4]);
    long iters = atol(argv[5]); rs = strtoull(argv[6], 0, 10) * 1000003ULL + 12345;
    double T0 = atof(argv[7]), T1 = atof(argv[8]); const char *outf = argv[9];
    G = m * n;
    if (k < 1 || 2 * k > MAXU) { fprintf(stderr, "bad k\n"); return 2; }
    pw = malloc(sizeof(int) * n); pw[0] = 1 % m;
    for (int j = 1; j < n; j++) pw[j] = (int)((long)pw[j - 1] * r % m);
    if ((long)pw[0] * 1 != 1 % m || (long)pw[n - 1] * r % m != 1 % m) { fprintf(stderr, "r^n != 1 mod m\n"); return 2; }
    ga = malloc(sizeof(int) * G); gj = malloc(sizeof(int) * G);
    for (int g = 0; g < G; g++) { ga[g] = g / n; gj[g] = g % n; }
    invt = malloc(sizeof(int) * G);
    for (int g = 0; g < G; g++) { /* (a,j)^-1 = (-r^(-j) a, -j) */
        int j1 = (n - gj[g]) % n, a1 = (m - (int)((long)pw[j1] * ga[g] % m)) % m;
        invt[g] = a1 * n + j1;
    }
    vis = calloc((size_t)2 * k * G, sizeof(uint32_t)); queue = malloc(sizeof(int) * 2 * k * G);

    /* gauge: spanning tree = {(i,0) all i} + {(i,1), i < k-1}; for k = 1 only (0,0) */
    memset(fixedv, 0, sizeof fixedv);
    for (int i = 0; i < k; i++) { fixedv[i][0] = 1; x[i][0] = 0; }
    if (k >= 2) for (int i = 0; i < k - 1; i++) { fixedv[i][1] = 1; x[i][1] = 0; }
    nslots = 0;
    for (int i = 0; i < k; i++) for (int t = 0; t < DEG; t++) if (!fixedv[i][t]) { slotsI[nslots] = i; slotsT[nslots] = t; nslots++; }
    /* random initial voltages, distinct within each pair */
    for (int q = 0; q < nslots; q++) {
        int i = slotsI[q], t = slotsT[q], val, tries = 0;
        do { val = (int)(rnd() % G); tries++; } while (conflicts(i, t, val) && tries < 100000);
        x[i][t] = val;
    }
    /* the fixed slots can clash with random ones only if the random value is e; re-check fixed-vs-free */
    {
        int bad = 0;
        for (int i = 0; i < k; i++) for (int t = 0; t < DEG; t++) if (conflicts(i, t, x[i][t])) bad = 1;
        if (bad) { fprintf(stderr, "initial assignment has conflicts (group too small for multiplicity)\n"); return 3; }
    }
    /* invt must be computed before first eval */
    int64_t cur = evalcost(), best = cur;
    int bx[MAXU / 2][DEG]; memcpy(bx, x, sizeof x);
    fprintf(stderr, "k=%d G=%d N=%d init cost=%lld\n", k, G, 2 * k * G, (long long)cur);
    for (long it = 0; it < iters && best > 0; it++) {
        double T = T0 * pow(T1 / T0, (double)it / iters);
        int q = rnd() % nslots; int i = slotsI[q], t = slotsT[q];
        int old = x[i][t]; int val = (int)(rnd() % G);
        if (val == old || conflicts(i, t, val)) continue;
        x[i][t] = val;
        int64_t c = evalcost();
        if (c <= cur || exp((double)(cur - c) / T) > (rnd() % 1000000) / 1e6) {
            cur = c;
            if (cur < best) { best = cur; memcpy(bx, x, sizeof x); }
        } else x[i][t] = old;
        if (it % 2000 == 0) fprintf(stderr, "it=%ld T=%.3f cur=%lld best=%lld\n", it, T, (long long)cur, (long long)best);
    }
    memcpy(x, bx, sizeof x);
    cur = evalcost();
    printf("k=%d m=%d n=%d r=%d G=%d N=%d cost=%lld\n", k, m, n, r, G, 2 * k * G, (long long)cur);
    if (cur == 0) {
        FILE *f = fopen(outf, "w");
        long N = 2L * k * G; long E = 0;
        fprintf(f, "%ld\n", N);
        for (int i = 0; i < k; i++) for (int t = 0; t < DEG; t++) {
            int j = (i + t) % k;
            for (int g = 0; g < G; g++) { fprintf(f, "%d %d\n", i * G + g, (k + j) * G + mul(g, x[i][t])); E++; }
        }
        fclose(f);
        printf("VALID wrote %s edges=%ld\n", outf, E);
        for (int i = 0; i < k; i++) { printf("x%d:", i); for (int t = 0; t < DEG; t++) printf(" %d", x[i][t]); printf("\n"); }
    }
    return 0;
}
