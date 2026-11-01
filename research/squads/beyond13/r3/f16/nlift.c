// nlift: simulated-annealing voltage lifts of a small base graph over a finite group.
// Group: metacyclic Z_m x|_r Z_k (element id = i*k + j, (i,j)(i2,j2) = (i + r^j i2 mod m, j+j2 mod k)); r=1 gives cyclic Z_mk
// only if the product is cyclic (use m=n,k=1,r=1 for cyclic Z_n).
// Lift: vertex (v,g); base edge (x,y) with voltage a gives lift edges (x,g)-(y,g*a) for all g.
// Left multiplication by h is an automorphism, so BFS from (v,e) for each base vertex v suffices.
// Cost = sum over base vertices v of #{lift vertices at distance > D from (v,e)}.
// Usage: nlift BASE m k r D seconds seed OUTPREFIX [T0 T1] ; env START=<OUTPREFIX.volt-like file> (ne voltage ids)
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <math.h>
#include <stdint.h>

static uint64_t rs;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }

static int nv, ne, n;
static int eu[1024], ev[1024];
static int *mul, *inv_;            // n x n multiplication table, inverses
static int volt[1024];            // voltage id per base edge
static int tree[1024];            // 1 if tree edge (fixed identity)
static int hdeg[256];
static int hw[256][8], he[256][8], hd[256][8]; // half-edges at base vertex: target, edge, dir (0: volt, 1: inverse volt)
static int D;

static int pw_mod(int b, int e, int m) { long r = 1 % m, x = b % m; while (e) { if (e & 1) r = r * x % m; x = x * x % m; e >>= 1; } return (int)r; }

static void build_group(int m, int k, int r) {
    n = m * k;
    mul = malloc(sizeof(int) * (size_t)n * n);
    inv_ = malloc(sizeof(int) * n);
    int *rp = malloc(sizeof(int) * k);
    for (int j = 0; j < k; j++) rp[j] = pw_mod(r, j, m);
    for (int a = 0; a < n; a++) for (int b = 0; b < n; b++) {
        int i1 = a / k, j1 = a % k, i2 = b / k, j2 = b % k;
        int i = (int)((i1 + (long)rp[j1] * i2) % m), j = (j1 + j2) % k;
        mul[(size_t)a * n + b] = i * k + j;
    }
    for (int a = 0; a < n; a++) for (int b = 0; b < n; b++) if (mul[(size_t)a * n + b] == 0) inv_[a] = b;
    // sanity: associativity on random triples
    for (int t = 0; t < 2000; t++) {
        int a = rand() % n, b = rand() % n, c = rand() % n;
        if (mul[(size_t)mul[(size_t)a * n + b] * n + c] != mul[(size_t)a * n + mul[(size_t)b * n + c]]) { fprintf(stderr, "not a group\n"); exit(2); }
    }
    free(rp);
}

static void read_base(const char *fn) {
    FILE *f = fopen(fn, "r");
    if (!f) { perror(fn); exit(1); }
    if (fscanf(f, "%d", &nv) != 1) exit(1);
    ne = 0;
    while (fscanf(f, "%d %d", &eu[ne], &ev[ne]) == 2) ne++;
    fclose(f);
    // spanning tree by BFS from 0: tree edges get identity voltage
    int *seen = calloc(nv, sizeof(int)); int *q = malloc(sizeof(int) * nv); int qh = 0, qt = 0;
    seen[0] = 1; q[qt++] = 0;
    memset(tree, 0, sizeof tree);
    while (qh < qt) {
        int u = q[qh++];
        for (int e = 0; e < ne; e++) {
            int w = -1;
            if (eu[e] == u) w = ev[e]; else if (ev[e] == u) w = eu[e];
            if (w >= 0 && !seen[w]) { seen[w] = 1; tree[e] = 1; q[qt++] = w; }
        }
    }
    free(seen); free(q);
    memset(hdeg, 0, sizeof hdeg);
    for (int e = 0; e < ne; e++) {
        int x = eu[e], y = ev[e];
        hw[x][hdeg[x]] = y; he[x][hdeg[x]] = e; hd[x][hdeg[x]] = 0; hdeg[x]++;
        hw[y][hdeg[y]] = x; he[y][hdeg[y]] = e; hd[y][hdeg[y]] = 1; hdeg[y]++;
    }
}

static inline int hvolt(int e, int dir) { return dir ? inv_[volt[e]] : volt[e]; }

// bit-parallel cost: bit v0 of reach[x] = lift vertex x within distance t of source (v0,e)
static uint64_t *reachA, *reachB, *nbr; 
static long cost_all(void) {
    long N = (long)nv * n;
    uint64_t full = (nv >= 64) ? ~0ULL : ((1ULL << nv) - 1);
    for (long x = 0; x < N; x++) reachA[x] = 0;
    for (int v0 = 0; v0 < nv; v0++) reachA[(long)v0 * n] |= 1ULL << v0;   // source (v0, identity)
    for (long x = 0; x < N; x++) {
        int u = (int)(x / n), g = (int)(x % n);
        for (int t = 0; t < hdeg[u]; t++) {
            int w = hw[u][t];
            int b = hvolt(he[u][t], hd[u][t]);
            nbr[x * 3 + t] = (long)w * n + mul[(size_t)g * n + b];
        }
    }
    uint64_t *cur = reachA, *nxt = reachB;
    for (int step = 0; step < D; step++) {
        for (long x = 0; x < N; x++) nxt[x] = cur[x];
        for (long x = 0; x < N; x++) {
            uint64_t bits = cur[x];
            if (!bits) continue;
            int u = (int)(x / n);
            for (int t = 0; t < hdeg[u]; t++) nxt[nbr[x * 3 + t]] |= bits;
        }
        uint64_t *tmp = cur; cur = nxt; nxt = tmp;
    }
    long covered = 0;
    for (long x = 0; x < N; x++) covered += __builtin_popcountll(cur[x] & full);
    return N * nv - covered;
}

static void write_outputs(const char *prefix) {
    char fn[1024];
    snprintf(fn, sizeof fn, "%s.edges", prefix);
    FILE *f = fopen(fn, "w");
    fprintf(f, "%ld\n", (long)nv * n);
    for (int e = 0; e < ne; e++)
        for (int g = 0; g < n; g++)
            fprintf(f, "%d %d\n", eu[e] * n + g, ev[e] * n + mul[(size_t)g * n + volt[e]]);
    fclose(f);
    snprintf(fn, sizeof fn, "%s.volt", prefix);
    f = fopen(fn, "w");
    for (int e = 0; e < ne; e++) fprintf(f, "%d\n", volt[e]);
    fclose(f);
}

int main(int argc, char **argv) {
    if (argc < 9) { fprintf(stderr, "usage: nlift BASE m k r D seconds seed OUTPREFIX [T0 T1]\n"); return 1; }
    read_base(argv[1]);
    int m = atoi(argv[2]), k = atoi(argv[3]), r = atoi(argv[4]);
    D = atoi(argv[5]);
    double secs = atof(argv[6]);
    rs = (uint64_t)atoll(argv[7]) * 2654435761ULL + 88172645463325252ULL;
    const char *outp = argv[8];
    double T0 = argc > 9 ? atof(argv[9]) : 3.0, T1 = argc > 10 ? atof(argv[10]) : 0.2;
    build_group(m, k, r);
    srand((unsigned)rs);
    reachA = malloc(sizeof(uint64_t) * (size_t)nv * n); reachB = malloc(sizeof(uint64_t) * (size_t)nv * n); nbr = malloc(sizeof(uint64_t) * 3 * (size_t)nv * n);
    // init voltages
    const char *st = getenv("START");
    int loaded = 0;
    if (st) {
        FILE *f = fopen(st, "r");
        if (f) { loaded = 1; for (int e = 0; e < ne; e++) if (fscanf(f, "%d", &volt[e]) != 1) loaded = 0; fclose(f); }
        if (!loaded) fprintf(stderr, "START unreadable, random init\n");
    }
    if (!loaded) for (int e = 0; e < ne; e++) volt[e] = tree[e] ? 0 : (int)(rnd() % n);
    int *freeE = malloc(sizeof(int) * ne), nfree = 0;
    for (int e = 0; e < ne; e++) if (!tree[e]) freeE[nfree++] = e;
    long cur = cost_all(), best = cur;
    int *bestv = malloc(sizeof(int) * ne); memcpy(bestv, volt, sizeof(int) * ne);
    long evals = 1;
    double t0 = now(), T = T0;
    if (cur == 0) { write_outputs(outp); printf("RESULT N=%ld m=%d k=%d r=%d D=%d best=0 evals=1\n", (long)nv * n, m, k, r, D); return 0; }
    while (1) {
        double el = now() - t0;
        if (el > secs) break;
        T = T0 * pow(T1 / T0, el / secs);
        int e = freeE[rnd() % nfree];
        int old = volt[e];
        int nw = (int)(rnd() % n);
        if (nw == old) continue;
        volt[e] = nw;
        long c = cost_all(); evals++;
        long delta = c - cur;
        if (delta <= 0 || (double)(rnd() % 1000000) / 1e6 < exp(-(double)delta / T)) {
            cur = c;
            if (cur < best) { best = cur; memcpy(bestv, volt, sizeof(int) * ne); }
            if (cur == 0) break;
        } else volt[e] = old;
    }
    memcpy(volt, bestv, sizeof(int) * ne);
    long fin = cost_all();
    if (fin == 0) {
        write_outputs(outp);
        printf("RESULT SOLVED N=%ld m=%d k=%d r=%d D=%d best=0 evals=%ld time=%.1f\n", (long)nv * n, m, k, r, D, evals, now() - t0);
    } else {
        char fn[1024]; snprintf(fn, sizeof fn, "%s.volt", outp);
        FILE *f = fopen(fn, "w"); for (int e = 0; e < ne; e++) fprintf(f, "%d\n", volt[e]); fclose(f);
        printf("RESULT N=%ld m=%d k=%d r=%d D=%d best=%ld evals=%ld\n", (long)nv * n, m, k, r, D, fin, evals);
    }
    return 0;
}
