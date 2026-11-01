// tlift: tabu search over voltages of a base graph lifted over the metacyclic group Z_m x|_r Z_k (element id i*k+j,
// (i,j)(i2,j2) = (i + r^j i2 mod m, j+j2 mod k)); r=1 gives the abelian Z_m x Z_k.
// Lift: vertex (v,g); base edge (x,y) with voltage a gives lift edges (x,g)-(y,g*a).
// Cost = number of (base vertex v0, lift vertex) pairs at distance > D from (v0,e), via bit-parallel BFS.
// Move: change the voltage of one non-tree edge to any other value (full neighbourhood scan each iteration),
// tabu on re-assigning the old value for TT iterations, aspiration on new best, random perturbation after STALL
// non-improving iterations (restart from best with PERT free edges randomised).
// Usage: tlift BASE m k r D seconds seed OUTPREFIX ; env START=<OUTPREFIX.volt file>, TT (default 6), STALL (default 150)
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <stdint.h>

static uint64_t rs;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }

static int nv, ne, n, D;
static int eu[1024], ev[1024];
static int *mul, *inv_;
static int volt[1024], tree[1024];
static int hdeg[256], hw[256][8], he[256][8], hd[256][8];
static uint64_t *reachA, *reachB, *nbr;

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
    for (int t = 0; t < 5000; t++) {
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
    int *seen = calloc(nv, sizeof(int)), *q = malloc(sizeof(int) * nv), qh = 0, qt = 0;
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

static long cost_all(void) {
    long N = (long)nv * n;
    uint64_t full = (nv >= 64) ? ~0ULL : ((1ULL << nv) - 1);
    for (long x = 0; x < N; x++) reachA[x] = 0;
    for (int v0 = 0; v0 < nv; v0++) reachA[(long)v0 * n] |= 1ULL << v0;
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
        memcpy(nxt, cur, sizeof(uint64_t) * (size_t)N);
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
    if (argc < 9) { fprintf(stderr, "usage: tlift BASE m k r D seconds seed OUTPREFIX\n"); return 1; }
    read_base(argv[1]);
    int m = atoi(argv[2]), k = atoi(argv[3]), r = atoi(argv[4]);
    D = atoi(argv[5]);
    double secs = atof(argv[6]);
    rs = (uint64_t)atoll(argv[7]) * 2654435761ULL + 88172645463325252ULL;
    const char *outp = argv[8];
    int TT = getenv("TT") ? atoi(getenv("TT")) : 6;
    long STALL = getenv("STALL") ? atol(getenv("STALL")) : 150;
    long SAMP = getenv("SAMP") ? atol(getenv("SAMP")) : 0;
    srand((unsigned)rs);
    build_group(m, k, r);
    long N = (long)nv * n;
    reachA = malloc(sizeof(uint64_t) * (size_t)N); reachB = malloc(sizeof(uint64_t) * (size_t)N);
    nbr = malloc(sizeof(uint64_t) * 3 * (size_t)N);
    int loaded = 0;
    const char *st = getenv("START");
    if (st) {
        FILE *f = fopen(st, "r");
        if (f) { loaded = 1; for (int e = 0; e < ne; e++) if (fscanf(f, "%d", &volt[e]) != 1) loaded = 0; fclose(f); }
        if (!loaded) fprintf(stderr, "START unreadable, random init\n");
    }
    if (!loaded) for (int e = 0; e < ne; e++) volt[e] = tree[e] ? 0 : (int)(rnd() % n);
    int *freeE = malloc(sizeof(int) * ne), nfree = 0;
    for (int e = 0; e < ne; e++) if (!tree[e]) freeE[nfree++] = e;
    long cur = cost_all(), best = cur, evals = 1;
    int *bestv = malloc(sizeof(int) * ne); memcpy(bestv, volt, sizeof(int) * ne);
    long *tabu = calloc((size_t)ne * n, sizeof(long));
    double t0 = now();
    long iter = 0, lastimp = 0, restarts = 0;
    if (cur == 0) goto done;
    while (now() - t0 < secs && cur > 0) {
        long bc = -1, ties = 0; int be = -1, bv = -1;
        // SAMP > 0: evaluate SAMP random (edge, value) moves per iteration; otherwise the full neighbourhood
        long nmoves = SAMP > 0 ? SAMP : (long)nfree * (n - 1);
        for (long mi = 0; mi < nmoves; mi++) {
            int fi, v, e;
            if (SAMP > 0) { fi = (int)(rnd() % nfree); e = freeE[fi]; v = (int)(rnd() % n); if (v == volt[e]) continue; }
            else { fi = (int)(mi / (n - 1)); e = freeE[fi]; v = (int)(mi % (n - 1)); if (v >= volt[e]) v++; }
            int old = volt[e];
            volt[e] = v;
            long c = cost_all(); evals++;
            volt[e] = old;
            if (tabu[(size_t)e * n + v] > iter && c >= best) continue;
            if (bc < 0 || c < bc) { bc = c; be = e; bv = v; ties = 1; }
            else if (c == bc && rnd() % (++ties) == 0) { be = e; bv = v; }
        }
        if (be < 0) break;
        tabu[(size_t)be * n + volt[be]] = iter + TT + (long)(rnd() % 4);
        volt[be] = bv; cur = bc;
        if (cur < best) { best = cur; memcpy(bestv, volt, sizeof(int) * ne); lastimp = iter; }
        iter++;
        if (iter - lastimp > STALL) {
            // restart from best with a random perturbation of 3 free edges
            memcpy(volt, bestv, sizeof(int) * ne);
            for (int p = 0; p < 3; p++) volt[freeE[rnd() % nfree]] = (int)(rnd() % n);
            cur = cost_all(); evals++;
            lastimp = iter; restarts++;
        }
    }
done:
    memcpy(volt, bestv, sizeof(int) * ne);
    long fin = cost_all();
    if (fin == 0) {
        write_outputs(outp);
        printf("RESULT SOLVED N=%ld m=%d k=%d r=%d D=%d best=0 evals=%ld iters=%ld restarts=%ld time=%.1f\n", N, m, k, r, D, evals, iter, restarts, now() - t0);
    } else {
        char fn[1024]; snprintf(fn, sizeof fn, "%s.volt", outp);
        FILE *f = fopen(fn, "w"); for (int e = 0; e < ne; e++) fprintf(f, "%d\n", volt[e]); fclose(f);
        printf("RESULT N=%ld m=%d k=%d r=%d D=%d best=%ld evals=%ld iters=%ld restarts=%ld\n", N, m, k, r, D, fin, evals, iter, restarts);
    }
    return 0;
}
