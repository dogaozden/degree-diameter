/* Simulated annealing over voltage lifts of a cubic bipartite base multigraph.
   Group: metacyclic Z_m x|_r Z_k (element g = y*m + x; (x1,y1)(x2,y2) = (x1 + r^y1 x2 mod m, y1+y2 mod k)).
   Cyclic Z_N is m=N, k=1, r=1.
   Lift: vertex (u,g) -> index u*N+g; base edge (u->w, a) gives (u,g) ~ (w, g*a).
   Cost = number of (base vertex s, lift vertex) pairs at distance > D from (s,id), summed over s.
   Usage: lift_sa BASEFILE m k r D iters restarts seed T0 OUTFILE */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <stdint.h>
#include <time.h>

static int b, E, N, D, K;
static int *eu, *ew, *treeflag, *nt, *volt, *mul, *inv;
static int *adjW, *adjR;
static int *stamp, *queue, *dist;
static int curstamp = 0;
static uint64_t rs;

static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static double rndu(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static void build_group(int m, int k, int r) {
    N = m * k;
    mul = malloc(sizeof(int) * N * N);
    inv = malloc(sizeof(int) * N);
    int *rp = malloc(sizeof(int) * k);
    rp[0] = 1 % m;
    for (int y = 1; y < k; y++) rp[y] = (int)((long)rp[y - 1] * r % m);
    if ((long)rp[k - 1] * r % m != 1 % m) { fprintf(stderr, "bad group: r^k != 1 mod m\n"); exit(2); }
    for (int g1 = 0; g1 < N; g1++)
        for (int g2 = 0; g2 < N; g2++) {
            int x1 = g1 % m, y1 = g1 / m, x2 = g2 % m, y2 = g2 / m;
            int x = (int)((x1 + (long)rp[y1] * x2) % m);
            int y = (y1 + y2) % k;
            mul[g1 * N + g2] = y * m + x;
        }
    for (int g = 0; g < N; g++) {
        int found = 0;
        for (int h = 0; h < N; h++) if (mul[g * N + h] == 0) { inv[g] = h; found = 1; break; }
        if (!found) { fprintf(stderr, "no inverse\n"); exit(2); }
    }
    /* quick associativity spot check */
    for (int t = 0; t < 20000; t++) {
        int a = rnd() % N, c = rnd() % N, d = rnd() % N;
        if (mul[mul[a * N + c] * N + d] != mul[a * N + mul[c * N + d]]) { fprintf(stderr, "not associative\n"); exit(2); }
    }
    free(rp);
}

static void build_adj(void) {
    int *cnt = calloc(b, sizeof(int));
    for (int i = 0; i < E; i++) {
        int u = eu[i], w = ew[i], a = volt[i];
        adjW[u * 3 + cnt[u]] = w; adjR[u * 3 + cnt[u]] = a; cnt[u]++;
        adjW[w * 3 + cnt[w]] = u; adjR[w * 3 + cnt[w]] = inv[a]; cnt[w]++;
    }
    free(cnt);
}

/* simple-lift check: for each base vertex, its three (neighbour, multiplier) pairs must be distinct */
static int valid(void) {
    for (int u = 0; u < b; u++)
        for (int p = 0; p < 3; p++)
            for (int q = p + 1; q < 3; q++)
                if (adjW[u * 3 + p] == adjW[u * 3 + q] && adjR[u * 3 + p] == adjR[u * 3 + q]) return 0;
    return 1;
}

static long cost_eval(void) {
    long n = (long)b * N, total = 0;
    for (int s = 0; s < b; s++) {
        curstamp++;
        int head = 0, tail = 0, src = s * N;
        stamp[src] = curstamp; dist[src] = 0; queue[tail++] = src;
        while (head < tail) {
            int x = queue[head++];
            int d = dist[x];
            if (d == D) continue;
            int u = x / N, g = x % N;
            for (int k = 0; k < 3; k++) {
                int w = adjW[u * 3 + k], r = adjR[u * 3 + k];
                int y = w * N + mul[g * N + r];
                if (stamp[y] != curstamp) { stamp[y] = curstamp; dist[y] = d + 1; queue[tail++] = y; }
            }
        }
        total += n - tail;
    }
    return total;
}

static void write_graph(const char *fn) {
    FILE *f = fopen(fn, "w");
    fprintf(f, "%d\n", b * N);
    for (int i = 0; i < E; i++) {
        int u = eu[i], w = ew[i], a = volt[i];
        for (int g = 0; g < N; g++)
            fprintf(f, "%d %d\n", u * N + g, w * N + mul[g * N + a]);
    }
    fclose(f);
}

int main(int argc, char **argv) {
    if (argc < 11) { fprintf(stderr, "usage: BASE m k r D iters restarts seed T0 OUT\n"); return 1; }
    FILE *bf = fopen(argv[1], "r");
    int m = atoi(argv[2]), k = atoi(argv[3]), r = atoi(argv[4]);
    D = atoi(argv[5]);
    long iters = atol(argv[6]);
    int restarts = atoi(argv[7]);
    uint64_t seed = strtoull(argv[8], 0, 10);
    double T0 = atof(argv[9]);
    const char *outfn = argv[10];
    if (fscanf(bf, "%d %d", &b, &E) != 2) return 2;
    eu = malloc(sizeof(int) * E); ew = malloc(sizeof(int) * E);
    for (int i = 0; i < E; i++) if (fscanf(bf, "%d %d", &eu[i], &ew[i]) != 2) return 2;
    fclose(bf);
    build_group(m, k, r);
    /* spanning tree by BFS over base multigraph */
    treeflag = calloc(E, sizeof(int));
    int *seen = calloc(b, sizeof(int)); int *bq = malloc(sizeof(int) * b); int bh = 0, bt = 0;
    seen[0] = 1; bq[bt++] = 0;
    while (bh < bt) {
        int x = bq[bh++];
        for (int i = 0; i < E; i++) {
            int y = -1;
            if (eu[i] == x) y = ew[i]; else if (ew[i] == x) y = eu[i];
            if (y >= 0 && !seen[y]) { seen[y] = 1; treeflag[i] = 1; bq[bt++] = y; }
        }
    }
    if (bt != b) { fprintf(stderr, "base disconnected\n"); return 2; }
    K = 0; nt = malloc(sizeof(int) * E);
    for (int i = 0; i < E; i++) if (!treeflag[i]) nt[K++] = i;
    volt = calloc(E, sizeof(int));
    adjW = malloc(sizeof(int) * b * 3); adjR = malloc(sizeof(int) * b * 3);
    stamp = calloc((long)b * N, sizeof(int)); queue = malloc(sizeof(int) * (long)b * N); dist = malloc(sizeof(int) * (long)b * N);
    rs = seed ? seed : (uint64_t)time(NULL) * 2654435761ULL + 1;
    long globalbest = -1;
    for (int rep = 0; rep < restarts; rep++) {
        /* random valid start */
        for (;;) {
            for (int i = 0; i < E; i++) volt[i] = treeflag[i] ? 0 : (int)(rnd() % N);
            build_adj();
            if (valid()) break;
        }
        long cur = cost_eval();
        long best = cur;
        for (long it = 0; it < iters && cur > 0; it++) {
            double T = T0 * (1.0 - (double)it / iters) + 1e-3;
            int j = nt[rnd() % K];
            int old = volt[j];
            int nv = (int)(rnd() % N);
            if (nv == old) continue;
            volt[j] = nv;
            build_adj();
            if (!valid()) { volt[j] = old; build_adj(); continue; }
            long c = cost_eval();
            if (c <= cur || rndu() < exp(-(double)(c - cur) / T)) {
                cur = c;
                if (cur < best) best = cur;
            } else {
                volt[j] = old; build_adj();
            }
        }
        if (globalbest < 0 || best < globalbest) globalbest = best;
        fprintf(stderr, "restart %d: best cost %ld (final %ld)\n", rep, best, cur);
        if (cur == 0) {
            write_graph(outfn);
            printf("FOUND n=%d D=%d m=%d k=%d r=%d base=%s\nVOLT", b * N, D, m, k, r, argv[1]);
            for (int i = 0; i < E; i++) printf(" %d", volt[i]);
            printf("\n");
            return 0;
        }
    }
    printf("NOTFOUND m=%d k=%d r=%d best=%ld base=%s\n", m, k, r, globalbest, argv[1]);
    return 0;
}
