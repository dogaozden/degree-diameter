/* c8: simulated annealing over Z_m voltage assignments of a bipartite base graph.
 * Lift vertex (u,g) -> index u*m+g; base edge e=(a,b) with voltage t gives lift edges (a,g)-(b,g+t).
 * Cost = sum over base vertices s of #{lift vertices at distance > D from (s,0)} (BFS, depth-limited).
 * By the left Z_m action, this is zero iff the lift has diameter <= D.
 * usage: vlift BASE m D SECS SEED OUT [T0 T1]
 * On cost 0 writes OUT as an edge list (first line = vertex count) and exits 0.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <time.h>

static int N, E, m, D, n;
static int *eu, *ev, *volt, *istree;
static int *inc_cnt, **inc_e, **inc_dir; /* incidence per base vertex */
static int *dist, *queue, *stamp;
static int curstamp = 0;
static unsigned long long rs;

static unsigned long long rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static double urand(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }

static long cost_from(int s) {
    /* BFS from lift vertex (s,0) up to depth D, count reached */
    int head = 0, tail = 0, reached = 0;
    curstamp++;
    int src = s * m;
    stamp[src] = curstamp; dist[src] = 0; queue[tail++] = src; reached = 1;
    while (head < tail) {
        int x = queue[head++];
        int dx = dist[x];
        if (dx >= D) continue;
        int u = x / m, g = x % m;
        for (int k = 0; k < inc_cnt[u]; k++) {
            int e = inc_e[u][k], w, h;
            if (inc_dir[u][k] > 0) { w = ev[e]; h = (g + volt[e]) % m; }
            else { w = eu[e]; h = (g - volt[e] + m) % m; }
            int y = w * m + h;
            if (stamp[y] != curstamp) {
                stamp[y] = curstamp; dist[y] = dx + 1; queue[tail++] = y; reached++;
            }
        }
    }
    return (long)n - reached;
}

static long total_cost(void) {
    long c = 0;
    for (int s = 0; s < N; s++) c += cost_from(s);
    return c;
}

static void write_lift(const char *out) {
    FILE *f = fopen(out, "w");
    if (!f) { perror("out"); exit(2); }
    fprintf(f, "%d\n", n);
    for (int e = 0; e < E; e++)
        for (int g = 0; g < m; g++)
            fprintf(f, "%d %d\n", eu[e] * m + g, ev[e] * m + (g + volt[e]) % m);
    fclose(f);
}

int main(int argc, char **argv) {
    if (argc < 7) { fprintf(stderr, "usage: vlift BASE m D SECS SEED OUT [T0 T1]\n"); return 1; }
    FILE *f = fopen(argv[1], "r");
    if (!f) { perror("base"); return 1; }
    m = atoi(argv[2]); D = atoi(argv[3]);
    double secs = atof(argv[4]);
    rs = 0x9E3779B97F4A7C15ULL ^ (unsigned long long)atoll(argv[5]) * 2654435761ULL;
    for (int i = 0; i < 10; i++) rnd();
    const char *out = argv[6];
    double T0 = argc > 7 ? atof(argv[7]) : 2.0, T1 = argc > 8 ? atof(argv[8]) : 0.2;
    if (fscanf(f, "%d %d", &N, &E) != 2) return 1;
    eu = malloc(sizeof(int) * E); ev = malloc(sizeof(int) * E);
    volt = calloc(E, sizeof(int)); istree = calloc(E, sizeof(int));
    for (int e = 0; e < E; e++) if (fscanf(f, "%d %d", &eu[e], &ev[e]) != 2) return 1;
    fclose(f);
    n = N * m;
    /* spanning tree (BFS from base vertex 0): tree edges fixed to voltage 0 (gauge) */
    {
        int *seen = calloc(N, sizeof(int)); int *q = malloc(sizeof(int) * N);
        int h = 0, t = 0; q[t++] = 0; seen[0] = 1;
        while (h < t) {
            int x = q[h++];
            for (int e = 0; e < E; e++) {
                int y = -1;
                if (eu[e] == x) y = ev[e]; else if (ev[e] == x) y = eu[e];
                if (y >= 0 && !seen[y]) { seen[y] = 1; istree[e] = 1; q[t++] = y; }
            }
        }
        free(seen); free(q);
    }
    inc_cnt = calloc(N, sizeof(int));
    inc_e = malloc(sizeof(int *) * N); inc_dir = malloc(sizeof(int *) * N);
    for (int u = 0; u < N; u++) { inc_e[u] = malloc(sizeof(int) * E); inc_dir[u] = malloc(sizeof(int) * E); }
    for (int e = 0; e < E; e++) {
        int a = eu[e], b = ev[e];
        inc_e[a][inc_cnt[a]] = e; inc_dir[a][inc_cnt[a]++] = +1;
        inc_e[b][inc_cnt[b]] = e; inc_dir[b][inc_cnt[b]++] = -1;
    }
    dist = malloc(sizeof(int) * n); queue = malloc(sizeof(int) * n); stamp = calloc(n, sizeof(int));
    int *freeE = malloc(sizeof(int) * E); int nfree = 0;
    for (int e = 0; e < E; e++) if (!istree[e]) freeE[nfree++] = e;
    for (int i = 0; i < nfree; i++) volt[freeE[i]] = rnd() % m;

    long cur = total_cost(), best = cur;
    fprintf(stderr, "init N=%d E=%d n=%d m=%d D=%d free=%d cost=%ld\n", N, E, n, m, D, nfree, cur);
    double t0 = now(), tlast = t0; long it = 0;
    while (cur > 0) {
        it++;
        double el = now() - t0;
        if (el > secs) break;
        double frac = el / secs;
        double T = T0 * pow(T1 / T0, frac);
        int e = freeE[rnd() % nfree];
        int old = volt[e];
        int nv = (old + 1 + rnd() % (m - 1)) % m;
        volt[e] = nv;
        long c2 = total_cost();
        long d = c2 - cur;
        if (d <= 0 || urand() < exp(-(double)d / T)) {
            cur = c2;
            if (cur < best) { best = cur; }
        } else volt[e] = old;
        if (now() - tlast > 10.0) {
            tlast = now();
            fprintf(stderr, "t=%.0fs it=%ld T=%.3f cur=%ld best=%ld\n", el, it, T, cur, best);
        }
    }
    fprintf(stderr, "done it=%ld cur=%ld best=%ld\n", it, cur, best);
    if (cur == 0) {
        write_lift(out);
        printf("FOUND lift with n=%d, D=%d, written to %s\n", n, D, out);
        return 0;
    }
    /* report best-effort status: nonzero cost */
    printf("NOT_FOUND final_cost=%ld\n", cur);
    return 3;
}
