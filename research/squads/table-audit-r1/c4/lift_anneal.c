/* lift_anneal.c: simulated annealing over voltage assignments of a regular voltage lift.
   Base: bipartite multigraph B (spec file), parts A = {0..p-1}, B = {p..nb-1}; every base edge is (u in A, w in B).
   Group: Gamma = Z_m x|_r Z_k (k=1, r=1 gives cyclic Z_m). Element index x*k+y, identity 0.
   Lift: vertices (b,g), id = b*N+g; base edge e=(u,w) with voltage a gives (u,g) ~ (w, g*a) for all g.
   Gamma acts by left multiplication, so the diameter equals the max eccentricity over the base vertices (s, identity).
   Cost = sum over base s of #lift vertices not within distance D of (s, identity). Cost 0 = diameter <= D.
   Usage: lift_anneal SPEC m k r d D restarts iters seed tlimit_sec outprefix [T0]
   Writes outprefix.edges (edge list, first line n) when a zero-cost lift is found, and outprefix.volt always. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <time.h>
#include <stdint.h>

static uint64_t rs = 88172645463325252ULL;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline double urand(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }
static inline int irand(int n) { return (int)(rnd() % (uint64_t)n); }

static int N, nb, p, E, d, D;
static int *MUL, *INV;
static int *eu, *ew, *V, *istree, *qf, *qb;
static int *dstart, *dto, *dvol;
static int *seen, *Q, gen = 0;

static void set_volt(int e, int x) {
    V[e] = x;
    dvol[qf[e]] = x;
    dvol[qb[e]] = INV[x];
}

/* number of lift vertices within distance D of (s, identity) */
static int reach(int s) {
    gen++;
    int head = 0, tail = 0, level = 0;
    int src = s * N;
    seen[src] = gen; Q[tail++] = src;
    while (head < tail && level < D) {
        int end = tail;
        while (head < end) {
            int id = Q[head++];
            int b = id / N, g = id - b * N;
            for (int k = dstart[b]; k < dstart[b + 1]; k++) {
                int nid = dto[k] * N + MUL[g * N + dvol[k]];
                if (seen[nid] != gen) { seen[nid] = gen; Q[tail++] = nid; }
            }
        }
        level++;
    }
    return tail;
}

static long cost_all(void) {
    long c = 0, n = (long)nb * N;
    for (int s = 0; s < nb; s++) c += n - reach(s);
    return c;
}

static int conflict(int e, int x) {
    for (int f = 0; f < E; f++)
        if (f != e && eu[f] == eu[e] && ew[f] == ew[e] && V[f] == x) return 1;
    return 0;
}

static void write_edges(const char *fn) {
    FILE *f = fopen(fn, "w");
    fprintf(f, "%d\n", nb * N);
    for (int e = 0; e < E; e++)
        for (int g = 0; g < N; g++)
            fprintf(f, "%d %d\n", eu[e] * N + g, ew[e] * N + MUL[g * N + V[e]]);
    fclose(f);
}

static void write_volt(const char *fn) {
    FILE *f = fopen(fn, "w");
    for (int e = 0; e < E; e++) fprintf(f, "%d %d %d\n", eu[e], ew[e], V[e]);
    fclose(f);
}

int main(int argc, char **argv) {
    if (argc < 12) {
        fprintf(stderr, "usage: lift_anneal SPEC m k r d D restarts iters seed tlimit outprefix [T0]\n");
        return 1;
    }
    const char *spec = argv[1];
    int m = atoi(argv[2]), k = atoi(argv[3]), r = atoi(argv[4]);
    d = atoi(argv[5]); D = atoi(argv[6]);
    int restarts = atoi(argv[7]);
    long iters = atol(argv[8]);
    rs ^= (uint64_t)atoll(argv[9]) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    double tlimit = atof(argv[10]);
    const char *outp = argv[11];
    double T0 = argc > 12 ? atof(argv[12]) : 2.0, T1 = 0.05;

    N = m * k;
    long rp = 1 % m;
    for (int i = 0; i < k; i++) rp = (rp * r) % m;
    if (rp != 1 % m) { fprintf(stderr, "r^k != 1 mod m\n"); return 1; }
    int *rpow = malloc(sizeof(int) * k);
    rpow[0] = 1 % m;
    for (int y = 1; y < k; y++) rpow[y] = (int)(((long)rpow[y - 1] * r) % m);
    MUL = malloc(sizeof(int) * (size_t)N * N);
    INV = malloc(sizeof(int) * N);
    for (int a = 0; a < N; a++) {
        int x1 = a / k, y1 = a % k;
        for (int b = 0; b < N; b++) {
            int x2 = b / k, y2 = b % k;
            int x = (int)((x1 + (long)rpow[y1] * x2) % m);
            int y = (y1 + y2) % k;
            MUL[a * N + b] = x * k + y;
        }
    }
    for (int a = 0; a < N; a++)
        for (int b = 0; b < N; b++)
            if (MUL[a * N + b] == 0) INV[a] = b;

    FILE *f = fopen(spec, "r");
    if (!f || fscanf(f, "%d %d", &nb, &p) != 2 || fscanf(f, "%d", &E) != 1) { fprintf(stderr, "bad spec\n"); return 1; }
    eu = malloc(sizeof(int) * E); ew = malloc(sizeof(int) * E); V = malloc(sizeof(int) * E);
    istree = calloc(E, sizeof(int)); qf = malloc(sizeof(int) * E); qb = malloc(sizeof(int) * E);
    for (int e = 0; e < E; e++) {
        if (fscanf(f, "%d %d", &eu[e], &ew[e]) != 2 || eu[e] >= p || ew[e] < p || ew[e] >= nb) {
            fprintf(stderr, "bad edge %d (need u in A, w in B)\n", e); return 1;
        }
        V[e] = 0;
    }
    fclose(f);

    /* spanning tree (voltage 0 by switching) */
    int *vis = calloc(nb, sizeof(int)); vis[0] = 1;
    int changed = 1;
    while (changed) {
        changed = 0;
        for (int e = 0; e < E; e++) {
            if (vis[eu[e]] && !vis[ew[e]]) { vis[ew[e]] = 1; istree[e] = 1; changed = 1; }
            else if (!vis[eu[e]] && vis[ew[e]]) { vis[eu[e]] = 1; istree[e] = 1; changed = 1; }
        }
    }
    for (int b = 0; b < nb; b++) if (!vis[b]) { fprintf(stderr, "base disconnected\n"); return 1; }
    int *nt = malloc(sizeof(int) * E), nnt = 0;
    for (int e = 0; e < E; e++) if (!istree[e]) nt[nnt++] = e;

    /* darts CSR */
    int *deg = calloc(nb, sizeof(int)), *pos = malloc(sizeof(int) * nb);
    for (int e = 0; e < E; e++) { deg[eu[e]]++; deg[ew[e]]++; }
    dstart = malloc(sizeof(int) * (nb + 1));
    dstart[0] = 0;
    for (int b = 0; b < nb; b++) {
        if (deg[b] > d) { fprintf(stderr, "base degree %d > d at vertex %d\n", deg[b], b); return 1; }
        dstart[b + 1] = dstart[b] + deg[b];
        pos[b] = dstart[b];
    }
    dto = malloc(sizeof(int) * 2 * E); dvol = malloc(sizeof(int) * 2 * E);
    for (int e = 0; e < E; e++) {
        qf[e] = pos[eu[e]]++; dto[qf[e]] = ew[e];
        qb[e] = pos[ew[e]]++; dto[qb[e]] = eu[e];
    }

    seen = calloc((size_t)nb * N, sizeof(int));
    Q = malloc(sizeof(int) * (size_t)nb * N);
    for (int e = 0; e < E; e++) set_volt(e, 0);

    int *bestV = malloc(sizeof(int) * E);
    long best = -1;
    clock_t t0 = clock();
    int found = 0, stop = 0;
    long nsteps = 0;
    for (int rr = 0; rr < restarts && !found && !stop; rr++) {
        for (int i = 0; i < nnt; i++) {
            int e = nt[i], x;
            do { x = irand(N); } while (conflict(e, x));
            set_volt(e, x);
        }
        long cur = cost_all();
        if (best < 0 || cur < best) { best = cur; memcpy(bestV, V, sizeof(int) * E); }
        for (long it = 0; it < iters; it++) {
            double T = T0 * pow(T1 / T0, (double)it / (double)iters);
            int e = nt[irand(nnt)];
            int old = V[e], x;
            if (urand() < 0.5) x = irand(N);
            else {
                int delta = 1 + irand(3);
                if (rnd() & 1) delta = N - delta;
                x = (old + delta) % N;
            }
            if (x == old || conflict(e, x)) continue;
            set_volt(e, x);
            long c = cost_all();
            nsteps++;
            if (c <= cur || urand() < exp((double)(cur - c) / T)) {
                cur = c;
                if (cur < best) { best = cur; memcpy(bestV, V, sizeof(int) * E); }
                if (cur == 0) { found = 1; break; }
            } else {
                set_volt(e, old);
            }
            if ((it & 1023) == 0 && (double)(clock() - t0) / CLOCKS_PER_SEC > tlimit) { stop = 1; break; }
        }
        fprintf(stderr, "restart %d done: cur=%ld best=%ld steps=%ld t=%.1fs\n", rr, cur, best, nsteps,
                (double)(clock() - t0) / CLOCKS_PER_SEC);
    }

    if (found) {
        memcpy(V, V, 0);
        char fn[512];
        snprintf(fn, sizeof fn, "%s.edges", outp);
        write_edges(fn);
        snprintf(fn, sizeof fn, "%s.volt", outp);
        write_volt(fn);
        printf("FOUND n=%d d=%d D=%d N=%d steps=%ld\n", nb * N, d, D, N, nsteps);
    } else {
        memcpy(V, bestV, sizeof(int) * E);
        char fn[512];
        snprintf(fn, sizeof fn, "%s.volt", outp);
        write_volt(fn);
        printf("NOTFOUND best_cost=%ld n=%d N=%d steps=%ld\n", best, nb * N, N, nsteps);
    }
    return 0;
}
