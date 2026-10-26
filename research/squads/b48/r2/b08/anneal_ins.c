/* b08: simulated annealing over insertion choices on a valid 2184-vertex 4-regular bipartite seed.
 * State: K seed edges deleted (del[]), new vertex x (side 0) joined to the side-1 endpoints selected by xm,
 * new vertex y (side 1) joined to the side-0 endpoints selected by ym, optional edge xy.
 * Energy = exact number of unordered pairs at distance > 8 (bitset BFS to radius 8).
 * usage: anneal_ins SEED.edges K dx dy xy SECONDS RNG T0 T1 OUT.edges */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN0 2200
#define MAXNN 2208
#define WMAX 40
#define MAXK 6
#define MAXE 5000

static int n0, nn, em;
static int side[MAXN0];
static int ea[MAXE], eb[MAXE];
static int adj0[MAXN0][4], inc0[MAXN0][4], deg0[MAXN0];
static int adjc[MAXNN][4], degc[MAXNN];
static uint64_t bufA[MAXNN * WMAX], bufB[MAXNN * WMAX];
static int K, DX, DY, XY;

typedef struct { int del[MAXK]; unsigned xm, ym; } State;

static uint64_t rs;
static inline uint64_t rnext(void) { rs ^= rs >> 12; rs ^= rs << 25; rs ^= rs >> 27; return rs * 2685821657736338717ULL; }
static inline double urand(void) { return (rnext() >> 11) * (1.0 / 9007199254740992.0); }
static inline int rnd(int n) { return (int)(urand() * n); }

static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }

static void rem(int u, int v) {
    for (int q = 0; q < degc[u]; q++)
        if (adjc[u][q] == v) { adjc[u][q] = adjc[u][--degc[u]]; return; }
    fprintf(stderr, "internal: missing edge\n"); exit(2);
}
static void add(int u, int v) { adjc[u][degc[u]++] = v; }

static void build(const State *s) {
    for (int v = 0; v < n0; v++) { degc[v] = deg0[v]; memcpy(adjc[v], adj0[v], sizeof adj0[v]); }
    degc[n0] = degc[n0 + 1] = 0;
    for (int i = 0; i < K; i++) { int e = s->del[i]; rem(ea[e], eb[e]); rem(eb[e], ea[e]); }
    for (int i = 0; i < K; i++) if (s->xm >> i & 1) { int vb = eb[s->del[i]]; add(n0, vb); add(vb, n0); }
    for (int i = 0; i < K; i++) if (s->ym >> i & 1) { int va = ea[s->del[i]]; add(n0 + 1, va); add(va, n0 + 1); }
    if (XY) { add(n0, n0 + 1); add(n0 + 1, n0); }
}

static long far_count(void) {
    int N = nn, Wn = (N + 63) / 64;
    uint64_t *cur = bufA, *nxt = bufB;
    memset(cur, 0, sizeof(uint64_t) * N * Wn);
    for (int v = 0; v < N; v++) cur[v * Wn + v / 64] = 1ULL << (v % 64);
    for (int step = 0; step < 8; step++) {
        for (int v = 0; v < N; v++) {
            uint64_t *d = nxt + v * Wn;
            memcpy(d, cur + v * Wn, sizeof(uint64_t) * Wn);
            for (int q = 0; q < degc[v]; q++) {
                const uint64_t *s = cur + adjc[v][q] * Wn;
                for (int w = 0; w < Wn; w++) d[w] |= s[w];
            }
        }
        uint64_t *t = cur; cur = nxt; nxt = t;
    }
    long tot = 0;
    for (int v = 0; v < N; v++) {
        int pc = 0;
        for (int w = 0; w < Wn; w++) pc += __builtin_popcountll(cur[v * Wn + w]);
        tot += N - pc;
    }
    return tot / 2;
}

static int popc(unsigned x) { return __builtin_popcount(x); }

static int valid(const State *s) {
    for (int i = 0; i < K; i++) for (int j = 0; j < i; j++) if (s->del[i] == s->del[j]) return 0;
    if (popc(s->xm) != DX || popc(s->ym) != DY) return 0;
    for (int i = 0; i < K; i++) for (int j = 0; j < i; j++) {
        if ((s->xm >> i & 1) && (s->xm >> j & 1) && eb[s->del[i]] == eb[s->del[j]]) return 0;
        if ((s->ym >> i & 1) && (s->ym >> j & 1) && ea[s->del[i]] == ea[s->del[j]]) return 0;
    }
    return 1;
}

static void propose(const State *s, State *t) {
    *t = *s;
    double wx = (DX < K) ? 0.25 : 0.0, wy = (DY < K) ? 0.25 : 0.0;
    double r = urand() * (0.5 + wx + wy);
    if (r < 0.5) {
        int i = rnd(K), e;
        if (urand() < 0.7) {
            int j = rnd(K), ed = s->del[j];
            int v = (urand() < 0.5) ? ea[ed] : eb[ed];
            int w = adj0[v][rnd(4)];
            e = inc0[w][rnd(4)];
        } else e = rnd(em);
        t->del[i] = e;
    } else if (r < 0.5 + wx) {
        int ones[MAXK], zeros[MAXK], no = 0, nz = 0;
        for (int i = 0; i < K; i++) { if (s->xm >> i & 1) ones[no++] = i; else zeros[nz++] = i; }
        int a = ones[rnd(no)], b = zeros[rnd(nz)];
        t->xm = (s->xm & ~(1u << a)) | (1u << b);
    } else {
        int ones[MAXK], zeros[MAXK], no = 0, nz = 0;
        for (int i = 0; i < K; i++) { if (s->ym >> i & 1) ones[no++] = i; else zeros[nz++] = i; }
        int a = ones[rnd(no)], b = zeros[rnd(nz)];
        t->ym = (s->ym & ~(1u << a)) | (1u << b);
    }
}

static void random_state(State *s) {
    do {
        for (int i = 0; i < K; i++) s->del[i] = rnd(em);
        s->xm = 0; s->ym = 0;
        while (popc(s->xm) < DX) s->xm |= 1u << rnd(K);
        while (popc(s->ym) < DY) s->ym |= 1u << rnd(K);
    } while (!valid(s));
}

int main(int argc, char **argv) {
    if (argc < 10) { fprintf(stderr, "usage: anneal_ins SEED.edges K dx dy xy SECONDS RNG T0 T1 OUT.edges\n"); return 1; }
    K = atoi(argv[2]); DX = atoi(argv[3]); DY = atoi(argv[4]); XY = atoi(argv[5]);
    double secs = atof(argv[6]); rs = strtoull(argv[7], 0, 10) * 2654435761ULL + 88172645463325252ULL;
    double T0 = atof(argv[8]), T1 = atof(argv[9]);
    const char *out = argv[10];
    if (K > MAXK || DX + XY > 4 || DY + XY > 4 || DX > K || DY > K) { fprintf(stderr, "bad params\n"); return 1; }

    FILE *f = fopen(argv[1], "r");
    if (!f || fscanf(f, "%d", &n0) != 1) { fprintf(stderr, "cannot read seed\n"); return 1; }
    int u, v; em = 0;
    while (fscanf(f, "%d %d", &u, &v) == 2) {
        if (deg0[u] >= 4 || deg0[v] >= 4) { fprintf(stderr, "seed degree > 4\n"); return 1; }
        adj0[u][deg0[u]] = v; inc0[u][deg0[u]++] = em;
        adj0[v][deg0[v]] = u; inc0[v][deg0[v]++] = em;
        if (em >= MAXE) { fprintf(stderr, "too many edges\n"); return 1; }
        em++;
        ea[em - 1] = u; eb[em - 1] = v; /* fixed below using coloring */
    }
    fclose(f);
    /* 2-colour: side 0 contains vertex 0 */
    for (int i = 0; i < n0; i++) side[i] = -1;
    {
        static int qu[MAXN0]; int h = 0, t = 0; side[0] = 0; qu[t++] = 0;
        while (h < t) { int x = qu[h++]; for (int q = 0; q < deg0[x]; q++) { int y = adj0[x][q];
            if (side[y] < 0) { side[y] = 1 - side[x]; qu[t++] = y; }
            else if (side[y] == side[x]) { fprintf(stderr, "seed not bipartite\n"); return 1; } } }
    }
    for (int e = 0; e < em; e++) {
        int a = ea[e], b = eb[e];
        if (side[a] == 1) { int tmp = a; a = b; b = tmp; }
        ea[e] = a; eb[e] = b;
    }
    nn = n0 + 2;

    State cur, best, cand;
    random_state(&cur);
    build(&cur);
    long E = far_count();
    long bestE = E; best = cur;
    double t0 = now(), tnow;
    long it = 0, acc = 0;
    while (1) {
        tnow = now();
        double frac = (tnow - t0) / secs;
        if (frac >= 1.0 || bestE == 0) break;
        double T = T0 * pow(T1 / T0, frac);
        propose(&cur, &cand);
        if (!valid(&cand)) continue;
        build(&cand);
        long E2 = far_count();
        it++;
        long dE = E2 - E;
        if (dE <= 0 || urand() < exp(-dE / T)) {
            cur = cand; E = E2; acc++;
            if (E < bestE) { bestE = E; best = cur; }
        }
    }
    build(&best);
    long chk = far_count();
    /* write best graph */
    FILE *g = fopen(out, "w");
    fprintf(g, "%d\n", nn);
    int ecount = 0;
    for (int x = 0; x < nn; x++) for (int q = 0; q < degc[x]; q++) if (adjc[x][q] > x) { fprintf(g, "%d %d\n", x, adjc[x][q]); ecount++; }
    fclose(g);
    printf("RESULT n=%d K=%d dx=%d dy=%d xy=%d best_far_pairs=%ld check=%ld iters=%ld acc=%ld secs=%.1f edges=%d\n",
           nn, K, DX, DY, XY, bestE, chk, it, acc, now() - t0, ecount);
    printf("STATE del:");
    for (int i = 0; i < K; i++) printf(" (%d,%d)", ea[best.del[i]], eb[best.del[i]]);
    printf(" xm=%x ym=%x\n", best.xm, best.ym);
    return 0;
}
