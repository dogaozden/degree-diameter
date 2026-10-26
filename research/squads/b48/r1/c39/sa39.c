// c39 (wildcard C): simulated annealing over simple 4-regular bipartite graphs, NO group, NO Cayley structure.
// Moves: bipartite 2-switches (a1b1,a2b2 -> a1b2,a2b1), keeping simple and 4-regular.
// Energy: number of unordered pairs at distance > 8 (bit-parallel ball BFS, exact).
// usage: sa39 SECONDS SEED T0 T1 OUT.edges     (n = 2*HH = 2186)
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define HH 1093
#define NV (2 * HH)
#define W ((NV + 63) / 64)
#define DEG 4
#define NE (NV * DEG / 2)
#define RAD 8

static int adj[NV][DEG];
static int ea[NE], eb[NE];
static int best_ea[NE], best_eb[NE];
static uint64_t bufA[NV * W], bufB[NV * W];

static uint64_t rs[2];
static inline uint64_t rnd(void) {
    uint64_t s1 = rs[0];
    const uint64_t s0 = rs[1];
    rs[0] = s0;
    s1 ^= s1 << 23;
    rs[1] = s1 ^ s0 ^ (s1 >> 18) ^ (s0 >> 5);
    return rs[1] + s0;
}
static inline double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + 1e-9 * ts.tv_nsec;
}

static int has(int v, int w) {
    for (int d = 0; d < DEG; d++)
        if (adj[v][d] == w) return 1;
    return 0;
}

static void replace(int v, int oldw, int neww) {
    for (int d = 0; d < DEG; d++)
        if (adj[v][d] == oldw) { adj[v][d] = neww; return; }
    fprintf(stderr, "replace failed\n");
    exit(2);
}

// edge e1 = (a1,b1), e2 = (a2,b2) -> e1 = (a1,b2), e2 = (a2,b1). Self-inverse call pattern.
static void sw(int e1, int e2) {
    int a1 = ea[e1], b1 = eb[e1], a2 = ea[e2], b2 = eb[e2];
    replace(a1, b1, b2);
    replace(b1, a1, a2);
    replace(a2, b2, b1);
    replace(b2, a2, a1);
    eb[e1] = b2;
    eb[e2] = b1;
}

static long far_pairs(void) {
    uint64_t *cur = bufA, *nxt = bufB;
    memset(cur, 0, sizeof(uint64_t) * NV * W);
    for (int v = 0; v < NV; v++) cur[(size_t)v * W + v / 64] |= 1ULL << (v % 64);
    for (int k = 0; k < RAD; k++) {
        for (int v = 0; v < NV; v++) {
            uint64_t *o = nxt + (size_t)v * W;
            memcpy(o, cur + (size_t)v * W, sizeof(uint64_t) * W);
            for (int d = 0; d < DEG; d++) {
                const uint64_t *s = cur + (size_t)adj[v][d] * W;
                for (int i = 0; i < W; i++) o[i] |= s[i];
            }
        }
        uint64_t *t = cur; cur = nxt; nxt = t;
    }
    long reach = 0;
    for (int v = 0; v < NV; v++)
        for (int i = 0; i < W; i++) reach += __builtin_popcountll(cur[(size_t)v * W + i]);
    long far_ord = (long)NV * NV - reach;
    return far_ord / 2;
}

// random simple 4-regular bipartite graph as union of 4 random perfect matchings (rejection)
static void make_init(void) {
    int perm[HH];
    for (;;) {
        int ok = 1;
        for (int j = 0; j < DEG && ok; j++) {
            for (int a = 0; a < HH; a++) perm[a] = a;
            for (int a = HH - 1; a > 0; a--) {
                int r = rnd() % (a + 1);
                int t = perm[a]; perm[a] = perm[r]; perm[r] = t;
            }
            for (int a = 0; a < HH && ok; a++) {
                int b = HH + perm[a];
                for (int d = 0; d < j; d++) if (adj[a][d] == b) { ok = 0; break; }
                if (!ok) break;
                adj[a][j] = b;
                adj[b][j] = a;
                ea[j * HH + a] = a;
                eb[j * HH + a] = b;
            }
        }
        if (ok) return;
    }
}

int main(int argc, char **argv) {
    if (argc < 6) { fprintf(stderr, "usage: sa39 SECONDS SEED T0 T1 OUT.edges\n"); return 1; }
    double secs = atof(argv[1]);
    uint64_t seed = strtoull(argv[2], 0, 10);
    double T0 = atof(argv[3]), T1 = atof(argv[4]);
    const char *out = argv[5];
    rs[0] = seed * 0x9E3779B97F4A7C15ULL + 12345; rs[1] = (seed + 7) * 0xBF58476D1CE4E5B9ULL + 999;
    for (int i = 0; i < 20; i++) rnd();

    make_init();
    long E = far_pairs(), best = E;
    memcpy(best_ea, ea, sizeof ea); memcpy(best_eb, eb, sizeof eb);
    printf("init far_pairs=%ld\n", E);
    fflush(stdout);

    double t0 = now();
    long evals = 0, acc = 0;
    for (;;) {
        double el = now() - t0;
        if (el >= secs || E == 0) break;
        double T = T0 * pow(T1 / T0, el / secs);
        int e1 = rnd() % NE, e2 = rnd() % NE;
        if (e1 == e2) continue;
        int a1 = ea[e1], b1 = eb[e1], a2 = ea[e2], b2 = eb[e2];
        if (has(a1, b2) || has(a2, b1)) continue;
        sw(e1, e2);
        long E2 = far_pairs();
        evals++;
        long dE = E2 - E;
        if (dE <= 0 || rnd01() < exp(-(double)dE / T)) {
            E = E2; acc++;
            if (E < best) {
                best = E;
                memcpy(best_ea, ea, sizeof ea); memcpy(best_eb, eb, sizeof eb);
            }
        } else {
            sw(e1, e2);
        }
        if (evals % 5000 == 0) {
            printf("t=%.1f evals=%ld acc=%ld T=%.3f E=%ld best=%ld\n", el, evals, acc, T, E, best);
            fflush(stdout);
        }
    }
    printf("done evals=%ld acc=%ld E=%ld best=%ld time=%.1f\n", evals, acc, E, best, now() - t0);

    FILE *f = fopen(out, "w");
    if (!f) { perror("open"); return 1; }
    fprintf(f, "%d\n", NV);
    for (int e = 0; e < NE; e++) fprintf(f, "%d %d\n", best_ea[e], best_eb[e]);
    fclose(f);
    printf("best_far_pairs=%ld miss=%.4f\n", best, 2.0 * best / NV);
    return 0;
}
