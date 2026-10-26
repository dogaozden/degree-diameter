/* c37 wildcard: 4-regular bipartite graph on A=Z_N, B=Z_N with x_A ~ (a_i x + b_i)_B, i=1..4,
   a_i units mod N (affine permutations). Simulated annealing over the 8 parameters.
   Cost = unordered pairs at distance > 8 (bit-parallel BFS from all 2N sources). */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>
#include <math.h>

#define MAXV 4400
static int N, V, W;
static int A_[4], B_[4];
static int P[4][2048], Q[4][2048];
static int units[2048], nunits;
static uint64_t *R0, *R1;
static uint64_t rs;

static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static double urand(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }
static int gcd(int a, int b) { while (b) { int t = a % b; a = b; b = t; } return a; }

static void build(void) {
    for (int i = 0; i < 4; i++) {
        for (int x = 0; x < N; x++) P[i][x] = (int)(((long long)A_[i] * x + B_[i]) % N);
        for (int x = 0; x < N; x++) Q[i][P[i][x]] = x;
    }
}
/* simple graph check: the four images of each x must be distinct */
static int simple_ok(void) {
    for (int x = 0; x < N; x++)
        for (int i = 0; i < 4; i++)
            for (int j = i + 1; j < 4; j++)
                if (P[i][x] == P[j][x]) return 0;
    return 1;
}
static inline int nb(int v, int i) { return v < N ? N + P[i][v] : Q[i][v - N]; }

/* returns unordered far pairs (distance > 8) */
static long far_cost(void) {
    memset(R0, 0, sizeof(uint64_t) * V * W);
    for (int v = 0; v < V; v++) R0[(size_t)v * W + v / 64] |= 1ULL << (v % 64);
    for (int step = 0; step < 8; step++) {
        for (int v = 0; v < V; v++) {
            uint64_t *dst = R1 + (size_t)v * W;
            uint64_t *src = R0 + (size_t)v * W;
            memcpy(dst, src, sizeof(uint64_t) * W);
            for (int i = 0; i < 4; i++) {
                uint64_t *s = R0 + (size_t)nb(v, i) * W;
                for (int w = 0; w < W; w++) dst[w] |= s[w];
            }
        }
        uint64_t *t = R0; R0 = R1; R1 = t;
    }
    long tot = 0;
    for (size_t k = 0; k < (size_t)V * W; k++) tot += __builtin_popcountll(R0[k]);
    long far_ordered = (long)V * V - tot;
    return far_ordered / 2;
}

static void rand_unit(int *a) {
    *a = units[rnd() % nunits];
}

static void write_edges(const char *fn) {
    FILE *f = fopen(fn, "w");
    if (!f) return;
    build();
    fprintf(f, "%d\n", V);
    for (int x = 0; x < N; x++)
        for (int i = 0; i < 4; i++) fprintf(f, "%d %d\n", x, N + P[i][x]);
    fclose(f);
}

int main(int argc, char **argv) {
    if (argc < 6) { fprintf(stderr, "usage: aff N SECONDS SEED T0 T1 [OUT.edges]\n"); return 1; }
    N = atoi(argv[1]);
    double secs = atof(argv[2]);
    rs = (uint64_t)atoll(argv[3]) * 2654435761ULL + 88172645463325252ULL;
    double T0 = atof(argv[4]), T1 = atof(argv[5]);
    const char *out = argc > 6 ? argv[6] : NULL;
    V = 2 * N; W = (V + 63) / 64;
    R0 = malloc(sizeof(uint64_t) * V * W);
    R1 = malloc(sizeof(uint64_t) * V * W);
    nunits = 0;
    for (int u = 1; u < N; u++) if (gcd(u, N) == 1) units[nunits++] = u;
    units[nunits++] = 1 % N; /* identity slope is allowed (may be duplicate) */
    /* random simple start */
    do {
        for (int i = 0; i < 4; i++) { rand_unit(&A_[i]); B_[i] = rnd() % N; }
        build();
    } while (!simple_ok());
    long cur = far_cost();
    long best = cur; int bA[4], bB[4];
    memcpy(bA, A_, sizeof bA); memcpy(bB, B_, sizeof bB);
    long evals = 1;
    clock_t c0 = clock();
    double el = 0;
    while (1) {
        el = (double)(clock() - c0) / CLOCKS_PER_SEC;
        if (el >= secs) break;
        double frac = el / secs;
        double T = T0 * pow(T1 / T0, frac);
        int i = rnd() % 4;
        int oa = A_[i], ob = B_[i];
        if (rnd() & 1) rand_unit(&A_[i]); else B_[i] = rnd() % N;
        build();
        if (!simple_ok()) { A_[i] = oa; B_[i] = ob; build(); continue; }
        long c = far_cost(); evals++;
        if (c <= cur || urand() < exp((double)(cur - c) / T)) {
            cur = c;
            if (c < best) { best = c; memcpy(bA, A_, sizeof bA); memcpy(bB, B_, sizeof bB); }
        } else {
            A_[i] = oa; B_[i] = ob; build();
        }
        if (best == 0) break;
    }
    el = (double)(clock() - c0) / CLOCKS_PER_SEC;
    memcpy(A_, bA, sizeof bA); memcpy(B_, bB, sizeof bB); build();
    printf("RESULT N=%d n=%d best_far=%ld miss=%.4f evals=%ld time=%.1f a=[%d,%d,%d,%d] b=[%d,%d,%d,%d]\n",
           N, V, best, 2.0 * best / V, evals, el, bA[0], bA[1], bA[2], bA[3], bB[0], bB[1], bB[2], bB[3]);
    if (out) { write_edges(out); printf("WROTE %s\n", out); }
    return 0;
}
