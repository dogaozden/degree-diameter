// c10: structure-free edge-swap annealing on bipartite 6-regular graphs, N+N vertices.
// Cost = number of same-side ordered pairs at distance > 4 (both sides).
// Ball computation with bitsets: P2[x] = union over y in N(x), x' in N(y) of P1[x'], P1[x] = union over y in N(x) of N(y).
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>
#define MAXN 512
#define D 6
#define W 8
static int N, WN;
static int adjA[MAXN][D], adjB[MAXN][D];
static uint64_t Bset[MAXN][W], P1[MAXN][W], P2[MAXN][W];

static uint64_t rng_s = 88172645463325252ULL;
static inline uint64_t rnd(void) { rng_s ^= rng_s << 13; rng_s ^= rng_s >> 7; rng_s ^= rng_s << 17; return rng_s; }
static inline double urand(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

// generic side cost: X vertices with adjX (X->Y), Y vertices with adjY (Y->X)
static int sidecost(int NX, int adjX[][D], int adjY[][D]) {
    for (int y = 0; y < NX; y++) {           // Bset[y] over X of N(y); NX==N same size
        memset(Bset[y], 0, sizeof(Bset[y]));
        for (int k = 0; k < D; k++) { int x = adjY[y][k]; Bset[y][x >> 6] |= 1ULL << (x & 63); }
    }
    for (int x = 0; x < NX; x++) {
        for (int w = 0; w < WN; w++) P1[x][w] = 0;
        for (int k = 0; k < D; k++) { int y = adjX[x][k]; for (int w = 0; w < WN; w++) P1[x][w] |= Bset[y][w]; }
    }
    int cost = 0;
    for (int x = 0; x < NX; x++) {
        uint64_t acc[W] = {0};
        for (int k = 0; k < D; k++) {
            int y = adjX[x][k];
            for (int j = 0; j < D; j++) {
                int x2 = adjY[y][j];
                for (int w = 0; w < WN; w++) acc[w] |= P1[x2][w];
            }
        }
        int pc = 0;
        for (int w = 0; w < WN; w++) pc += __builtin_popcountll(acc[w]);
        cost += N - pc;
    }
    return cost;
}
static int fullcost(void) { return sidecost(N, adjA, adjB) + sidecost(N, adjB, adjA); }

static int has_edge(int a, int b) { for (int k = 0; k < D; k++) if (adjA[a][k] == b) return 1; return 0; }
// set adjacency entry: A-vertex a slot i now points to b; B-vertex b's slot holding a gets replaced
static void setA(int a, int i, int b) {
    int old = adjA[a][i];
    adjA[a][i] = b;
    for (int k = 0; k < D; k++) if (adjB[old][k] == a) { adjB[old][k] = -1; break; }
    for (int k = 0; k < D; k++) if (adjB[b][k] == -1) { adjB[b][k] = a; break; }
}
static void write_edges(const char *fn) {
    FILE *f = fopen(fn, "w"); if (!f) return;
    fprintf(f, "%d\n", 2 * N);
    for (int a = 0; a < N; a++) for (int k = 0; k < D; k++) fprintf(f, "%d %d\n", a, N + adjA[a][k]);
    fclose(f);
}

int main(int argc, char **argv) {
    N = argc > 1 ? atoi(argv[1]) : 343;
    long iters = argc > 2 ? atol(argv[2]) : 1000000;
    double T0 = argc > 3 ? atof(argv[3]) : 3.0, T1 = argc > 4 ? atof(argv[4]) : 0.2;
    rng_s ^= (uint64_t)(argc > 5 ? atol(argv[5]) : 1) * 0x9E3779B97F4A7C15ULL;
    const char *out = argc > 6 ? argv[6] : "best.edges";
    WN = (N + 63) / 64;
    // start: circulant (mixed afterwards by 2-switches at high temperature)
    for (int a = 0; a < N; a++) for (int k = 0; k < D; k++) { adjA[a][k] = (a + k) % N; }
    for (int b = 0; b < N; b++) for (int k = 0; k < D; k++) { adjB[b][k] = (b - k + N) % N; }
    int cur = fullcost(), best = cur;
    printf("start cost %d\n", cur); fflush(stdout);
    time_t t0 = time(NULL);
    long acc = 0;
    for (long it = 0; it < iters; it++) {
        double T = T0 * pow(T1 / T0, (double)it / iters);
        int a1 = rnd() % N, i = rnd() % D, a2 = rnd() % N, j = rnd() % D;
        if (a1 == a2) continue;
        int b1 = adjA[a1][i], b2 = adjA[a2][j];
        if (b1 == b2 || has_edge(a1, b2) || has_edge(a2, b1)) continue;
        setA(a1, i, b2); setA(a2, j, b1);
        int nc = fullcost();
        int delta = nc - cur;
        if (delta <= 0 || urand() < exp(-delta / T)) {
            cur = nc; acc++;
            if (cur < best) { best = cur; write_edges(out); }
            if (cur == 0) break;
        } else {
            setA(a1, i, b1); setA(a2, j, b2);
        }
        if (it % 20000 == 0) { printf("it %ld T %.3f cur %d best %d acc %ld t %lds\n", it, T, cur, best, acc, (long)(time(NULL)-t0)); fflush(stdout); }
    }
    printf("final best %d\n", best);
    return 0;
}
