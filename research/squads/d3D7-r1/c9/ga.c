/* ga: memetic genetic algorithm over voltage lifts of cubic bipartite p+p base multigraphs (base and voltages free).
   Usage: ga p GROUPS id seed seconds [POP] [out.sol]
   Same lift model and cost as research/d3D7/salift.c (cost = #(base vertex, vertex) pairs at distance > 7).
   Individuals: 3p base edges (eu ev ea). Crossover: take the 3-edge blocks of white vertices 0..c-1 from parent A and the
   rest from parent B (whites are the sorting key), then repair black degrees by retargeting edges to underfull blacks.
   Child is improved by a short hill climb (salift moves, accept if not worse). Steady state: child replaces the worst
   individual if better. Writes out.sol (salift format) on cost 0. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <time.h>

#define MAXE 96
static int p, k, N, D = 7, *mul, *inv;
static uint64_t *R, *R2; static int *nbr;
static uint64_t rng = 88172645463325252ULL;
static inline uint64_t xr(void) { rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17; return rng; }
static inline double ur(void) { return (xr() >> 11) * (1.0 / 9007199254740992.0); }

typedef struct { int ne; int eu[MAXE], ev[MAXE], ea[MAXE]; long fit; } Ind;

static long cost(const Ind *I) {
    int ne = I->ne;
    for (int e = 0; e < ne; e++) for (int f = e + 1; f < ne; f++)
        if (I->eu[e] == I->eu[f] && I->ev[e] == I->ev[f] && I->ea[e] == I->ea[f]) return 1L << 40;
    int n = k * N, dg[64] = {0};
    static int dv[64][3], da[64][3];
    for (int e = 0; e < ne; e++) { int u = I->eu[e], v = I->ev[e];
        dv[u][dg[u]] = v; da[u][dg[u]++] = I->ea[e]; dv[v][dg[v]] = u; da[v][dg[v]++] = inv[I->ea[e]]; }
    for (int u = 0; u < k; u++) for (int g = 0; g < N; g++) for (int j = 0; j < 3; j++)
        nbr[(u * N + g) * 3 + j] = dv[u][j] * N + mul[g * N + da[u][j]];
    memset(R, 0, 8L * n);
    for (int u = 0; u < k; u++) R[u * N] = 1ULL << u;
    for (int t = 0; t < D; t++) {
        for (int x = 0; x < n; x++) R2[x] = R[x] | R[nbr[3 * x]] | R[nbr[3 * x + 1]] | R[nbr[3 * x + 2]];
        uint64_t *tmp = R; R = R2; R2 = tmp;
    }
    uint64_t full = k == 64 ? ~0ULL : (1ULL << k) - 1; long c = 0;
    for (int x = 0; x < n; x++) c += __builtin_popcountll(~R[x] & full);
    return c;
}

static void random_ind(Ind *I) {
    I->ne = 0;
    for (int m = 0; m < 3; m++) { int pm[32]; for (int i = 0; i < p; i++) pm[i] = i;
        for (int i = p - 1; i > 0; i--) { int j = xr() % (i + 1); int t = pm[i]; pm[i] = pm[j]; pm[j] = t; }
        for (int i = 0; i < p; i++) { I->eu[I->ne] = i; I->ev[I->ne] = p + pm[i]; I->ea[I->ne] = xr() % N; I->ne++; } }
    I->fit = cost(I);
}

/* one salift-style move; returns 0 if skipped */
static void move(Ind *I, Ind *undo) {
    *undo = *I;
    int ne = I->ne, i = xr() % ne, j = xr() % ne;
    if (xr() % 2) I->ea[i] = xr() % N;
    else { if (i == j || I->ev[i] == I->ev[j]) return; int t = I->ev[i]; I->ev[i] = I->ev[j]; I->ev[j] = t; if (xr() & 1) I->ea[i] = xr() % N; }
}

static void hill(Ind *I, int steps) {
    Ind u;
    for (int s = 0; s < steps && I->fit > 0; s++) {
        Ind c = *I; move(&c, &u); if (memcmp(&c, I, sizeof(Ind)) == 0) continue;
        c.fit = cost(&c);
        if (c.fit <= I->fit) *I = c;
    }
}

/* crossover + repair */
static void cross(const Ind *A, const Ind *B, Ind *C) {
    int ne = 3 * p; C->ne = 0;
    int cut = xr() % p;
    int dgb[64] = {0};
    /* whites 0..cut-1 from A, rest from B; each white contributes its 3 edges */
    for (int w = 0; w < p; w++) {
        const Ind *S = w < cut ? A : B;
        for (int e = 0; e < S->ne; e++) if (S->eu[e] == w) {
            C->eu[C->ne] = S->eu[e]; C->ev[C->ne] = S->ev[e]; C->ea[C->ne] = S->ea[e]; C->ne++; dgb[S->ev[e]]++; }
    }
    /* repair: black degree must be 3 each; retarget an edge into an overfull black to an underfull black it is not adjacent to */
    for (int tries = 0; tries < 10000; tries++) {
        int over = -1, under = -1;
        for (int b = p; b < k; b++) { if (dgb[b] > 3 && over < 0) over = b; if (dgb[b] < 3 && under < 0) under = b; }
        if (over < 0 && under < 0) break;
        if (over < 0 || under < 0) { C->fit = 1L << 40; return; }
        int cand[MAXE], nc = 0;
        for (int e = 0; e < C->ne; e++) if (C->ev[e] == over) {
            int ok = 1; for (int f = 0; f < C->ne; f++) if (C->eu[f] == C->eu[e] && C->ev[f] == under) ok = 0;
            if (ok) cand[nc++] = e; }
        if (nc == 0) { C->fit = 1L << 40; return; }
        int e = cand[xr() % nc];
        C->ev[e] = under; C->ea[e] = xr() % N; dgb[over]--; dgb[under]++;
    }
    C->fit = cost(C);
}

static void save(const Ind *I, const char *out) {
    FILE *f = fopen(out, "w"); fprintf(f, "%d %d %d\n", N, 0, p);
    for (int e = 0; e < I->ne; e++) fprintf(f, "%d %d %d\n", I->eu[e], I->ev[e], I->ea[e]); fclose(f);
}

int main(int argc, char **argv) {
    if (argc < 6) { fprintf(stderr, "usage: ga p GROUPS id seed seconds [POP] [out.sol]\n"); return 2; }
    p = atoi(argv[1]); k = 2 * p; int want = atoi(argv[3]);
    rng ^= (uint64_t)atoll(argv[4]) * 0x9E3779B97F4A7C15ULL; xr(); xr();
    double secs = atof(argv[5]);
    int POP = argc > 6 ? atoi(argv[6]) : 30;
    const char *out = argc > 7 ? argv[7] : "best.sol";
    if (getenv("D")) D = atoi(getenv("D"));
    FILE *fg = fopen(argv[2], "r"); char tag[8], name[256]; int gid, found = 0;
    while (fscanf(fg, "%7s %d %d %255s", tag, &N, &gid, name) == 4) {
        mul = malloc(sizeof(int) * N * N);
        for (int i = 0; i < N * N; i++) if (fscanf(fg, "%d", &mul[i]) != 1) return 3;
        if (gid == want) { found = 1; break; }
        free(mul);
    }
    if (!found) { fprintf(stderr, "group not found\n"); return 2; }
    inv = malloc(sizeof(int) * N);
    for (int a = 0; a < N; a++) for (int b = 0; b < N; b++) if (mul[a * N + b] == 0) inv[a] = b;
    int n = k * N; R = malloc(8L * n); R2 = malloc(8L * n); nbr = malloc(sizeof(int) * 3 * n);
    Ind *pop = malloc(sizeof(Ind) * POP); Ind best; best.fit = 1L << 41;
    for (int i = 0; i < POP; i++) { random_ind(&pop[i]); hill(&pop[i], 200); if (pop[i].fit < best.fit) best = pop[i]; }
    printf("group N=%d id=%d %s p=%d n=%d init best %ld\n", N, gid, name, p, n, best.fit); fflush(stdout);
    clock_t st = clock(); long gen = 0;
    while (best.fit > 0) {
        double el = (double)(clock() - st) / CLOCKS_PER_SEC; if (el > secs) break;
        gen++;
        int a = xr() % POP, b = xr() % POP, c2 = xr() % POP;
        int pa = pop[a].fit < pop[b].fit ? a : b; int pb = c2;  /* tournament of 2 + random partner */
        int worst = 0; for (int i = 1; i < POP; i++) if (pop[i].fit > pop[worst].fit) worst = i;
        Ind child; cross(&pop[pa], &pop[pb], &child);
        if (child.fit < (1L << 40)) {
            for (int s = 0; s < 3; s++) { Ind u; move(&child, &u); child.fit = cost(&child); }
            hill(&child, 300);
            if (child.fit < pop[worst].fit) pop[worst] = child;
            if (child.fit < best.fit) { best = child;
                printf("t=%.1f gen=%ld best %ld\n", el, gen, best.fit); fflush(stdout);
                if (best.fit == 0) { save(&best, out); printf("FOUND\n"); break; } }
        }
        /* restart the worst slot occasionally if the population has converged */
        if (gen % 2000 == 0) { int w = 0; for (int i = 1; i < POP; i++) if (pop[i].fit > pop[w].fit) w = i;
            random_ind(&pop[w]); hill(&pop[w], 200); }
    }
    if (best.fit > 0) save(&best, out);
    printf("end best %ld gens %ld\n", best.fit, gen);
    return 0;
}
