/* tabu.c (card c8, squad s384r1): tabu search for 6-subsets S = {e} u T of a group G (table format of
 * research/six-five-384/src/haarex4.c: N, N x N table with identity 0, then automorphisms, ignored here).
 * Cost(S) = |G \ (S^-1 S)^2| + |G \ (S S^-1)^2|  (0 means the Haar graph H(G,S) has diameter <= 5, 768 vertices
 * for N = 384). Moves: replace one non-identity element of S by a non-member. Tabu: a removed element may not be
 * re-added for a random tenure; aspiration when a move beats the best cost of the run. Restart from a random S
 * after RESTART non-improving iterations (of the restart). Time budget per group.
 * usage: tabu SECS SEED FILE...     prints one line per file: best cost, S (element indices), time of best,
 *        iterations, and "ZERO" lines when cost 0 is reached (then the search stops for that file).
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <limits.h>
#include <time.h>

#define K 6
static int RESTART = 60;

static int N;
static int *M, *INV;
static unsigned *stamp;
static unsigned gen = 0;
static uint64_t rs = 88172645463325252ULL;

static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }
static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndint(int n) { return (int)(rnd() % (uint64_t)n); }

static int load(const char *fn) {
    FILE *f = fopen(fn, "r");
    if (!f) return 0;
    if (fscanf(f, "%d", &N) != 1 || N < 2 || N > 4096) { fclose(f); return 0; }
    free(M); free(INV); free(stamp);
    M = malloc(sizeof(int) * N * N); INV = malloc(sizeof(int) * N); stamp = calloc(N, sizeof(unsigned)); gen = 0;
    for (int i = 0; i < N * N; i++) if (fscanf(f, "%d", &M[i]) != 1) { fclose(f); return 0; }
    fclose(f);
    for (int a = 0; a < N; a++) for (int b = 0; b < N; b++) if (M[a * N + b] == 0) INV[a] = b;
    return 1;
}

/* number of elements of G not in the set {Q[i] Q[j]} */
static int missing(const int *Q, int nq) {
    if (++gen == 0) { memset(stamp, 0, sizeof(unsigned) * N); gen = 1; }
    int cnt = 0;
    for (int i = 0; i < nq; i++) {
        const int *row = M + Q[i] * N;
        for (int j = 0; j < nq; j++) { int x = row[Q[j]]; if (stamp[x] != gen) { stamp[x] = gen; cnt++; } }
    }
    return N - cnt;
}

static int cost(const int *S) {
    int P[K * K + 1], np = 0;
    for (int i = 0; i < K; i++) for (int j = 0; j < K; j++) if (i != j) P[np++] = M[INV[S[i]] * N + S[j]];
    P[np++] = 0;
    int c1 = missing(P, np);
    np = 0;
    for (int i = 0; i < K; i++) for (int j = 0; j < K; j++) if (i != j) P[np++] = M[S[i] * N + INV[S[j]]];
    P[np++] = 0;
    return c1 + missing(P, np);
}

static int inset(const int *S, int u) { for (int i = 0; i < K; i++) if (S[i] == u) return 1; return 0; }

static void pr_set(const int *S) { printf("S ="); for (int i = 0; i < K; i++) printf(" %d", S[i]); }

static int tabu_until[4096];

/* returns best cost found in this file; bestS, tbest (time of best), its(total moves) */
static int search(double secs, int *bestS, double *tbest, long *its, int *zero_found) {
    double t0 = now();
    int best = INT_MAX;
    long it = 0;
    *zero_found = 0;
    for (int i = 0; i < N; i++) tabu_until[i] = 0;
    int S[K];
    while (now() - t0 < secs) {
        S[0] = 0;
        for (int i = 1; i < K; i++) { int u; do { u = 1 + rndint(N - 1); } while (inset(S, u)); S[i] = u; }
        int cur = cost(S), lbest = cur;
        long lastimp = it;
        while (it - lastimp < RESTART) {
            if ((it & 15) == 0 && now() - t0 >= secs) break;
            it++;
            int bp = -1, bu = -1, bc = INT_MAX, nties = 0;
            for (int p = 1; p < K; p++) {
                int x = S[p];
                for (int u = 1; u < N; u++) {
                    if (inset(S, u)) continue;
                    S[p] = u; int c = cost(S); S[p] = x;
                    int tabu = tabu_until[u] > it;
                    if (tabu && c >= best) continue;      /* aspiration: beat the run's best */
                    if (c < bc) { bc = c; bp = p; bu = u; nties = 1; }
                    else if (c == bc && rndint(++nties) == 0) { bp = p; bu = u; }
                }
            }
            if (bp < 0) { /* every move tabu and none aspirates: random move */
                int p = 1 + rndint(K - 1), u;
                do { u = 1 + rndint(N - 1); } while (inset(S, u));
                tabu_until[S[p]] = (int)(it + 7 + rndint(8));
                S[p] = u; cur = cost(S);
            } else {
                tabu_until[S[bp]] = (int)(it + 7 + rndint(8));
                S[bp] = bu; cur = bc;
            }
            if (cur < lbest) { lbest = cur; lastimp = it; }
            if (cur < best) {
                best = cur; memcpy(bestS, S, sizeof S); *tbest = now() - t0;
                if (best == 0) { *zero_found = 1; *its = it; return 0; }
            }
        }
    }
    *its = it;
    return best;
}

int main(int argc, char **argv) {
    if (argc < 4) { fprintf(stderr, "usage: tabu SECS SEED FILE...\n"); return 1; }
    double secs = atof(argv[1]);
    if (getenv("RESTART")) RESTART = atoi(getenv("RESTART"));
    rs ^= (uint64_t)atoll(argv[2]) * 0x9E3779B97F4A7C15ULL; if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();
    for (int a = 3; a < argc; a++) {
        if (!load(argv[a])) { printf("%s LOADFAIL\n", argv[a]); continue; }
        int bestS[K]; double tbest = -1; long its = 0; int z = 0;
        int best = search(secs, bestS, &tbest, &its, &z);
        printf("%s N=%d best=%d ", argv[a], N, best);
        pr_set(bestS);
        printf(" tbest=%.2f iters=%ld %s\n", tbest, its, z ? "ZERO" : "");
        fflush(stdout);
    }
    return 0;
}
