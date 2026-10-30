/* tabu.c (card c2, squad d75-r1): TABU search over non-symmetric S (|S| = 7, S[0] = identity) for Haar graphs
 * H(G,S) on a group given by the multiplication table of research/d75-raise/src/export.g.
 * Table loader and cost()/fullcheck() copied from research/d75-raise/src/haar75.c.
 * cost = |G \ XX| + |G \ YY|, X = S^-1 S, Y = S S^-1 (cost 0 is then checked for the odd condition YY S = G).
 * Move: replace S[i] (i >= 1) by an element v not in S. Neighbourhood: all 6(n-7) moves, or SAMPLE random moves.
 * Tabu: after S[i]: old -> v, inserting old back into slot i is tabu for TEN + rand(0..4) iterations.
 * Aspiration: a tabu move is allowed if it beats the global best. Restart from random S after STALL iterations
 * without improvement of the restart best.
 * env: SECS (wall clock, default 800), SEED (1), TEN (15), STALL (2000), SAMPLE (0 = full neighbourhood),
 *      EDGES=file (writes the edge list of the first valid solution).
 * usage: tabu FILE.ht
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

static int n, ninv;
static uint16_t *mul;
static int *inv;
#define M(a,b) mul[(size_t)(a) * n + (b)]
static uint32_t *stA, *stB; static uint32_t sA = 0, sB = 0;
static long long evals = 0;

static int rdint(FILE *f) { int x; if (fscanf(f, "%d", &x) != 1) { fprintf(stderr, "read error\n"); exit(1); } return x; }

static void load(const char *path) {
    FILE *f = fopen(path, "r"); if (!f) { perror(path); exit(1); }
    n = rdint(f); ninv = rdint(f);
    mul = malloc(sizeof(uint16_t) * n * n); inv = malloc(sizeof(int) * n);
    for (int i = 0; i < n * n; i++) mul[i] = rdint(f);
    for (int i = 0; i < n; i++) inv[i] = rdint(f);
    fclose(f);
    stA = calloc(n, sizeof(uint32_t)); stB = calloc(n, sizeof(uint32_t));
    for (int i = 0; i < n; i++) if (M(0, i) != i || M(i, 0) != i || M(i, inv[i]) != 0) { fprintf(stderr, "bad table\n"); exit(1); }
}

/* uncovered count of XX (left=1: X = {a^-1 b}) or YY (left=0: Y = {a b^-1}) */
static int uncov(const int *S, int k, int left) {
    int X[64], nx = 0;
    sB++;
    for (int i = 0; i < k; i++) for (int j = 0; j < k; j++) {
        int x = left ? M(inv[S[i]], S[j]) : M(S[i], inv[S[j]]);
        if (stB[x] != sB) { stB[x] = sB; X[nx++] = x; }
    }
    sA++; int cov = 0;
    for (int i = 0; i < nx; i++) { const uint16_t *row = mul + (size_t)X[i] * n;
        for (int j = 0; j < nx; j++) { int z = row[X[j]]; if (stA[z] != sA) { stA[z] = sA; cov++; } } }
    return n - cov;
}
static int cost(const int *S, int k) { evals++; return uncov(S, k, 1) + uncov(S, k, 0); }

/* cost 0 plus distinct S plus odd condition YY S = G */
static int fullcheck(const int *S, int k) {
    if (cost(S, k) != 0) return 0;
    for (int i = 0; i < k; i++) for (int j = i + 1; j < k; j++) if (S[i] == S[j]) return 0;
    int Y[64], ny = 0; sB++;
    for (int i = 0; i < k; i++) for (int j = 0; j < k; j++) { int x = M(S[i], inv[S[j]]); if (stB[x] != sB) { stB[x] = sB; Y[ny++] = x; } }
    char *yy = calloc(n, 1), *odd = calloc(n, 1);
    for (int i = 0; i < ny; i++) for (int j = 0; j < ny; j++) yy[M(Y[i], Y[j])] = 1;
    for (int z = 0; z < n; z++) if (yy[z]) for (int i = 0; i < k; i++) odd[M(z, S[i])] = 1;
    int ok = 1; for (int z = 0; z < n; z++) if (!odd[z]) ok = 0;
    free(yy); free(odd); return ok;
}

static uint64_t rs = 88172645463325252ULL;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }

int main(int argc, char **argv) {
    if (argc < 2) { fprintf(stderr, "usage: tabu FILE.ht\n"); return 2; }
    load(argv[1]);
    double secs = getenv("SECS") ? atof(getenv("SECS")) : 800;
    int seed = getenv("SEED") ? atoi(getenv("SEED")) : 1;
    int ten = getenv("TEN") ? atoi(getenv("TEN")) : 15;
    long long stall_max = getenv("STALL") ? atoll(getenv("STALL")) : 2000;
    int sample = getenv("SAMPLE") ? atoi(getenv("SAMPLE")) : 0;
    const char *edges_out = getenv("EDGES");
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 10; i++) rnd();
    printf("GROUP %s n %d ninv %d secs %.0f ten %d stall %lld sample %d seed %d\n", argv[1], n, ninv, secs, ten, stall_max, sample, seed);
    fflush(stdout);

    const int K = 7;
    int S[7], bestS[7];
    int gbest = 1 << 30;
    char *inS = calloc(n, 1);
    long long *tabu = calloc((size_t)K * n, sizeof(long long));
    long long it = 0; long long zero_nonodd = 0;
    int restarts = 0, done = 0, found = 0;
    time_t t0 = time(NULL);
    while (!done) {
        restarts++;
        memset(inS, 0, n); S[0] = 0; inS[0] = 1;
        for (int i = 1; i < K; i++) { int v; do { v = 1 + rnd() % (n - 1); } while (inS[v]); S[i] = v; inS[v] = 1; }
        int cur = cost(S, K), rbest = cur; long long stall = 0;
        while (stall < stall_max) {
            if ((it & 63) == 0 && difftime(time(NULL), t0) > secs) { done = 1; break; }
            it++;
            int bc = 1 << 30, bi = -1, bv = -1, nties = 0;
            long long ntot = sample > 0 ? sample : (long long)(K - 1) * (n - 1);
            for (long long m = 0; m < ntot; m++) {
                int i, v;
                if (sample > 0) { i = 1 + rnd() % (K - 1); v = 1 + rnd() % (n - 1); }
                else { i = 1 + (int)(m / (n - 1)); v = 1 + (int)(m % (n - 1)); }
                if (inS[v]) continue;
                int old = S[i];
                S[i] = v; int c = cost(S, K); S[i] = old;
                if (tabu[(size_t)i * n + v] > it && c >= gbest) continue;   /* tabu unless aspiration */
                if (c < bc) { bc = c; bi = i; bv = v; nties = 1; }
                else if (c == bc) { nties++; if (rnd() % nties == 0) { bi = i; bv = v; } }
            }
            if (bi < 0) break;   /* everything tabu: restart */
            int old = S[bi];
            tabu[(size_t)bi * n + old] = it + ten + (long long)(rnd() % 5);
            inS[old] = 0; S[bi] = bv; inS[bv] = 1; cur = bc;
            if (cur < rbest) { rbest = cur; stall = 0; } else stall++;
            if (cur < gbest) {
                gbest = cur; memcpy(bestS, S, sizeof S);
                printf("BEST cost %d it %lld restart %d secs %.0f set", gbest, it, restarts, difftime(time(NULL), t0));
                for (int i = 0; i < K; i++) printf(" %d", S[i]);
                printf("\n"); fflush(stdout);
            }
            if (cur == 0) {
                if (fullcheck(S, K)) {
                    printf("VALID cost 0 it %lld set", it); for (int i = 0; i < K; i++) printf(" %d", S[i]); printf("\n");
                    fflush(stdout);
                    memcpy(bestS, S, sizeof S); found = 1;
                    if (edges_out) {
                        FILE *f = fopen(edges_out, "w"); fprintf(f, "%d\n", 2 * n);
                        for (int g = 0; g < n; g++) for (int i = 0; i < K; i++) fprintf(f, "%d %d\n", g, n + M(S[i], g));
                        fclose(f);
                    }
                    done = 1; break;
                } else zero_nonodd++;
            }
        }
    }
    printf("DONE restarts %d iters %lld evals %lld best %d zero_without_odd %lld found %d set", restarts, it, evals, gbest, zero_nonodd, found);
    for (int i = 0; i < K; i++) printf(" %d", bestS[i]);
    printf("\n");
    return 0;
}
