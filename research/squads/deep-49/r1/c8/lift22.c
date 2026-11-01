/* lift22.c: 2+2 voltage lifts of metacyclic groups G = Z_m x|_r Z_k (wildcard card c8, deep-49 round 1).

   Base graph: two vertex orbits per side, multiplicity matrix [[a, 4-a], [4-a, a]] (a = 1 or 2).
   Vertices: A_{i,g} = i*N + g (i in {0,1}), B_{j,h} = 2N + j*N + h, N = |G| = m*k, n = 4N.
   Edges: A_{i,g} ~ B_{j,g*s} for every s in S_ij (|S_ij| = base multiplicity).
   Normalisation: 1 is in S_00, S_01, S_10 (spanning tree of the base graph; relabelling shows this is WLOG).
   Left translation by G is an automorphism, so the graph has diameter <= 9 iff BFS from the four orbit
   representatives A_0, A_1, B_0, B_1 (identity element) reaches everything within distance 9.
   cost = sum over the 4 representatives of #vertices at distance > 9 (0 iff diameter <= 9).

   Group element e = x*K + y, (x1,y1)(x2,y2) = (x1 + r^y1 x2 mod m, y1+y2 mod k); identity 0.

   Usage: lift22 GROUPFILE FIRSTLINE LASTLINE SECONDS_PER_RUN SEED [EDGEDIR]
   GROUPFILE lines: "m k r" (0-based line numbers FIRSTLINE..LASTLINE). Each group: a=2 run, then a=1 run.
   Simulated annealing over the 5 free voltages with restarts. Prints one line per run:
     RES m k r a N best evals seconds
   If best == 0 the edge list is written to EDGEDIR/lift_m<m>_k<k>_r<r>_a<a>.edges (0-based, first line n). */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <stdint.h>
#include <limits.h>
#include <time.h>

static int M, K, R, N, NV;
static int *mul, *inv_, *rp;
static int *X, *Y;
static int A;
static int sz[2][2];
static int L[2][2][4];
static int freei[5], freej[5], freet[5];
static int nf;
static int *dist, *queue;
static int Aj[2][4], As[2][4];
static int Bi[2][4], Bs[2][4];

static uint64_t rs = 88172645463325252ULL;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline int rndint(int n) { return (int)(rnd() % (uint64_t)n); }
static inline double urand(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }

static void build_group(void) {
    N = M * K; NV = 4 * N;
    rp = malloc(sizeof(int) * K);
    rp[0] = 1;
    for (int y = 1; y < K; y++) rp[y] = (int)((long)rp[y - 1] * R % M);
    if ((long)rp[K - 1] * R % M != 1) { fprintf(stderr, "r^k != 1 mod m\n"); exit(1); }
    mul = malloc(sizeof(int) * (size_t)N * N);
    for (int a = 0; a < N; a++) {
        int x1 = a / K, y1 = a % K;
        for (int b = 0; b < N; b++) {
            int x2 = b / K, y2 = b % K;
            int x = (int)((x1 + (long)rp[y1] * x2) % M);
            int y = (y1 + y2) % K;
            mul[(size_t)a * N + b] = x * K + y;
        }
    }
    inv_ = malloc(sizeof(int) * N);
    for (int a = 0; a < N; a++)
        for (int b = 0; b < N; b++)
            if (mul[(size_t)a * N + b] == 0) { inv_[a] = b; break; }
    dist = malloc(sizeof(int) * NV);
    queue = malloc(sizeof(int) * NV);
    X = malloc(sizeof(int) * N); Y = malloc(sizeof(int) * N);
    for (int e = 0; e < N; e++) { X[e] = e / K; Y[e] = e % K; }
}

static inline int mulfast(int g, int s) {
    int x = (X[g] + rp[Y[g]] * X[s]) % M;
    int y = Y[g] + Y[s];
    if (y >= K) y -= K;
    return x * K + y;
}

static void free_group(void) {
    free(mul); free(inv_); free(rp); free(dist); free(queue); free(X); free(Y);
}

static void setup_family(int a) {
    A = a;
    if (a == 2) { sz[0][0] = sz[0][1] = sz[1][0] = sz[1][1] = 2; }
    else { sz[0][0] = 1; sz[0][1] = 3; sz[1][0] = 3; sz[1][1] = 1; }
    nf = 0;
    for (int i = 0; i < 2; i++)
        for (int j = 0; j < 2; j++)
            for (int t = 0; t < sz[i][j]; t++) {
                int fixed0 = (t == 0 && !(i == 1 && j == 1));
                if (fixed0) L[i][j][t] = 0;
                else { freei[nf] = i; freej[nf] = j; freet[nf] = t; L[i][j][t] = -1; nf++; }
            }
}

static int ok_val(int f, int v) {
    int i = freei[f], j = freej[f], t = freet[f];
    for (int u = 0; u < sz[i][j]; u++)
        if (u != t && L[i][j][u] == v) return 0;
    return 1;
}

static void build_adj(void) {
    for (int i = 0; i < 2; i++) {
        int c = 0;
        for (int j = 0; j < 2; j++)
            for (int t = 0; t < sz[i][j]; t++) { Aj[i][c] = j; As[i][c] = L[i][j][t]; c++; }
    }
    for (int j = 0; j < 2; j++) {
        int c = 0;
        for (int i = 0; i < 2; i++)
            for (int t = 0; t < sz[i][j]; t++) { Bi[j][c] = i; Bs[j][c] = inv_[L[i][j][t]]; c++; }
    }
}

static void randomize(void) {
    for (int f = 0; f < nf; f++) {
        int v;
        do { v = rndint(N); } while (!ok_val(f, v));
        L[freei[f]][freej[f]][freet[f]] = v;
    }
    build_adj();
}

static int far_from(int src) {
    for (int v = 0; v < NV; v++) dist[v] = -1;
    int head = 0, tail = 0;
    queue[tail++] = src; dist[src] = 0;
    while (head < tail) {
        int v = queue[head++];
        int d = dist[v];
        if (d >= 9) continue;
        if (v < 2 * N) {
            int i = v / N, g = v - i * N;
            for (int t = 0; t < 4; t++) {
                int u = 2 * N + Aj[i][t] * N + mulfast(g, As[i][t]);
                if (dist[u] < 0) { dist[u] = d + 1; queue[tail++] = u; }
            }
        } else {
            int w = v - 2 * N;
            int j = w / N, h = w - j * N;
            for (int t = 0; t < 4; t++) {
                int u = Bi[j][t] * N + mulfast(h, Bs[j][t]);
                if (dist[u] < 0) { dist[u] = d + 1; queue[tail++] = u; }
            }
        }
    }
    return NV - tail;
}

static int cost(void) {
    return far_from(0) + far_from(N) + far_from(2 * N) + far_from(3 * N);
}

static void write_edges(const char *path) {
    FILE *f = fopen(path, "w");
    if (!f) { perror(path); return; }
    fprintf(f, "%d\n", NV);
    for (int i = 0; i < 2; i++)
        for (int g = 0; g < N; g++)
            for (int t = 0; t < 4; t++) {
                int u = i * N + g;
                int v = 2 * N + Aj[i][t] * N + mul[(size_t)g * N + As[i][t]];
                fprintf(f, "%d %d\n", u, v);
            }
    fclose(f);
}

/* Simulated annealing with restarts. Returns best cost; best voltages in bestv[0..4]. */
static int anneal(double secs, long epoch, int *bestv, long *evals_out) {
    double t0 = now();
    int cur[5], best[5];
    int bestc = INT_MAX, c, c2;
    long evals = 0;
    randomize();
    c = cost(); evals++;
    for (int f = 0; f < nf; f++) cur[f] = L[freei[f]][freej[f]][freet[f]];
    bestc = c; memcpy(best, cur, sizeof(cur));
    int done = 0;
    while (!done) {
        if (bestc == 0) break;
        if (rnd() & 1) { /* restart from the global best */
            for (int f = 0; f < nf; f++) L[freei[f]][freej[f]][freet[f]] = best[f];
            build_adj();
        } else {
            randomize();
        }
        c = cost(); evals++;
        for (long s = 0; s < epoch; s++) {
            if (now() - t0 >= secs) { done = 1; break; }
            double frac = (double)s / (double)epoch;
            double T = 6.0 * pow(0.3 / 6.0, frac);
            int f = rndint(nf);
            int i = freei[f], j = freej[f], t = freet[f];
            int old = L[i][j][t];
            int v = rndint(N);
            if (v == old || !ok_val(f, v)) continue;
            L[i][j][t] = v; build_adj();
            c2 = cost(); evals++;
            if (c2 <= c || urand() < exp(-(c2 - c) / T)) {
                c = c2;
                if (c < bestc) {
                    bestc = c;
                    for (int g = 0; g < nf; g++) best[g] = L[freei[g]][freej[g]][freet[g]];
                    if (bestc == 0) { done = 1; break; }
                }
            } else {
                L[i][j][t] = old; build_adj();
            }
        }
        if (now() - t0 >= secs) done = 1;
    }
    memcpy(bestv, best, sizeof(best));
    *evals_out = evals;
    return bestc;
}


static long EV = 0;
static double DEADLINE = 0;
static int SCANLIM = 600;

/* cost with early exit: returns a value >= limit as soon as the partial sum reaches limit */
static int cost_lim(int limit) {
    int s = 0;
    for (int src = 0; src < 4; src++) {
        s += far_from(src * N);
        if (s >= limit) return s;
    }
    return s;
}

/* first-improvement coordinate descent over random subsets of values (SCANLIM per coordinate) */
static int descend(int c) {
    int improved = 1;
    while (improved) {
        improved = 0;
        for (int q = 0; q < nf; q++) {
            if (now() > DEADLINE) return c;
            int f = rndint(nf);
            int i = freei[f], j = freej[f], t = freet[f];
            int old = L[i][j][t];
            int lim = N < SCANLIM ? N : SCANLIM;
            int start = rndint(N), step = 1 + 2 * rndint(N / 2);
            for (int z = 0; z < lim; z++) {
                int v = (int)(((long)start + (long)z * step) % N);
                if (v == old || !ok_val(f, v)) continue;
                L[i][j][t] = v; build_adj();
                int c2 = cost_lim(c); EV++;
                if (c2 < c) { c = c2; improved = 1; old = v; break; }
            }
            L[i][j][t] = old; build_adj();
            if (c == 0) return 0;
        }
    }
    return c;
}

/* iterated local search with random 1-2 coordinate kicks from the current local optimum */
static int ils(double secs, int *bestv, long *evals_out) {
    double t0 = now();
    DEADLINE = t0 + secs;
    int best[5], bestc, c, cur[5], curc;
    EV = 0;
    randomize();
    curc = descend(cost()); EV++;
    for (int f = 0; f < nf; f++) cur[f] = L[freei[f]][freej[f]][freet[f]];
    bestc = curc; memcpy(best, cur, sizeof(best));
    while (bestc > 0 && now() < DEADLINE) {
        int kicks = 1 + rndint(2);
        for (int k = 0; k < kicks; k++) {
            int f = rndint(nf), v;
            do { v = rndint(N); } while (!ok_val(f, v));
            L[freei[f]][freej[f]][freet[f]] = v;
        }
        build_adj();
        c = descend(cost_lim(INT_MAX)); EV++;
        if (c <= curc) {
            curc = c;
            for (int f = 0; f < nf; f++) cur[f] = L[freei[f]][freej[f]][freet[f]];
        } else {
            for (int f = 0; f < nf; f++) L[freei[f]][freej[f]][freet[f]] = cur[f];
            build_adj();
        }
        if (curc < bestc) { bestc = curc; memcpy(best, cur, sizeof(best)); }
        if (rndint(40) == 0 && now() < DEADLINE) { /* occasional random restart */
            randomize();
            curc = descend(cost_lim(INT_MAX)); EV++;
            for (int f = 0; f < nf; f++) cur[f] = L[freei[f]][freej[f]][freet[f]];
            if (curc < bestc) { bestc = curc; memcpy(best, cur, sizeof(best)); }
        }
    }
    memcpy(bestv, best, sizeof(best));
    *evals_out = EV;
    return bestc;
}

int main(int argc, char **argv) {
    if (argc < 6) {
        fprintf(stderr, "usage: lift22 GROUPFILE FIRSTLINE LASTLINE SECONDS_PER_RUN SEED [EDGEDIR]\n");
        return 2;
    }
    const char *gf = argv[1];
    int first = atoi(argv[2]), last = atoi(argv[3]);
    double secs = atof(argv[4]);
    rs ^= (uint64_t)atoll(argv[5]) * 0x9E3779B97F4A7C15ULL;
    for (int i = 0; i < 10; i++) rnd();
    const char *edir = argc > 6 ? argv[6] : ".";
    if (getenv("SCANLIM")) SCANLIM = atoi(getenv("SCANLIM"));
    FILE *f = fopen(gf, "r");
    if (!f) { perror(gf); return 2; }
    char line[256];
    int lineno = 0;
    while (fgets(line, sizeof line, f)) {
        if (lineno < first || lineno > last) { lineno++; continue; }
        lineno++;
        int m, k, r;
        if (sscanf(line, "%d %d %d", &m, &k, &r) != 3) continue;
        M = m; K = k; R = r;
        build_group();
        for (int a = 2; a >= 1; a--) {
            setup_family(a);
            int bestv[5]; long evals = 0;
            double t0 = now();
            int best = getenv("ILS") ? ils(secs, bestv, &evals) : anneal(secs, 20000, bestv, &evals);
            double el = now() - t0;
            printf("RES %d %d %d %d %d %d %ld %.1f\n", M, K, R, a, N, best, evals, el);
            fflush(stdout);
            if (best == 0 || getenv("DUMP")) {
                for (int g = 0; g < nf; g++) L[freei[g]][freej[g]][freet[g]] = bestv[g];
                build_adj();
                char path[1024];
                snprintf(path, sizeof path, "%s/%s_m%d_k%d_r%d_a%d.edges", edir, best == 0 ? "lift" : "dump", M, K, R, a);
                write_edges(path);
                printf("%s %s\n", best == 0 ? "FOUND" : "DUMP", path);
                fflush(stdout);
            }
        }
        free_group();
    }
    fclose(f);
    return 0;
}
