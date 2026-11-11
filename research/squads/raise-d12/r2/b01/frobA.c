/* b01 (r2): Haar graphs H(G,S) on G = F_512 x| C_73 (v,j)(w,l) = (v + z^j w, j+l), z = zeta^7 (order 73).
 * alpha(v,j) = (v^8, 8j) (order 3, Fix = F_8 x {0}).
 * Modes:
 *   scan a b            : orbit-closed S = {e,x,ax,a^2x} for x in [a,b); histogram of holes U1 (B-elements not within 11 of (e,A)).
 *   anneal seed secs    : plain S = {e,s1,s2,s3} simulated annealing, moves: targeted (cover a random uncovered B-element y
 *                         by s_new = y v^-1 for a random reached A-vertex v at even depth <= 10) or random replacement.
 *   Cost 0 => writes EDGE file b01_sol_<seed>.txt (n=2N, "u v" lines) and prints S.
 * Cost = holes from (e,A) only (right-multiplication transitivity + neighbour argument gives diameter <= 12 when 0).
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>
static double wall(void){ struct timespec ts; clock_gettime(CLOCK_MONOTONIC,&ts); return ts.tv_sec+1e-9*ts.tv_nsec; }
#define NF 512
#define K 73
#define N (NF * K)
static int expt[2 * NF], logt[NF], pw7[K];
static uint8_t *dist; static int *q;
static int S[4], Sinv[4];
static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int fmul(int a, int b) { if (!a || !b) return 0; return expt[logt[a] + logt[b]]; }
static inline int gmul(int g1, int g2) {
    int v1 = g1 / K, j1 = g1 % K, v2 = g2 / K, j2 = g2 % K;
    int v = v1 ^ fmul(pw7[j1], v2);
    int j = (j1 + j2) % K;
    return v * K + j;
}
static int ginv(int g) {
    int v = g / K, j = g % K;
    int jinv = (K - j) % K;
    int vi = fmul(pw7[jinv], v);
    return vi * K + jinv;
}
static inline int galpha(int g) {
    int v = g / K, j = g % K; int v8 = 0;
    if (v) { int l = logt[v]; v8 = expt[(8 * l) % 511]; }
    return v8 * K + (8 * j) % K;
}
static int qlen; /* BFS queue length after holes() */
static int holes(int src) {
    memset(dist, 255, 2 * N);
    int head = 0, tail = 0;
    q[tail++] = src; dist[src] = 0;
    while (head < tail) {
        int v = q[head++]; int d = dist[v];
        if (d >= 11) continue;
        if (v < N) {
            for (int i = 0; i < 4; i++) { int w = N + gmul(S[i], v); if (dist[w] == 255) { dist[w] = d + 1; q[tail++] = w; } }
        } else {
            int y = v - N;
            for (int i = 0; i < 4; i++) { int w = gmul(Sinv[i], y); if (dist[w] == 255) { dist[w] = d + 1; q[tail++] = w; } }
        }
    }
    qlen = tail;
    int lo = (src < N) ? N : 0, hi = (src < N) ? 2 * N : N, cnt = 0;
    for (int v = lo; v < hi; v++) if (dist[v] == 255) cnt++;
    return cnt;
}
static void setS(void) { for (int i = 0; i < 4; i++) Sinv[i] = ginv(S[i]); }
static void setOrb(int x) { S[0] = 0; S[1] = x; S[2] = galpha(x); S[3] = galpha(S[2]); setS(); }
static int distinct(void) { for (int i = 0; i < 4; i++) for (int j = 0; j < i; j++) if (S[i] == S[j]) return 0; return 1; }
static void init_field(void) {
    int poly = (1 << 9) | (1 << 4) | 1, e = 1;
    for (int i = 0; i < 511; i++) { expt[i] = e; expt[i + 511] = e; e <<= 1; if (e & 512) e ^= poly; }
    for (int i = 0; i < 511; i++) logt[expt[i]] = i;
    for (int j = 0; j < K; j++) pw7[j] = expt[(7 * j) % 511];
    dist = malloc(2 * N); q = malloc(sizeof(int) * 2 * N);
}
static void write_edges(const char *fn) {
    FILE *f = fopen(fn, "w"); if (!f) return;
    fprintf(f, "%d\n", 2 * N);
    for (int g = 0; g < N; g++) for (int i = 0; i < 4; i++) fprintf(f, "%d %d\n", g, N + gmul(S[i], g));
    fclose(f);
}
int main(int argc, char **argv) {
    init_field();
    if (argc < 2) return 1;
    if (!strcmp(argv[1], "scan")) {
        long a = atol(argv[2]), b = atol(argv[3]);
        long hist[64] = {0}; int bestU = 1 << 30; long bestx = -1, tested = 0;
        for (long x = a; x < b && x < N; x++) {
            if (x < 1 || galpha(x) == x) continue;
            { int y1 = galpha(x), y2 = galpha(y1); if (y1 < x || y2 < x) continue; } /* orbit representative only */
            setOrb((int)x); if (!distinct()) continue;
            int U = holes(0); tested++;
            if (U < 64) hist[U]++;
            if (U < bestU) { bestU = U; bestx = x; }
            if (U <= 20) { printf("x %ld U %d\n", x, U); fflush(stdout); }
            if (U == 0) { printf("U1=0 x=%ld S=%d %d %d %d\n", x, S[0], S[1], S[2], S[3]); fflush(stdout);
                char fn[128]; sprintf(fn, "b01_orb_x%ld.txt", x); write_edges(fn); }
        }
        printf("scan [%ld,%ld) tested=%ld best_U1=%d at x=%ld\nhist:", a, b, tested, bestU, bestx);
        for (int i = 0; i < 64; i++) if (hist[i]) printf(" %d:%ld", i, hist[i]);
        printf("\n");
        return 0;
    }
    if (!strcmp(argv[1], "anneal")) {
        uint64_t seed = strtoull(argv[2], 0, 10); double secs = atof(argv[3]);
        double T0 = argc > 4 ? atof(argv[4]) : 1.5;
        rs ^= seed * 2654435761ULL; for (int i = 0; i < 10; i++) rnd();
        int cur[4]; int bestS[4]; int bestC = 1 << 30; long evals = 0, restarts = 0;
        double t0 = wall();
        int hist_best[64] = {0};
        for (;;) {
            /* random start */
            S[0] = 0; do { for (int i = 1; i < 4; i++) S[i] = 1 + rnd() % (N - 1); } while (!distinct());
            setS(); int C = holes(0); evals++; restarts++;
            double T = T0;
            long steps = 0;
            while (1) {
                steps++;
                if ((steps & 15) == 0) {
                    double el = wall() - t0;
                    if (el > secs) goto done;
                    T = T0 * (1.0 - 0.9 * (steps % 20000) / 20000.0);
                }
                if (C == 0) break;
                int old[4]; memcpy(old, S, sizeof old);
                int i = 1 + rnd() % 3;
                int nw;
                if (rnd() % 10 < 7) {
                    /* targeted: uncovered B-element y, covered by s = y v^-1 from a reached A-vertex v at even depth <= 10 */
                    int y, tries = 0;
                    do { y = N + rnd() % N; tries++; } while (dist[y] != 255 && tries < 100000);
                    int v; int tv = 0;
                    do { v = q[rnd() % qlen]; tv++; } while ((v >= N || dist[v] > 10) && tv < 100000);
                    if (v >= N) continue;
                    nw = gmul(y - N, ginv(v));
                } else nw = 1 + rnd() % (N - 1);
                S[i] = nw; setS();
                if (!distinct()) { memcpy(S, old, sizeof old); setS(); continue; }
                int Cn = holes(0); evals++;
                int dlt = Cn - C;
                if (dlt <= 0 || (double)(rnd() % 1000000) / 1e6 < __builtin_exp(-dlt / T)) {
                    C = Cn;
                    if (C < bestC) { bestC = C; memcpy(bestS, S, sizeof S); }
                } else { memcpy(S, old, sizeof old); setS(); }
            }
            if (C < 64) hist_best[C]++;
            if (C == 0) {
                printf("COST 0 seed=%llu S=%d %d %d %d (restart %ld, evals %ld)\n", (unsigned long long)seed, S[0], S[1], S[2], S[3], restarts, evals);
                char fn[128]; sprintf(fn, "b01_sol_%llu.txt", (unsigned long long)seed); write_edges(fn);
                fflush(stdout);
                break;
            }
            if (C < bestC) { bestC = C; memcpy(bestS, S, sizeof S); }
            printf("restart %ld end cost %d (best so far %d) evals %ld\n", restarts, C, bestC, evals); fflush(stdout);
        }
done:
        printf("anneal seed=%llu done: evals=%ld restarts=%ld best_cost=%d bestS=%d %d %d %d\n", (unsigned long long)seed, evals, restarts, bestC, bestS[0], bestS[1], bestS[2], bestS[3]);
        return 0;
    }
    return 1;
}
