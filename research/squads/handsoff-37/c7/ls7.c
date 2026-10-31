/* ls7.c (worker c7): local search over cubic bipartite graphs on n = 2m vertices, D = 7.
   cost = number of ORDERED same-side pairs at distance > 6 (0 iff diameter <= 7, for a connected graph).
   Same-side ball of radius 6 = radius-3 ball in the 2-step graph H on each side (H(x) = same-side vertices
   at distance 2, with x itself). Bitsets: m <= 128 -> 2 words per row. Cost ~ 2 us at n = 170.

   Usage: ls7 n seed seconds T0 T1 cycle pf focus_k [init.edges|-] [out.edges]
     T0, T1: start/end temperature (geometric), cycle: seconds per cooling cycle (restart from best at cycle start),
     pf: probability of a focused proposal, focus_k: 0 = pure random partner, else focused partner from the
     unreached set of x (uses x's 2-step ball to pick the edges).
   Moves: 2-switch on edges (u1 v1), (u2 v2) of one side S: -> (u1 v2), (u2 v1), keeps simple cubic bipartite.
   Build: gcc -O3 -march=native -o ls7 ls7.c -lm */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <time.h>

#define MAXN 260
#define MAXM 130
#define W 2

static int n, m;
static int nb[MAXN][3];
static uint64_t reach[MAXN][W];   /* global vertex x: bit j set iff local same-side vertex j within distance 6 */
static int cnt[MAXN];             /* unreached same-side count of x */
static uint64_t B1[MAXM][W], B2[MAXM][W];
static int hlb[MAXM][9];

static uint64_t rng_s = 88172645463325252ULL;
static inline uint64_t xr(void) { rng_s ^= rng_s << 13; rng_s ^= rng_s >> 7; rng_s ^= rng_s << 17; return rng_s; }
static inline double ur(void) { return (xr() >> 11) * (1.0 / 9007199254740992.0); }
static inline int ri(int k) { return (int)(xr() % (uint64_t)k); }

/* cost over both sides; fills reach[] and cnt[] */
static long cost_full(void) {
    long total = 0;
    for (int s = 0; s < 2; s++) {
        int base = s * m;
        for (int i = 0; i < m; i++) {
            int x = base + i, k = 0;
            uint64_t *b = B1[i]; b[0] = b[1] = 0;
            for (int p = 0; p < 3; p++) {
                int y = nb[x][p];
                for (int q = 0; q < 3; q++) {
                    int j = nb[y][q] - base;
                    hlb[i][k++] = j;
                    b[j >> 6] |= 1ULL << (j & 63);
                }
            }
        }
        for (int i = 0; i < m; i++) {
            uint64_t a0 = B1[i][0], a1 = B1[i][1];
            for (int k = 0; k < 9; k++) { int j = hlb[i][k]; a0 |= B1[j][0]; a1 |= B1[j][1]; }
            B2[i][0] = a0; B2[i][1] = a1;
        }
        for (int i = 0; i < m; i++) {
            uint64_t a0 = B2[i][0], a1 = B2[i][1];
            for (int k = 0; k < 9; k++) { int j = hlb[i][k]; a0 |= B2[j][0]; a1 |= B2[j][1]; }
            int x = base + i;
            reach[x][0] = a0; reach[x][1] = a1;
            int c = m - __builtin_popcountll(a0) - __builtin_popcountll(a1);
            cnt[x] = c; total += c;
        }
    }
    return total;
}

/* remove u1v1, u2v2; add u1v2, u2v1 (u1,u2 on one side) */
static inline void swap2(int u1, int v1, int u2, int v2) {
    for (int k = 0; k < 3; k++) if (nb[u1][k] == v1) { nb[u1][k] = v2; break; }
    for (int k = 0; k < 3; k++) if (nb[u2][k] == v2) { nb[u2][k] = v1; break; }
    for (int k = 0; k < 3; k++) if (nb[v1][k] == u1) { nb[v1][k] = u2; break; }
    for (int k = 0; k < 3; k++) if (nb[v2][k] == u2) { nb[v2][k] = u1; break; }
}
static inline int adjq(int a, int b) { return nb[a][0] == b || nb[a][1] == b || nb[a][2] == b; }

static void random_graph(void) {
    for (;;) {
        int ok = 1;
        for (int i = 0; i < n; i++) nb[i][0] = nb[i][1] = nb[i][2] = -1;
        for (int k = 0; k < 3 && ok; k++) {
            int p[MAXM];
            for (int i = 0; i < m; i++) p[i] = i;
            for (int i = m - 1; i > 0; i--) { int j = ri(i + 1); int t = p[i]; p[i] = p[j]; p[j] = t; }
            for (int i = 0; i < m; i++) {
                int a = i, b = m + p[i];
                int dup = 0;
                for (int t = 0; t < 3; t++) if (nb[a][t] == b) dup = 1;
                if (dup) { ok = 0; break; }
                for (int t = 0; t < 3; t++) if (nb[a][t] < 0) { nb[a][t] = b; break; }
                for (int t = 0; t < 3; t++) if (nb[b][t] < 0) { nb[b][t] = a; break; }
            }
        }
        if (ok) return;
    }
}

static void load(const char *path) {
    FILE *f = fopen(path, "r");
    if (!f) { perror(path); exit(2); }
    int nn; if (fscanf(f, "%d", &nn) != 1 || nn != n) { fprintf(stderr, "init n mismatch\n"); exit(2); }
    int dg[MAXN] = {0}; for (int i = 0; i < n; i++) nb[i][0] = nb[i][1] = nb[i][2] = -1;
    int a, b;
    while (fscanf(f, "%d %d", &a, &b) == 2) {
        if (a > b) { int t = a; a = b; b = t; }
        if (a < m && b >= m) { nb[a][dg[a]++] = b; nb[b][dg[b]++] = a; }
        else { fprintf(stderr, "init: edge not A-B (%d %d)\n", a, b); exit(2); }
    }
    fclose(f);
    for (int i = 0; i < n; i++) if (dg[i] != 3) { fprintf(stderr, "init: vertex %d has degree %d\n", i, dg[i]); exit(2); }
}

static void save(const char *path) {
    FILE *f = fopen(path, "w"); if (!f) return;
    fprintf(f, "%d\n", n);
    for (int a = 0; a < m; a++) for (int k = 0; k < 3; k++) fprintf(f, "%d %d\n", a, nb[a][k]);
    fclose(f);
}

static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }

static int valid_pair(int u1, int v1, int u2, int v2) {
    if (u1 == u2 || v1 == v2) return 0;
    if (adjq(u1, v2) || adjq(u2, v1)) return 0;
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 9) { fprintf(stderr, "usage: ls7 n seed seconds T0 T1 cycle pf focus_k [init|-] [out]\n"); return 2; }
    n = atoi(argv[1]); m = n / 2;
    if (n > MAXN - 4 || m > MAXM || (n & 1)) { fprintf(stderr, "bad n\n"); return 2; }
    rng_s ^= (uint64_t)atoll(argv[2]) * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 10; i++) xr();
    double secs = atof(argv[3]), T0 = atof(argv[4]), T1 = atof(argv[5]), cyc = atof(argv[6]);
    double pf = atof(argv[7]); int focus_k = atoi(argv[8]);
    const char *init = argc > 9 ? argv[9] : "-";
    const char *out = argc > 10 ? argv[10] : "best.edges";
    if (strcmp(init, "-") == 0) random_graph(); else load(init);

    long cur = cost_full(), best = cur;
    save(out);
    double t0 = now(), tlast = t0, tcyc0 = t0;
    static int bestnb[MAXN][3];
    memcpy(bestnb, nb, sizeof(nb));
    long it = 0, acc = 0;
    static uint64_t reachb[MAXN][W]; static int cntb[MAXN];
    printf("start cost %ld\n", cur); fflush(stdout);
    for (;;) {
        if ((it & 255) == 0) {
            double el = now() - t0;
            if (el > secs) break;
            if (now() - tcyc0 > cyc) { /* restart the cycle from the best state found so far */
                memcpy(nb, bestnb, sizeof(nb)); cur = cost_full(); tcyc0 = now();
            }
            if (now() - tlast > 10.0) {
                double frac = fmod(now() - tcyc0, cyc) / cyc;
                printf("t=%.0f it=%ld acc=%.3f cur=%ld best=%ld T=%.3f\n", el, it, (double)acc / (it + 1), cur, best,
                       T0 * pow(T1 / T0, frac));
                fflush(stdout); tlast = now();
            }
        }
        it++;
        double T = T0 * pow(T1 / T0, fmod(now() - tcyc0, cyc) / cyc);

        int s = ri(2), base = s * m;
        int u1, v1, u2, v2;
        if (focus_k && ur() < pf) {
            /* x: random bad vertex on side s; y: random unreached same-side vertex of x */
            int x = -1;
            for (int tries = 0; tries < 64; tries++) { int c = base + ri(m); if (cnt[c] > 0) { x = c; break; } }
            if (x < 0) continue;
            int jy = -1;
            for (int tries = 0; tries < 256; tries++) {
                int j = ri(m);
                if (!((reach[x][j >> 6] >> (j & 63)) & 1ULL)) { jy = j; break; }
            }
            if (jy < 0) continue;
            int y = base + jy;
            /* u1: a same-side vertex near x (2-step neighbour), u2: near y */
            u1 = (ur() < 0.5) ? x : (nb[nb[x][ri(3)]][ri(3)]);
            u2 = (ur() < 0.5) ? y : (nb[nb[y][ri(3)]][ri(3)]);
            v1 = nb[u1][ri(3)];
            v2 = nb[u2][ri(3)];
        } else if (focus_k == 2) {
            /* local switch: u2 is a 2-step neighbour (or 4-step) of u1 */
            u1 = base + ri(m);
            int w = nb[u1][ri(3)];
            u2 = nb[w][ri(3)];
            if (u2 == u1) continue;
            v1 = nb[u1][ri(3)];
            v2 = nb[u2][ri(3)];
        } else {
            u1 = base + ri(m); v1 = nb[u1][ri(3)];
            u2 = base + ri(m); v2 = nb[u2][ri(3)];
        }
        if (!valid_pair(u1, v1, u2, v2)) continue;

        memcpy(reachb, reach, sizeof(reach)); memcpy(cntb, cnt, sizeof(cnt));
        swap2(u1, v1, u2, v2);
        long c2 = cost_full();
        long d = c2 - cur;
        if (d <= 0 || ur() < exp(-(double)d / T)) {
            cur = c2; acc++;
            if (cur < best) {
                best = cur; memcpy(bestnb, nb, sizeof(nb)); save(out);
                printf("t=%.1f it=%ld best %ld\n", now() - t0, it, best); fflush(stdout);
                if (best == 0) { printf("FOUND\n"); break; }
            }
        } else {
            swap2(u1, v2, u2, v1);
            memcpy(reach, reachb, sizeof(reach)); memcpy(cnt, cntb, sizeof(cnt));
        }
    }
    printf("end best %ld its %ld acc %.4f time %.1f\n", best, it, (double)acc / (it + 1), now() - t0);
    return 0;
}
