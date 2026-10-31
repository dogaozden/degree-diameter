/* tw.c (worker c6): graphs on A={a_x}, B={b_y}, x,y in G (|G| = m, multiplication table file, element 0 = id).
 * Edges: a_x ~ b_{x*s_i} for i = 0..4 (the 5 translation edges, S = {s_0..s_4}) and a_x ~ b_{sigma(x)} (one twisted
 * matching, sigma any permutation of G; sigma(x) = phi(x) t covers every phi, t). Degree 6 (multi-edges are merged).
 * Cost = number of unordered vertex pairs at distance > 5 (bit-parallel BFS to depth 5).
 * Simulated annealing; moves: swap sigma(x), sigma(y) (prob 1-PS) or replace one s_i (prob PS).
 * usage: tw TABLE SEED SECONDS OUTPREFIX [T0 T1 ITERS_PER_CYCLE] [S=a,b,c,d,e] [INIT=identity:t | INIT=random]
 *   writes OUTPREFIX.edges whenever the best cost improves (edge list, first number n) and OUTPREFIX.log lines.
 *   ends early when cost 0 is reached (prints FOUND).                               */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <time.h>
static double wall(void) { struct timespec ts; clock_gettime(CLOCK_MONOTONIC, &ts); return ts.tv_sec + ts.tv_nsec * 1e-9; }

static uint64_t rs;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline double urand(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int m, n, W;
static int *mul, *inv;
static int S[6], sig[1024], sigi[1024];
static int haarmode = 0;
static int randrestart = 0;
static int usetabu = 0;
#define NX 2
#define TEN 12
static int adj[2048][6];
static uint64_t *R, *Rn;

static void set_haar(void) {
    for (int x = 0; x < m; x++) { sig[x] = mul[x * m + S[5]]; }
    for (int x = 0; x < m; x++) sigi[sig[x]] = x;
}
static void build_adj(void) {
    for (int x = 0; x < m; x++) {
        for (int i = 0; i < 5; i++) adj[x][i] = m + mul[x * m + S[i]];
        adj[x][5] = m + sig[x];
    }
    /* b_y neighbours: a_x with x*s_i = y  ->  x = y * s_i^{-1}; a_x with sigma(x) = y -> x = sigi[y] */
    for (int y = 0; y < m; y++) {
        for (int i = 0; i < 5; i++) adj[m + y][i] = mul[y * m + inv[S[i]]];
        adj[m + y][5] = sigi[y];
    }
}

/* number of unordered pairs at distance > 5 */
static long score(void) {
    build_adj();
    memset(R, 0, sizeof(uint64_t) * (size_t)n * W);
    for (int v = 0; v < n; v++) R[(size_t)v * W + (v >> 6)] |= 1ULL << (v & 63);
    for (int k = 0; k < 5; k++) {
        memcpy(Rn, R, sizeof(uint64_t) * (size_t)n * W);
        for (int v = 0; v < n; v++) {
            uint64_t *dst = Rn + (size_t)v * W;
            for (int j = 0; j < 6; j++) {
                const uint64_t *src = R + (size_t)adj[v][j] * W;
                for (int w = 0; w < W; w++) dst[w] |= src[w];
            }
        }
        uint64_t *t = R; R = Rn; Rn = t;
    }
    long tot = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += __builtin_popcountll(R[(size_t)v * W + w]);
        tot += n - c;
    }
    return tot / 2;
}

static void write_edges(const char *path) {
    FILE *f = fopen(path, "w");
    if (!f) return;
    fprintf(f, "%d\n", n);
    for (int x = 0; x < m; x++) {
        for (int i = 0; i < 5; i++) fprintf(f, "%d %d\n", x, m + mul[x * m + S[i]]);
        fprintf(f, "%d %d\n", x, m + sig[x]);
    }
    fclose(f);
}

int main(int argc, char **argv) {
    if (argc < 5) { fprintf(stderr, "usage: tw TABLE SEED SECONDS OUTPREFIX [T0 T1 ITERS] [S=..] [INIT=..]\n"); return 2; }
    FILE *f = fopen(argv[1], "r");
    if (!f) { fprintf(stderr, "no table\n"); return 2; }
    if (fscanf(f, "%d", &m) != 1) return 2;
    mul = malloc(sizeof(int) * m * m);
    for (int i = 0; i < m * m; i++) if (fscanf(f, "%d", &mul[i]) != 1) return 2;
    fclose(f);
    n = 2 * m; W = (n + 63) / 64;
    inv = malloc(sizeof(int) * m);
    for (int g = 0; g < m; g++) for (int h = 0; h < m; h++) if (mul[g * m + h] == 0) inv[g] = h;
    R = malloc(sizeof(uint64_t) * (size_t)n * W); Rn = malloc(sizeof(uint64_t) * (size_t)n * W);
    rs = 88172645463325252ULL ^ (uint64_t)strtoull(argv[2], 0, 10) * 0x9E3779B97F4A7C15ULL;
    for (int i = 0; i < 10; i++) rnd();
    double secs = atof(argv[3]);
    const char *outp = argv[4];
    double T0 = 2.0, T1 = 0.05;
    long ipc = 2000000;
    int fixedS = 0, init_t = -1;
    for (int a = 5; a < argc; a++) {
        if (!strncmp(argv[a], "T0=", 3)) T0 = atof(argv[a] + 3);
        else if (!strncmp(argv[a], "T1=", 3)) T1 = atof(argv[a] + 3);
        else if (!strncmp(argv[a], "IPC=", 4)) ipc = atol(argv[a] + 4);
    }
    int initmode = 0; /* 0 random sigma, 1 haar (sigma = x*S5) */
    int PSden = 20;
    for (int a = 5; a < argc; a++) {
        if (!strncmp(argv[a], "S=", 2)) {
            char buf[256]; strncpy(buf, argv[a] + 2, 255); buf[255] = 0;
            int i = 0; for (char *p = strtok(buf, ","); p && i < 6; p = strtok(NULL, ",")) S[i++] = atoi(p);
            fixedS = 1;
        } else if (!strcmp(argv[a], "MODE=haar")) haarmode = 1;
        else if (!strcmp(argv[a], "INIT=haar")) initmode = 1;
        else if (!strcmp(argv[a], "RESTART=random")) randrestart = 1;
        else if (!strcmp(argv[a], "TABU=1")) usetabu = 1;
        else if (!strncmp(argv[a], "PSDEN=", 6)) PSden = atoi(argv[a] + 6);
        else if (!strncmp(argv[a], "INIT=identity:", 14)) init_t = atoi(argv[a] + 14);
    }
    if (!fixedS) for (int i = 0; i < 6; i++) S[i] = rnd() % m;
    if (init_t >= 0) { S[5] = init_t; initmode = 1; }
    if (haarmode) initmode = 1;
    if (initmode == 1) { set_haar(); }
    else { for (int x = 0; x < m; x++) sig[x] = x; for (int x = m - 1; x > 0; x--) { int j = rnd() % (x + 1); int t = sig[x]; sig[x] = sig[j]; sig[j] = t; } }
    for (int x = 0; x < m; x++) sigi[sig[x]] = x;
    /* check that sig is a permutation (identity case) */
    { char *seen = calloc(m, 1); for (int x = 0; x < m; x++) { if (seen[sig[x]]) { fprintf(stderr, "sigma not a permutation\n"); return 2; } seen[sig[x]] = 1; } free(seen); }


    long cur = score(), best = cur;
    int bestS[6]; int bestsig[1024];
    memcpy(bestS, S, sizeof S); memcpy(bestsig, sig, sizeof(int) * m);
    char logp[512]; snprintf(logp, sizeof logp, "%s.log", outp);
    FILE *lg = fopen(logp, "a");
    char ep[512]; snprintf(ep, sizeof ep, "%s.edges", outp);
    double c0 = wall();
    long it = 0, acc = 0;
    double T = T0;
    long cyc = 0;
    fprintf(stderr, "start cost=%ld\n", cur);
    if (usetabu) {
        /* steepest tabu over: S_i := g (i<5, all g) and sigma swaps (x0, y) for NX random x0 */
        long tabuS[6] = {0,0,0,0,0,0}; long *tabuX = calloc(m, sizeof(long));
        long step = 0; long tenure = TEN;
        cur = score(); best = cur; memcpy(bestS, S, sizeof S); memcpy(bestsig, sig, sizeof(int) * m);
        double tc0 = wall();
        while (wall() - tc0 < secs) {
            step++;
            long bc = 1L << 60; int kind = -1, ai = -1, aj = -1, aval = -1;
            /* S moves */
            for (int i = 0; i < 5; i++) {
                int old = S[i];
                for (int g = 0; g < m; g++) {
                    if (g == old) continue;
                    S[i] = g; long c = score();
                    int tabu = tabuS[i] > step;
                    if ((!tabu || c < best) && c < bc) { bc = c; kind = 0; ai = i; aval = g; }
                }
                S[i] = old;
            }
            /* sigma swaps */
            for (int r = 0; r < NX; r++) {
                int x0 = rnd() % m;
                for (int y = 0; y < m; y++) {
                    if (y == x0) continue;
                    int sx = sig[x0], sy = sig[y];
                    sig[x0] = sy; sig[y] = sx; sigi[sy] = x0; sigi[sx] = y;
                    long c = score();
                    int tabu = (tabuX[x0] > step) || (tabuX[y] > step);
                    if ((!tabu || c < best) && c < bc) { bc = c; kind = 1; ai = x0; aj = y; }
                    sig[x0] = sx; sig[y] = sy; sigi[sx] = x0; sigi[sy] = y;
                }
            }
            if (kind < 0) continue;
            if (kind == 0) { S[ai] = aval; tabuS[ai] = step + tenure; }
            else {
                int sx = sig[ai], sy = sig[aj];
                sig[ai] = sy; sig[aj] = sx; sigi[sy] = ai; sigi[sx] = aj;
                tabuX[ai] = step + tenure; tabuX[aj] = step + tenure;
            }
            cur = bc;
            if (cur < best) {
                best = cur; memcpy(bestS, S, sizeof S); memcpy(bestsig, sig, sizeof(int) * m);
                double el = wall() - c0;
                fprintf(stderr, "step=%ld t=%.0f best=%ld kind=%d\n", step, el, best, kind);
                write_edges(ep);
                if (lg) { fprintf(lg, "n=%d best=%ld step=%ld t=%.0f TABU\n", n, best, step, el); fflush(lg); }
                if (best == 0) { printf("FOUND n=%d\n", n); break; }
            }
            if (step % 50 == 0) fprintf(stderr, "step=%ld cur=%ld best=%ld\n", step, cur, best);
        }
        printf("END-TABU m=%d n=%d best=%ld steps=%ld S=%d,%d,%d,%d,%d\n", m, n, best, step, bestS[0], bestS[1], bestS[2], bestS[3], bestS[4]);
        if (lg) fclose(lg);
        return 0;
    }

    while (1) {
        if (it % 4096 == 0) {
            double el = wall() - c0;
            if (el > secs) break;
        }
        /* temperature: geometric within a cycle of ipc iterations, then reheat from best */
        double frac = (double)(it % ipc) / (double)ipc;
        T = T0 * pow(T1 / T0, frac);
        if (it > 0 && it % ipc == 0) {
            cyc++;
            /* restart from best */
            if (randrestart) {
                for (int i = 0; i < 6; i++) if (!(fixedS && 0)) S[i] = rnd() % m;
                if (haarmode) set_haar();
                cur = score();
            } else {
                memcpy(S, bestS, sizeof S); memcpy(sig, bestsig, sizeof(int) * m);
                for (int x = 0; x < m; x++) sigi[sig[x]] = x;
                cur = best;
            }
        }
        it++;
        if (haarmode || (!fixedS && rnd() % PSden == 0)) {
            int i = haarmode ? (int)(rnd() % 6) : (int)(rnd() % 5); int old = S[i];
            int oldsig[1024];
            if (i == 5) memcpy(oldsig, sig, sizeof(int) * m);
            int nw = rnd() % m;
            S[i] = nw;
            if (i == 5) set_haar();
            long c = score();
            long d = c - cur;
            if (d <= 0 || urand() < exp(-d / T)) { cur = c; acc++; }
            else { S[i] = old; if (i == 5) { memcpy(sig, oldsig, sizeof(int) * m); for (int x = 0; x < m; x++) sigi[sig[x]] = x; } }
        } else {
            int x = rnd() % m, y = rnd() % m;
            if (x == y) continue;
            int sx = sig[x], sy = sig[y];
            sig[x] = sy; sig[y] = sx; sigi[sy] = x; sigi[sx] = y;
            long c = score();
            long d = c - cur;
            if (d <= 0 || urand() < exp(-d / T)) { cur = c; acc++; }
            else { sig[x] = sx; sig[y] = sy; sigi[sx] = x; sigi[sy] = y; }
        }
        if (cur < best) {
            best = cur;
            memcpy(bestS, S, sizeof S); memcpy(bestsig, sig, sizeof(int) * m);
            double el = wall() - c0;
            fprintf(stderr, "it=%ld t=%.0f best=%ld T=%.3f\n", it, el, best, T);
            write_edges(ep);
            if (lg) { fprintf(lg, "n=%d best=%ld it=%ld t=%.0f S=%d,%d,%d,%d,%d,%d\n", n, best, it, el, S[0], S[1], S[2], S[3], S[4], S[5]); fflush(lg); }
            if (best == 0) { printf("FOUND n=%d\n", n); break; }
        }
    }
    printf("END m=%d n=%d best=%ld it=%ld cycles=%ld acc=%ld S=%d,%d,%d,%d,%d,%d\n", m, n, best, it, cyc, acc,
           bestS[0], bestS[1], bestS[2], bestS[3], bestS[4], bestS[5]);
    if (lg) fclose(lg);
    return 0;
}
