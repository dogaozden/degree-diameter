// Voltage-cover annealer for a small base graph (<=256 vertices) and a group of order N<=8.
// Cost = number of (root (u,e), lift vertex) pairs at distance > D; cost 0 = valid lift.
// usage: cov BASE_TREE GROUP SECONDS SEED OUTPREFIX T0 T1 [D]
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>
#include <math.h>
#define MAXB 256
#define MAXE 1024
static int N, mul[8][8], invv[8];
static int nb, m, ea[MAXE], eb[MAXE], etree[MAXE], volt[MAXE], cot[MAXE], ncot, D = 10;
static uint8_t TT[8][256];
static int nin[MAXB], inw[MAXB][8], inx[MAXB][8];
static uint64_t rs = 88172645463325252ULL;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static double urand(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static void build_in(void) {
    for (int v = 0; v < nb; v++) nin[v] = 0;
    for (int e = 0; e < m; e++) {
        int a = ea[e], b = eb[e], x = volt[e];
        inw[b][nin[b]] = a; inx[b][nin[b]] = x; nin[b]++;     // dart a->b has voltage x
        inw[a][nin[a]] = b; inx[a][nin[a]] = invv[x]; nin[a]++; // dart b->a has voltage x^-1
    }
}

static int cost(int bound) {
    int total = 0;
    uint8_t cur[MAXB], nxt[MAXB];
    int full = N; (void)full;
    for (int u = 0; u < nb; u++) {
        memset(cur, 0, nb);
        cur[u] = 1; // identity element is index 0
        for (int k = 1; k <= D; k++) {
            for (int v = 0; v < nb; v++) {
                uint8_t s = cur[v];
                for (int i = 0; i < nin[v]; i++) s |= TT[inx[v][i]][cur[inw[v][i]]];
                nxt[v] = s;
            }
            memcpy(cur, nxt, nb);
        }
        for (int v = 0; v < nb; v++) total += N - __builtin_popcount(cur[v]);
        if (total > bound) return total;
    }
    return total;
}

int main(int argc, char **argv) {
    if (argc < 8) { fprintf(stderr, "usage: cov BASE GROUP SECONDS SEED OUTPREFIX T0 T1 [D]\n"); return 1; }
    FILE *f = fopen(argv[1], "r");
    if (fscanf(f, "%d %d", &nb, &m) != 2) return 1;
    int side[MAXB];
    ncot = 0;
    for (int e = 0; e < m; e++) {
        int a, b, t, s;
        if (fscanf(f, "%d %d %d %d", &a, &b, &t, &s) != 4) return 1;
        ea[e] = a; eb[e] = b; etree[e] = t; volt[e] = 0;
        if (!t) cot[ncot++] = e;
        side[a] = s; side[b] = 1 - s;
    }
    fclose(f);
    f = fopen(argv[2], "r");
    if (fscanf(f, "%d", &N) != 1) return 1;
    for (int i = 0; i < N; i++) for (int j = 0; j < N; j++) if (fscanf(f, "%d", &mul[i][j]) != 1) return 1;
    fclose(f);
    for (int x = 0; x < N; x++) for (int y = 0; y < N; y++) if (mul[x][y] == 0) invv[x] = y;
    for (int x = 0; x < N; x++) for (int mask = 0; mask < 256; mask++) {
        int r = 0;
        for (int h = 0; h < N; h++) if (mask >> h & 1) r |= 1 << mul[h][x];
        TT[x][mask] = (uint8_t)r;
    }
    double secs = atof(argv[3]);
    rs ^= (uint64_t)atoll(argv[4]) * 0x9E3779B97F4A7C15ULL; if (!rs) rs = 1;
    const char *outp = argv[5];
    double T0 = atof(argv[6]), T1 = atof(argv[7]);
    if (argc > 8) D = atoi(argv[8]);
    for (int i = 0; i < 10; i++) rnd();
    for (int i = 0; i < ncot; i++) volt[cot[i]] = rnd() % N;
    build_in();
    int cur = cost(1 << 30), best = cur;
    int bestvolt[MAXE];
    memcpy(bestvolt, volt, sizeof(int) * m);
    fprintf(stderr, "N=%d nb=%d cotree=%d initial cost %d\n", N, nb, ncot, cur);
    clock_t t0 = clock();
    long iters = 0, acc = 0;
    double el = 0, lastp = 0;
    while (1) {
        if ((iters & 255) == 0) {
            el = (double)(clock() - t0) / CLOCKS_PER_SEC;
            if (el >= secs) break;
            if (el - lastp >= 10) { lastp = el; fprintf(stderr, "t=%.0f it=%ld cur=%d best=%d\n", el, iters, cur, best); }
        }
        iters++;
        double Tm = T0 * pow(T1 / T0, el / secs);
        int c = cot[rnd() % ncot];
        int old = volt[c];
        int nv = rnd() % N;
        if (nv == old) continue;
        volt[c] = nv; build_in();
        double thr = cur - Tm * log(urand() + 1e-300);
        int nc = cost((int)floor(thr));
        if (nc <= thr) {
            cur = nc; acc++;
            if (cur < best) { best = cur; memcpy(bestvolt, volt, sizeof(int) * m); }
            if (cur == 0) break;
        } else { volt[c] = old; build_in(); }
    }
    fprintf(stderr, "done iters=%ld acc=%ld best=%d\n", iters, acc, best);
    // write best
    memcpy(volt, bestvolt, sizeof(int) * m);
    char fn[512];
    sprintf(fn, "%s.volt", outp);
    f = fopen(fn, "w");
    fprintf(f, "%d %d %d\n", N, nb, best);
    for (int e = 0; e < m; e++) fprintf(f, "%d %d %d %d\n", ea[e], eb[e], volt[e], etree[e]);
    fclose(f);
    sprintf(fn, "%s.edges", outp);
    f = fopen(fn, "w");
    fprintf(f, "%d\n", nb * N);
    for (int e = 0; e < m; e++)
        for (int g = 0; g < N; g++) fprintf(f, "%d %d\n", ea[e] * N + g, eb[e] * N + mul[g][volt[e]]);
    fclose(f);
    printf("BEST %d\n", best);
    return 0;
}
