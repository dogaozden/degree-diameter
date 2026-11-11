/* wl2: simulated annealing over voltage assignments of a small base multigraph lifted over a group table (w8).
   Generalizes wl.c: groups up to order 2048, base up to 256 vertices, parallel base edges allowed.

   Lift: vertices (u,g) = u*K+g, identity = index 0. Base edge (u,v) with voltage a gives lift edges (u,g)~(v,g*a).
   Left multiplication by h is an automorphism of the lift, so the lift has diameter <= D iff for every base root x the
   ball of radius D around (x,e) contains every lift vertex.

   Evaluation: S[y][g] is a bitset over the b roots (W words): bit x set iff some walk of exactly t steps from (x,e)
   ends at (y,g). ACC accumulates S over t = 0..D (backtracking walks make ACC the exact ball).
   cost = (number of (root, lift vertex) pairs at distance > D) + PEN * (parallel base edges with equal voltage).
   Lift far-pair count (unordered, score48) = cost * K / 2 when the penalty is 0.

   Usage: wl2 BASE GROUP.bin D seconds seed OUT [T0 T1]
     BASE: first line n, then edge lines "u v" (multi-edges allowed, no loops, connected).
     GROUP.bin: groups.py table (int32 N, then N*N uint16, row g: g*h, identity 0), N <= 2048.
     Writes OUT.edges and OUT.sol on cost 0 (prints RESULT FOUND); otherwise OUT.best.edges and OUT.best.sol. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <time.h>

#define MAXB 256
#define MAXK 4096
#define MAXW 4
#define MAXE 512
#define PEN 1000

static int b, m, K, D, W;
static uint16_t *MT;
static int *INV;
static int eu[MAXE], ev[MAXE], volt[MAXE], istree[MAXE];
static int cot[MAXE], ncot;
static uint16_t arcperm[2 * MAXE][MAXK];
static int asrc[2 * MAXE], adst[2 * MAXE];
static uint64_t *S1, *S2, *ACC;

static uint64_t rng_state = 88172645463325252ULL;
static inline uint64_t rnd(void) {
    rng_state ^= rng_state << 13; rng_state ^= rng_state >> 7; rng_state ^= rng_state << 17; return rng_state;
}
static inline double rndu(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) { struct timespec ts; clock_gettime(CLOCK_MONOTONIC, &ts); return ts.tv_sec + 1e-9 * ts.tv_nsec; }

static void read_group(const char *fn) {
    FILE *f = fopen(fn, "rb");
    if (!f) { perror(fn); exit(1); }
    int32_t n; if (fread(&n, 4, 1, f) != 1) exit(1);
    if (n > MAXK) { fprintf(stderr, "group order %d > %d\n", n, MAXK); exit(1); }
    K = n;
    MT = malloc(sizeof(uint16_t) * (size_t)K * K);
    INV = malloc(sizeof(int) * K);
    if (fread(MT, 2, (size_t)K * K, f) != (size_t)K * K) { fprintf(stderr, "short group file\n"); exit(1); }
    fclose(f);
    for (int g = 0; g < K; g++) for (int h = 0; h < K; h++) if (MT[g * K + h] == 0) INV[g] = h;
}

static void set_arc_perms(int i) {
    /* arc 2i: eu->ev with volt[i]; arc 2i+1: ev->eu with inverse */
    int a = volt[i], ai = INV[a];
    for (int g = 0; g < K; g++) {
        arcperm[2 * i][g] = MT[g * K + a];
        arcperm[2 * i + 1][g] = MT[g * K + ai];
    }
}

static long eval_cost(void) {
    size_t nb = (size_t)b * K * W;
    memset(ACC, 0, sizeof(uint64_t) * nb);
    memset(S1, 0, sizeof(uint64_t) * nb);
    for (int x = 0; x < b; x++) {
        size_t idx = ((size_t)x * K + 0) * W + x / 64;
        S1[idx] |= 1ULL << (x % 64);
        ACC[idx] |= 1ULL << (x % 64);
    }
    uint64_t *cur = S1, *nxt = S2;
    for (int t = 1; t <= D; t++) {
        memset(nxt, 0, sizeof(uint64_t) * nb);
        int any = 0;
        for (int a = 0; a < 2 * m; a++) {
            const uint64_t *sb = cur + (size_t)asrc[a] * K * W;
            uint64_t *db = nxt + (size_t)adst[a] * K * W;
            const uint16_t *pm = arcperm[a];
            for (int g = 0; g < K; g++) {
                const uint64_t *s = sb + (size_t)g * W;
                uint64_t nz = 0;
                for (int w = 0; w < W; w++) nz |= s[w];
                if (!nz) continue;
                uint64_t *d = db + (size_t)pm[g] * W;
                for (int w = 0; w < W; w++) d[w] |= s[w];
                any = 1;
            }
        }
        if (!any) break;
        for (size_t j = 0; j < nb; j++) ACC[j] |= nxt[j];
        uint64_t *tmp = cur; cur = nxt; nxt = tmp;
    }
    long have = 0;
    for (size_t j = 0; j < nb; j++) have += __builtin_popcountll(ACC[j]);
    return (long)b * b * K - have;
}

static long dup_count(void) {
    long c = 0;
    for (int i = 0; i < m; i++) for (int j = i + 1; j < m; j++)
        if (((eu[i] == eu[j] && ev[i] == ev[j]) || (eu[i] == ev[j] && ev[i] == eu[j])) && volt[i] == volt[j]) c++;
    return c;
}

static void write_out(const char *out, const char *suffix, int *vol) {
    char fn[1024];
    snprintf(fn, sizeof fn, "%s%s.sol", out, suffix);
    FILE *f = fopen(fn, "w");
    fprintf(f, "%d %d\n", K, m);
    for (int i = 0; i < m; i++) fprintf(f, "%d\n", vol[i]);
    fclose(f);
    snprintf(fn, sizeof fn, "%s%s.edges", out, suffix);
    f = fopen(fn, "w");
    fprintf(f, "%d\n", b * K);
    for (int i = 0; i < m; i++)
        for (int g = 0; g < K; g++) fprintf(f, "%d %d\n", eu[i] * K + g, ev[i] * K + MT[g * K + vol[i]]);
    fclose(f);
}

int main(int argc, char **argv) {
    if (argc < 7) { fprintf(stderr, "usage: wl2 BASE GROUP.bin D seconds seed OUT [T0 T1]\n"); return 2; }
    FILE *bf = fopen(argv[1], "r");
    if (!bf) { perror(argv[1]); return 2; }
    int n; if (fscanf(bf, "%d", &n) != 1) return 2;
    b = n; m = 0;
    int a0, a1;
    while (fscanf(bf, "%d %d", &a0, &a1) == 2) {
        if (m >= MAXE) { fprintf(stderr, "too many base edges\n"); return 2; }
        eu[m] = a0; ev[m] = a1; m++;
    }
    fclose(bf);
    if (b > MAXB) { fprintf(stderr, "base too big\n"); return 2; }
    W = (b + 63) / 64;
    read_group(argv[2]);
    D = atoi(argv[3]);
    double secs = atof(argv[4]);
    rng_state ^= (uint64_t)atoll(argv[5]) * 0x9E3779B97F4A7C15ULL;
    for (int i = 0; i < 10; i++) rnd();
    const char *out = argv[6];
    double T0 = argc > 7 ? atof(argv[7]) : 3.0;
    double T1 = argc > 8 ? atof(argv[8]) : 0.05;

    size_t nb = (size_t)b * K * W;
    S1 = malloc(sizeof(uint64_t) * nb); S2 = malloc(sizeof(uint64_t) * nb); ACC = malloc(sizeof(uint64_t) * nb);

    for (int a = 0; a < 2 * m; a++) {
        int i = a / 2;
        asrc[a] = (a % 2 == 0) ? eu[i] : ev[i];
        adst[a] = (a % 2 == 0) ? ev[i] : eu[i];
    }
    /* spanning tree by BFS from vertex 0 */
    int seen[MAXB] = {0}, queue[MAXB], qh = 0, qt = 0;
    seen[0] = 1; queue[qt++] = 0;
    while (qh < qt) {
        int u = queue[qh++];
        for (int i = 0; i < m; i++) {
            int w = -1;
            if (eu[i] == u) w = ev[i]; else if (ev[i] == u) w = eu[i];
            if (w >= 0 && !seen[w]) { seen[w] = 1; queue[qt++] = w; istree[i] = 1; }
        }
    }
    if (qt != b) { fprintf(stderr, "base not connected\n"); return 2; }
    ncot = 0;
    for (int i = 0; i < m; i++) { if (!istree[i]) cot[ncot++] = i; volt[i] = 0; }
    for (int j = 0; j < ncot; j++) volt[cot[j]] = (int)(rnd() % K);
    for (int i = 0; i < m; i++) set_arc_perms(i);

    long cost = eval_cost() + PEN * dup_count(), best = cost;
    int *bestvol = malloc(sizeof(int) * m);
    memcpy(bestvol, volt, sizeof(int) * m);
    double t0 = now(), T = T0, lastprint = t0;
    long iters = 0;
    fprintf(stderr, "start cost=%ld (b=%d m=%d K=%d D=%d cotree=%d)\n", cost, b, m, K, D, ncot);
    while (cost > 0) {
        double el = now() - t0;
        if (el > secs) break;
        T = T0 * pow(T1 / T0, el / secs);
        int c = cot[rnd() % ncot];
        int old = volt[c];
        int nv = (int)(rnd() % (K - 1));
        if (nv >= old) nv++;
        volt[c] = nv;
        set_arc_perms(c);
        long nc = eval_cost() + PEN * dup_count();
        iters++;
        if (nc <= cost || rndu() < exp(-(double)(nc - cost) / T)) {
            cost = nc;
            if (cost < best) { best = cost; memcpy(bestvol, volt, sizeof(int) * m); }
        } else {
            volt[c] = old;
            set_arc_perms(c);
        }
        if (now() - lastprint > 15.0) {
            lastprint = now();
            fprintf(stderr, "BEST cost=%ld cur=%ld T=%.3f t=%.0f it=%ld\n", best, cost, T, el, iters);
        }
    }
    memcpy(volt, bestvol, sizeof(int) * m);
    for (int i = 0; i < m; i++) set_arc_perms(i);
    long fin = eval_cost() + PEN * dup_count();
    printf("RESULT cost=%ld iters=%ld n=%d K=%d D=%d b=%d\n", fin, iters, b * K, K, D, b);
    if (fin == 0) {
        write_out(out, "", volt);
        printf("RESULT FOUND n=%d file=%s.edges\n", b * K, out);
    } else {
        write_out(out, ".best", volt);
    }
    return 0;
}
