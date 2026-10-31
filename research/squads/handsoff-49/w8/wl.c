/* wl: simulated annealing over voltage assignments of a simple base graph lifted over a group table (w8, handsoff-49).

   Lift: vertices (u,g) = u*K+g (g in 0..K-1, identity = 0). Base edge (u,v) with voltage a gives lift edges
   (u,g) ~ (v,g*a) for all g. Left multiplication by h is an automorphism, so distances from (x,e) to (y,g) for all
   base x,y and all g decide the diameter: lift diameter <= D iff for every base x the ball of radius D around (x,e)
   contains every lift vertex.

   Evaluation (batched over roots): S[y][g] is a bitset over the b roots x: bit x set iff some walk of exactly t steps
   from (x,e) ends at (y,g). ACC accumulates S over t = 0..D. Walks may backtrack, so ACC is exactly the ball of
   radius D. Cost = (number of (root, lift vertex) pairs at distance > D); cost 0 iff the lift has diameter <= D.
   Cotree voltages are free (spanning tree voltages are 0).

   Usage: wl BASE GROUP.bin D seconds seed OUT [T0 T1]
     BASE: first line n, then edges "u v" (simple graph, n <= 256, m <= 512, any parity).
     GROUP.bin: groups.py table (int32 N, then N*N uint16, row g: g*h, identity 0), N <= 64.
     OUT.sol: "K m" then one voltage per base edge (in BASE order). OUT.edges: lift edge list, written when cost 0
     (or at exit for the best state, file OUT.best.edges).
   Prints "BEST cost=.. t=.." lines and "RESULT FOUND" when cost 0. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <time.h>

#define MAXB 256
#define MAXK 64
#define MAXW 4
#define MAXE 512

static int b, m, K, D, W;
static uint16_t MT[MAXK][MAXK];
static int INV[MAXK];
static uint8_t PERM[MAXK][MAXK]; /* PERM[v][g] = g*v */
static int eu[MAXE], ev[MAXE], volt[MAXE], istree[MAXE];
static int cot[MAXE], ncot;
static uint64_t S1[MAXB * MAXK * MAXW], S2[MAXB * MAXK * MAXW], ACC[MAXB * MAXK * MAXW];

static uint64_t rng_state = 88172645463325252ULL;
static inline uint64_t rnd(void) {
    rng_state ^= rng_state << 13; rng_state ^= rng_state >> 7; rng_state ^= rng_state << 17; return rng_state;
}
static inline double rndu(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static double now(void) { struct timespec ts; clock_gettime(CLOCK_MONOTONIC, &ts); return ts.tv_sec + 1e-9 * ts.tv_nsec; }

static int read_group(const char *fn) {
    FILE *f = fopen(fn, "rb");
    if (!f) { perror(fn); exit(1); }
    int32_t n; if (fread(&n, 4, 1, f) != 1) exit(1);
    if (n > MAXK) { fprintf(stderr, "group order %d > %d\n", n, MAXK); exit(1); }
    uint16_t buf[MAXK * MAXK];
    if (fread(buf, 2, (size_t)n * n, f) != (size_t)n * n) { fprintf(stderr, "short group file\n"); exit(1); }
    fclose(f);
    for (int g = 0; g < n; g++) for (int h = 0; h < n; h++) MT[g][h] = buf[g * n + h];
    return n;
}

static void setup_group(void) {
    for (int g = 0; g < K; g++) for (int h = 0; h < K; h++) if (MT[g][h] == 0) INV[g] = h;
    for (int v = 0; v < K; v++) for (int g = 0; g < K; g++) PERM[v][g] = (uint8_t)MT[g][v];
}

static long eval_cost(void) {
    /* arcs: 2i = (eu->ev, volt), 2i+1 = (ev->eu, inv(volt)) */
    int nb = b * K * W;
    memset(ACC, 0, sizeof(uint64_t) * nb);
    memset(S1, 0, sizeof(uint64_t) * nb);
    for (int x = 0; x < b; x++) {
        int idx = (x * K + 0) * W + x / 64;
        S1[idx] |= 1ULL << (x % 64);
        ACC[idx] |= 1ULL << (x % 64);
    }
    uint64_t *cur = S1, *nxt = S2;
    for (int t = 1; t <= D; t++) {
        memset(nxt, 0, sizeof(uint64_t) * nb);
        int any = 0;
        for (int i = 0; i < m; i++) {
            for (int dir = 0; dir < 2; dir++) {
                int src = dir ? ev[i] : eu[i];
                int dst = dir ? eu[i] : ev[i];
                int a = dir ? INV[volt[i]] : volt[i];
                const uint64_t *sb = cur + (size_t)src * K * W;
                uint64_t *db = nxt + (size_t)dst * K * W;
                for (int g = 0; g < K; g++) {
                    const uint64_t *s = sb + g * W;
                    uint64_t nz = 0;
                    for (int w = 0; w < W; w++) nz |= s[w];
                    if (!nz) continue;
                    uint64_t *d = db + (size_t)PERM[a][g] * W;
                    for (int w = 0; w < W; w++) d[w] |= s[w];
                    any = 1;
                }
            }
        }
        if (!any) break;
        for (int j = 0; j < nb; j++) ACC[j] |= nxt[j];
        uint64_t *tmp = cur; cur = nxt; nxt = tmp;
    }
    long have = 0;
    for (int j = 0; j < nb; j++) have += __builtin_popcountll(ACC[j]);
    return (long)b * b * K - have;
}

static void write_outputs(const char *out, int *vol, const char *suffix) {
    char fn[1024];
    snprintf(fn, sizeof fn, "%s%s.sol", out, suffix);
    FILE *f = fopen(fn, "w");
    fprintf(f, "%d %d\n", K, m);
    for (int i = 0; i < m; i++) fprintf(f, "%d\n", vol[i]);
    fclose(f);
    snprintf(fn, sizeof fn, "%s%s.edges", out, suffix);
    f = fopen(fn, "w");
    fprintf(f, "%d\n", b * K);
    for (int i = 0; i < m; i++) {
        int a = vol[i];
        for (int g = 0; g < K; g++) fprintf(f, "%d %d\n", eu[i] * K + g, ev[i] * K + MT[g][a]);
    }
    fclose(f);
}

int main(int argc, char **argv) {
    if (argc < 7) { fprintf(stderr, "usage: wl BASE GROUP.bin D seconds seed OUT [T0 T1]\n"); return 2; }
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
    K = read_group(argv[2]);
    setup_group();
    D = atoi(argv[3]);
    double secs = atof(argv[4]);
    rng_state ^= (uint64_t)atoll(argv[5]) * 0x9E3779B97F4A7C15ULL;
    for (int i = 0; i < 10; i++) rnd();
    const char *out = argv[6];
    double T0 = argc > 7 ? atof(argv[7]) : 3.0;
    double T1 = argc > 8 ? atof(argv[8]) : 0.05;

    /* spanning tree by BFS from vertex 0 */
    int seen[MAXB] = {0}, queue[MAXB], qh = 0, qt = 0;
    for (int i = 0; i < m; i++) istree[i] = 0;
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

    long cost = eval_cost(), best = cost;
    int bestvol[MAXE];
    memcpy(bestvol, volt, sizeof(int) * m);
    double t0 = now(), T = T0, lastprint = t0;
    long iters = 0;
    fprintf(stderr, "start cost=%ld (b=%d m=%d K=%d D=%d cotree=%d)\n", cost, b, m, K, D, ncot);
    while (cost > 0) {
        double el = now() - t0;
        if (el > secs) break;
        double frac = el / secs;
        T = T0 * pow(T1 / T0, frac);
        int c = cot[rnd() % ncot];
        int old = volt[c];
        int nv = (int)(rnd() % (K - 1));
        if (nv >= old) nv++;
        volt[c] = nv;
        long nc = eval_cost();
        iters++;
        if (nc <= cost || rndu() < exp(-(double)(nc - cost) / T)) {
            cost = nc;
            if (cost < best) {
                best = cost; memcpy(bestvol, volt, sizeof(int) * m);
            }
        } else {
            volt[c] = old;
        }
        if (now() - lastprint > 15.0) {
            lastprint = now();
            fprintf(stderr, "BEST cost=%ld cur=%ld T=%.3f t=%.0f it=%ld\n", best, cost, T, el, iters);
        }
    }
    memcpy(volt, bestvol, sizeof(int) * m);
    long fin = eval_cost();
    printf("RESULT cost=%ld iters=%ld n=%d K=%d D=%d\n", fin, iters, b * K, K, D);
    if (fin == 0) {
        write_outputs(out, volt, "");
        printf("RESULT FOUND n=%d file=%s.edges\n", b * K, out);
    } else {
        write_outputs(out, volt, ".best");
    }
    return 0;
}
