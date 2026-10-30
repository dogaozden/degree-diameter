/* mm.c: two copies of a bipartite graph G (N vertices, max degree 5, diameter 5, sides L and R of size N/2)
 * joined by two annealed bijections: L1 <-> L2 (pL) and R1 <-> R2 (pR). Copy 2 has its colour classes exchanged,
 * so the joined graph is bipartite with classes (L1 u R2) and (R1 u L2), max degree 6, n = 2N.
 * Cost = number of unordered vertex pairs at distance > 5 ("bad", same as score65), computed exactly with
 * bit-parallel radius-5 balls. Annealing over transpositions of pL or pR.
 * usage: mm COPY.edges OUT.edges ; env SECS (60) SEED (1) T0 (4) T1 (0.2) INIT (random|id)
 */
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 1024
#define MAXW 16
#define MAXD 8
static int N, H, n, W;
static int cnb[MAXN][MAXD], cdeg[MAXN];
static int pm[2][MAXN], pinv[2][MAXN];   /* pm[0] = pL, pm[1] = pR on H points */
static int nb[2 * MAXN][MAXD], nd[2 * MAXN];
static uint64_t S[2][2 * MAXN][MAXW];
static uint64_t rng_s = 88172645463325252ULL;
static inline uint64_t rnd(void) { rng_s ^= rng_s << 13; rng_s ^= rng_s >> 7; rng_s ^= rng_s << 17; return rng_s; }
static double urand(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static void build(void) {
    for (int v = 0; v < n; v++) {
        int c = v % N, off = v - c, k = 0;
        for (int j = 0; j < cdeg[c]; j++) nb[v][k++] = off + cnb[c][j];
        int mate;
        if (off == 0) mate = (c < H) ? N + pm[0][c] : N + H + pm[1][c - H];
        else          mate = (c < H) ? pinv[0][c] : H + pinv[1][c - H];
        nb[v][k++] = mate;
        nd[v] = k;
    }
}

static long cost(void) {
    build();
    int cur = 0;
    memset(S[0], 0, sizeof(S[0]));
    for (int v = 0; v < n; v++) S[0][v][v >> 6] |= 1ULL << (v & 63);
    for (int it = 0; it < 5; it++) {
        int nx = cur ^ 1;
        for (int v = 0; v < n; v++) {
            uint64_t *dst = S[nx][v];
            memcpy(dst, S[cur][v], W * 8);
            for (int k = 0; k < nd[v]; k++) {
                uint64_t *src = S[cur][nb[v][k]];
                for (int w = 0; w < W; w++) dst[w] |= src[w];
            }
        }
        cur = nx;
    }
    long tot = 0;
    for (int v = 0; v < n; v++)
        for (int w = 0; w < W; w++) tot += __builtin_popcountll(S[cur][v][w]);
    return ((long)n * n - tot) / 2;
}

static void setperm(int s, int i, int j) {  /* swap images of i and j in permutation s */
    int a = pm[s][i], b = pm[s][j];
    pm[s][i] = b; pm[s][j] = a;
    pinv[s][b] = i; pinv[s][a] = j;
}

int main(int argc, char **argv) {
    if (argc < 3) { fprintf(stderr, "usage: mm COPY.edges OUT.edges\n"); return 2; }
    FILE *f = fopen(argv[1], "r");
    if (!f || fscanf(f, "%d", &N) != 1) { fprintf(stderr, "bad copy file\n"); return 2; }
    H = N / 2; n = 2 * N; W = (n + 63) / 64;
    int u, v;
    while (fscanf(f, "%d %d", &u, &v) == 2) {
        if (cdeg[u] >= MAXD - 1 || cdeg[v] >= MAXD - 1) { fprintf(stderr, "degree too big\n"); return 2; }
        cnb[u][cdeg[u]++] = v; cnb[v][cdeg[v]++] = u;
    }
    fclose(f);
    for (int c = 0; c < N; c++) if (cdeg[c] != 5) { fprintf(stderr, "copy not 5-regular at %d\n", c); return 2; }
    double SECS = getenv("SECS") ? atof(getenv("SECS")) : 60;
    double T0 = getenv("T0") ? atof(getenv("T0")) : 4, T1 = getenv("T1") ? atof(getenv("T1")) : 0.2;
    rng_s ^= (uint64_t)(getenv("SEED") ? atoll(getenv("SEED")) : 1) * 0x9E3779B97F4A7C15ULL;
    int ident = getenv("INIT") && !strcmp(getenv("INIT"), "id");
    for (int s = 0; s < 2; s++) {
        for (int i = 0; i < H; i++) pm[s][i] = i;
        if (!ident) for (int i = H - 1; i > 0; i--) { int j = rnd() % (i + 1); int t = pm[s][i]; pm[s][i] = pm[s][j]; pm[s][j] = t; }
        for (int i = 0; i < H; i++) pinv[s][pm[s][i]] = i;
    }
    long cur = cost(), best = cur;
    int bestp[2][MAXN];
    memcpy(bestp, pm, sizeof(bestp));
    fprintf(stderr, "init cost %ld\n", cur);
    clock_t t0c = clock();
    time_t start = time(NULL);
    long it = 0, acc = 0;
    double el = 0;
    while (1) {
        if ((it & 255) == 0) {
            el = (double)(clock() - t0c) / CLOCKS_PER_SEC;
            if (el >= SECS) break;
            if ((it & 16383) == 0) fprintf(stderr, "t=%.0fs it=%ld cur=%ld best=%ld T=%.3f\n", el, it, cur, best, T0 * pow(T1 / T0, el / SECS));
        }
        double T = T0 * pow(T1 / T0, el / SECS);
        int s = rnd() & 1;
        int i = rnd() % H, j = rnd() % H;
        if (i == j) continue;
        setperm(s, i, j);
        long c2 = cost();
        long d = c2 - cur;
        if (d <= 0 || urand() < exp(-d / T)) {
            cur = c2; acc++;
            if (cur < best) { best = cur; memcpy(bestp, pm, sizeof(bestp)); }
        } else setperm(s, i, j);
        it++;
    }
    (void)start;
    fprintf(stderr, "done it=%ld acc=%ld best=%ld\n", it, acc, best);
    /* write best graph */
    memcpy(pm, bestp, sizeof(bestp));
    for (int s = 0; s < 2; s++) for (int i = 0; i < H; i++) pinv[s][pm[s][i]] = i;
    build();
    FILE *o = fopen(argv[2], "w");
    fprintf(o, "%d\n", n);
    for (int x = 0; x < n; x++) for (int k = 0; k < nd[x]; k++) if (x < nb[x][k]) fprintf(o, "%d %d\n", x, nb[x][k]);
    fclose(o);
    printf("RESULT best %ld n %d\n", best, n);
    return 0;
}
