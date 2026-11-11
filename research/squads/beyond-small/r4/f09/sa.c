/* f09 (round 4, side A): simulated-annealing packer for Z11 half-orbits of hubs on side A of G.
 * Graph G = data/d16D5_n33792.edges: A = ids [0,H), B = ids [H,2H), H = 16896. Side-A hubs have bases N in B.
 * A Z11 half-orbit with base N (|N| <= 17, B-locals) is the 11 hubs N+u, u in {0,2,...,20} (block shift on B-locals).
 * Conditions for a new base N (same as build_d17D5_hubs.py, applied to every hub of the orbit):
 *   (1) cover: every A-vertex of G is within distance 3 of N                       -> U = #uncovered A-vertices
 *   (2) compat: every existing side-A hub N' (all 22 translates) meets ball2(N)      -> H0 = #hubs with no hit
 *   (3) self: for even s != 0, N+s meets ball2(N)                                    -> S0 = #shifts failing
 *   (4) disjoint: N's vertices are unused, and no two of N share (j,x,parity of h)  (N+u disjoint from N)
 * Cost = U + LAM*H0 + MU*S0, simulated annealing over the swap of one base vertex. Each zero-cost base is accepted
 * (its 11 hubs are added), then the next base is searched against the enlarged hub set.
 * usage: sa EDGES STARTA OUTHUBS SECS SEED ITERS K
 *   STARTA: full orbits (one base per line, global ids >= H). Output: one hub per line, global ids, all side-A hubs.
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <time.h>

#define H 16896
#define NV 33792
#define W 264
#define MAXHUB 4000
#define R2L 256
#define NCLS (768 * 2)

static int adjg[NV][16];
static int *R2;                 /* H*R2L: B-locals within distance 2 of b (with multiplicity) */
static uint64_t *D3;            /* H*W: A-locals within distance 3 of b (incl. distance 1) */
static int hubN[MAXHUB][17], hubSz[MAXHUB], nh = 0;
static int hubOf[H];
static int wc[H], cnt[H], hitc[MAXHUB], inN[H];
static int U, H0;
static int Nc[17], K = 17;
static int occ[NCLS];
static int freeList[H], nfree;
static double LAM = 2.0, MU = 2.0;
static unsigned long long rs = 88172645463325252ULL;
static inline unsigned long long rnd64(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline double urand(void) { return (rnd64() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }

static inline int shl(int b, int s) {
    int blk = b >> 8, j = blk / 22, h = blk % 22;
    return ((j * 22 + (h + s) % 22) << 8) | (b & 255);
}
static inline int cls(int b) { int blk = b >> 8, j = blk / 22, h = blk % 22; return ((j * 256 + (b & 255)) << 1) | (h & 1); }

static void addv(int x) {
    const int *r = R2 + (size_t)x * R2L;
    for (int k = 0; k < R2L; k++) { int y = r[k]; if (wc[y]++ == 0 && hubOf[y] >= 0) { if (hitc[hubOf[y]]++ == 0) H0--; } }
    const uint64_t *d = D3 + (size_t)x * W;
    for (int w = 0; w < W; w++) { uint64_t m = d[w]; while (m) { int a = w * 64 + __builtin_ctzll(m); m &= m - 1; if (cnt[a]++ == 0) U--; } }
    inN[x] = 1; occ[cls(x)]++;
}
static void remv(int x) {
    const int *r = R2 + (size_t)x * R2L;
    for (int k = 0; k < R2L; k++) { int y = r[k]; if (--wc[y] == 0 && hubOf[y] >= 0) { if (--hitc[hubOf[y]] == 0) H0++; } }
    const uint64_t *d = D3 + (size_t)x * W;
    for (int w = 0; w < W; w++) { uint64_t m = d[w]; while (m) { int a = w * 64 + __builtin_ctzll(m); m &= m - 1; if (--cnt[a] == 0) U++; } }
    inN[x] = 0; occ[cls(x)]--;
}
static double cost(void) {
    int S0 = 0;
    for (int s = 2; s <= 20; s += 2) {
        int ok = 0;
        for (int i = 0; i < K && !ok; i++) if (wc[shl(Nc[i], s)] > 0) ok = 1;
        if (!ok) S0++;
    }
    return U + LAM * H0 + MU * S0;
}
static void reset_candidate(void) {
    memset(wc, 0, sizeof wc); memset(cnt, 0, sizeof cnt); memset(inN, 0, sizeof inN); memset(occ, 0, sizeof occ);
    memset(hitc, 0, sizeof(int) * nh);
    U = H; H0 = nh; nfree = 0;
    for (int b = 0; b < H; b++) if (hubOf[b] < 0) freeList[nfree++] = b;
}

int main(int argc, char **argv) {
    if (argc < 8) { fprintf(stderr, "usage: sa EDGES STARTA OUTHUBS SECS SEED ITERS K\n"); return 1; }
    double secs = atof(argv[4]);
    rs ^= (unsigned long long)atoll(argv[5]) * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 10; i++) rnd64();
    long iters = atol(argv[6]);
    K = atoi(argv[7]);
    if (getenv("LAM")) LAM = atof(getenv("LAM"));
    if (getenv("MU")) MU = atof(getenv("MU"));
    FILE *f = fopen(argv[1], "r");
    int n; if (fscanf(f, "%d", &n) != 1 || n != NV) { fprintf(stderr, "bad n\n"); return 1; }
    static int deg[NV];
    int u, v;
    while (fscanf(f, "%d %d", &u, &v) == 2) {
        if (deg[u] >= 16 || deg[v] >= 16) { fprintf(stderr, "degree > 16\n"); return 1; }
        adjg[u][deg[u]++] = v; adjg[v][deg[v]++] = u;
    }
    fclose(f);
    for (int i = 0; i < NV; i++) if (deg[i] != 16) { fprintf(stderr, "not 16-regular at %d\n", i); return 1; }
    R2 = malloc(sizeof(int) * (size_t)H * R2L);
    D3 = calloc((size_t)H * W, 8);
    for (int b = 0; b < H; b++) {
        int g = H + b, idx = 0;
        for (int i = 0; i < 16; i++) { int a = adjg[g][i];                       /* A-vertex (global = local) */
            for (int j = 0; j < 16; j++) { int y = adjg[a][j];                    /* B-vertex */
                R2[(size_t)b * R2L + idx++] = y - H;
                for (int k = 0; k < 16; k++) { int a2 = adjg[y][k];               /* A-vertex at distance 3 from g */
                    D3[(size_t)b * W + (a2 >> 6)] |= 1ULL << (a2 & 63); } } }
        for (int i = 0; i < 16; i++) { int a = adjg[g][i]; D3[(size_t)b * W + (a >> 6)] |= 1ULL << (a & 63); }
        if (idx != R2L) { fprintf(stderr, "R2 size\n"); return 1; }
    }
    /* existing side-A hubs: expand full orbits */
    for (int b = 0; b < H; b++) hubOf[b] = -1;
    FILE *fa = fopen(argv[2], "r"); char line[4096]; int nbases = 0;
    while (fgets(line, sizeof line, fa)) {
        int x, off, m = 0, base[17]; char *q = line;
        while (sscanf(q, "%d%n", &x, &off) == 1) { q += off; base[m++] = x - H; }
        if (m == 0) continue;
        nbases++;
        for (int t = 0; t < 22; t++) {
            int h = nh++; hubSz[h] = m;
            for (int i = 0; i < m; i++) { int b = shl(base[i], t); if (hubOf[b] >= 0) { fprintf(stderr, "overlap\n"); return 1; } hubOf[b] = h; hubN[h][i] = b; }
        }
    }
    fclose(fa);
    fprintf(stderr, "bases %d, existing side-A hubs %d\n", nbases, nh);
    int nstart = nh;
    int nfreeAll = 0; for (int b = 0; b < H; b++) if (hubOf[b] < 0) nfreeAll++;
    fprintf(stderr, "free B-vertices %d\n", nfreeAll);

    double t_end = now() + secs, tstart = now();
    int found = 0, tries = 0;
    long hist[8] = {0};
    while (now() < t_end) {
        tries++;
        reset_candidate();
        /* random initial base: K free vertices, distinct classes */
        int nN = 0;
        for (int tt = 0; tt < 100000 && nN < K; tt++) {
            int y = freeList[rnd64() % nfree];
            if (inN[y] || occ[cls(y)]) continue;
            Nc[nN++] = y; addv(y);
        }
        if (nN < K) { fprintf(stderr, "init failed\n"); break; }
        double cur = cost(), best = cur;
        double T0 = 2.0, T1 = 0.05;
        long it;
        for (it = 0; it < iters && cur > 0; it++) {
            double T = T0 * pow(T1 / T0, (double)it / iters);
            int i = rnd64() % K; int xo = Nc[i];
            remv(xo);
            int y = -1;
            for (int tt = 0; tt < 50; tt++) { int c = freeList[rnd64() % nfree]; if (hubOf[c] < 0 && !inN[c] && occ[cls(c)] == 0) { y = c; break; } }
            if (y < 0) { addv(xo); continue; }
            addv(y); Nc[i] = y;
            double nw = cost(); double d = nw - cur;
            if (d <= 0 || urand() < exp(-d / T)) { cur = nw; if (cur < best) best = cur; }
            else { remv(y); Nc[i] = xo; addv(xo); }
        }
        int hb = (int)(best > 7 ? 7 : best); hist[hb]++;
        if (cur == 0) {
            found++;
            /* accept: add the 11 hubs N+u, u even; leave the candidate state, rebuilt at next reset */
            for (int uu = 0; uu < 22; uu += 2) {
                int h = nh++; hubSz[h] = K;
                for (int i = 0; i < K; i++) { int b = shl(Nc[i], uu); hubOf[b] = h; hubN[h][i] = b; }
            }
            fprintf(stderr, "[%.1fs] try %d: FOUND base (%d hubs total on side A, %d orbits added)\n",
                    now() - tstart, tries, nh, found);
        } else {
            if (tries <= 3 || tries % 10 == 0) fprintf(stderr, "[%.1fs] try %d: best cost %.1f (U=%d H0=%d) iters %ld\n", now() - tstart, tries, best, U, H0, it);
        }
    }
    fprintf(stderr, "tries %d found %d; best-cost histogram 0..6+: ", tries, found);
    for (int i = 0; i < 8; i++) fprintf(stderr, "%ld ", hist[i]);
    fprintf(stderr, "\nside-A hubs %d (new %d)\n", nh, nh - nstart);
    FILE *fo = fopen(argv[3], "w");
    for (int h = 0; h < nh; h++) { for (int i = 0; i < hubSz[h]; i++) fprintf(fo, "%d ", H + hubN[h][i]); fprintf(fo, "\n"); }
    fclose(fo);
    return 0;
}
