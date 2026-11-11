/* e05: fill leftover slots of the 34,848 graph (G34848.edges) with single hubs by simulated annealing.
 * A single hub on side X has N subset of Y (|N| = 17, all old vertices of Y with no hub neighbour yet).
 * Conditions checked on the static graph G (adding hubs only shortens distances, so they stay sufficient):
 *   (1) every X-vertex (old and orbit hubs) within distance 3 of N            -> coverage count cnt[]
 *   (2) every existing hub h on side X: N meets M2_h = ball2(N(h))            (d(h,h') <= 4)
 *   (3) every existing hub h on side Y: N meets M3_h = ball3(N(h))            (d(h,h') <= 5)
 * Cost = uncovered X-vertices + LAM * (hubs with no compatible neighbour).
 * usage: fill EDGES SINGLES_IN SINGLES_OUT SECS SEED LAM ITERS [T0 T1]
 * SINGLES file: one hub per line "A id ... id" or "B id ... id" (global ids of G, side of the new hub).
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <time.h>

#define MAXN 34944
#define NW 546
#define MD 17
#define MAXHUB 2200
#define NOLD 33792

static int n;
static int deg[MAXN], adj[MAXN][MD], side[MAXN], used[MAXN];
static uint64_t *B2, *B3, SM[2][NW];
static uint64_t *M2[MAXHUB], *M3[MAXHUB], *relM[MAXHUB];
static int hubSide[MAXHUB], hubSz[MAXHUB], hubN[MAXHUB][MD], nh = 0;
static int cnt[MAXN], inN[MAXN], N[MD], cc[MAXHUB];
static int U, V, X, Y;
static int freel[MAXN], nfree;
static double LAM = 2.0, TT0 = 1.2, TT1 = 0.03;
static unsigned long long rs = 88172645463325252ULL;
static inline unsigned long long rnd64(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline double urand(void) { return (rnd64() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }
static inline int bit(const uint64_t *a, int t) { return (a[t >> 6] >> (t & 63)) & 1; }
static inline void setb(uint64_t *a, int t) { a[t >> 6] |= 1ULL << (t & 63); }

static void make_hub_masks(int h) {
    /* M2 = union ball2(N(h)), M3 = union ball3(N(h)) = union over N(h) of OR_{u in adj} ball2(u) */
    uint64_t *m2 = M2[h], *m3 = M3[h];
    memset(m2, 0, NW * 8); memset(m3, 0, NW * 8);
    for (int k = 0; k < hubSz[h]; k++) {
        int y = hubN[h][k];
        for (int w = 0; w < NW; w++) m2[w] |= B2[(size_t)y * NW + w];
        for (int a = 0; a < deg[y]; a++) {
            int u = adj[y][a];
            for (int w = 0; w < NW; w++) m3[w] |= B2[(size_t)u * NW + w];
        }
    }
}

static void cover_update(int t, int d) {
    /* d = +1 add t, -1 remove t: update cnt over X-vertices within distance 3, U, and hub counters V */
    const uint64_t *b = B3 + (size_t)t * NW;
    for (int w = 0; w < NW; w++) {
        uint64_t mm = b[w] & SM[X][w];
        while (mm) {
            int s = w * 64 + __builtin_ctzll(mm); mm &= mm - 1;
            if (d > 0) { if (cnt[s]++ == 0) U--; }
            else { if (--cnt[s] == 0) U++; }
        }
    }
    for (int h = 0; h < nh; h++) {
        if (bit(relM[h], t)) {
            if (d > 0) { if (cc[h]++ == 0) V--; }
            else { if (--cc[h] == 0) V++; }
        }
    }
}

static int load_singles(const char *fn) {
    FILE *f = fopen(fn, "r");
    if (!f) return 0;
    char line[4096]; int cntl = 0;
    while (fgets(line, sizeof line, f)) {
        char *p = line; char s = 0; int off;
        if (sscanf(p, " %c%n", &s, &off) != 1) continue;
        p += off;
        int h = nh; hubSide[h] = (s == 'A') ? 0 : 1; hubSz[h] = 0;
        M2[h] = calloc(NW, 8); M3[h] = calloc(NW, 8);
        int v, o;
        while (sscanf(p, " %d%n", &v, &o) == 1) { hubN[h][hubSz[h]++] = v; used[v] = 1; p += o; }
        nh++; cntl++;
        make_hub_masks(h);
    }
    fclose(f);
    return cntl;
}

int main(int argc, char **argv) {
    if (argc < 8) { fprintf(stderr, "usage: fill EDGES SINGLES_IN SINGLES_OUT SECS SEED LAM ITERS [T0 T1]\n"); return 1; }
    double secs = atof(argv[4]);
    rs ^= (unsigned long long)atoll(argv[5]) * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 10; i++) rnd64();
    LAM = atof(argv[6]);
    long iters = atol(argv[7]);
    if (argc > 9) { TT0 = atof(argv[8]); TT1 = atof(argv[9]); }
    FILE *f = fopen(argv[1], "r");
    if (fscanf(f, "%d", &n) != 1) return 1;
    for (int i = 0; i < n; i++) deg[i] = 0;
    int u, v;
    while (fscanf(f, "%d %d", &u, &v) == 2) { adj[u][deg[u]++] = v; adj[v][deg[v]++] = u; }
    fclose(f);
    /* sides by BFS from 0 (A = 0) */
    for (int i = 0; i < n; i++) side[i] = -1;
    int *q = malloc(sizeof(int) * n), qh = 0, qt = 0; side[0] = 0; q[qt++] = 0;
    while (qh < qt) { int x = q[qh++]; for (int a = 0; a < deg[x]; a++) { int y = adj[x][a];
        if (side[y] < 0) { side[y] = 1 - side[x]; q[qt++] = y; } else if (side[y] == side[x]) { fprintf(stderr, "not bipartite\n"); return 1; } } }
    free(q);
    for (int i = 0; i < n; i++) setb(SM[side[i]], i);
    for (int i = 0; i < n; i++) { if (i < NOLD && deg[i] >= 17) used[i] = 1; }
    B2 = calloc((size_t)n * NW, 8);
    for (int x = 0; x < n; x++) {
        uint64_t *b = B2 + (size_t)x * NW;
        setb(b, x);
        for (int a = 0; a < deg[x]; a++) { int y = adj[x][a]; setb(b, y);
            for (int c = 0; c < deg[y]; c++) setb(b, adj[y][c]); }
    }
    /* static hubs */
    for (int h = 0; h < n - NOLD; h++) {
        int hv = NOLD + h; hubSide[nh] = side[hv]; hubSz[nh] = deg[hv];
        for (int a = 0; a < deg[hv]; a++) hubN[nh][a] = adj[hv][a];
        nh++;
    }
    int nstatic = nh;
    for (int h = 0; h < nstatic; h++) { M2[h] = calloc(NW, 8); M3[h] = calloc(NW, 8); make_hub_masks(h); }
    int nsing = load_singles(argv[2]);
    fprintf(stderr, "n=%d static hubs=%d singles loaded=%d\n", n, nstatic, nsing);
    B3 = calloc((size_t)n * NW, 8);   /* ball3 for coverage updates */
    for (int x = 0; x < n; x++) { uint64_t *b = B3 + (size_t)x * NW;
        for (int a = 0; a < deg[x]; a++) { const uint64_t *s = B2 + (size_t)adj[x][a] * NW;
            for (int w = 0; w < NW; w++) b[w] |= s[w]; } }

    double t_end = now() + secs;
    int fails[2] = {0, 0}, attempt = 0;
    while (now() < t_end) {
        X = attempt & 1; Y = 1 - X; attempt++;
        if (attempt == 1 && getenv("INIT")) { FILE *fi = fopen(getenv("INIT"), "r"); char c = 'A'; if (fi) { c = fgetc(fi); fclose(fi); } X = (c == 'B'); Y = 1 - X; }
        nfree = 0;
        for (int t = 0; t < NOLD; t++) if (side[t] == Y && !used[t]) freel[nfree++] = t;
        if (nfree < MD) { fails[X]++; if (fails[0] + fails[1] > 1000) break; continue; }
        for (int h = 0; h < nh; h++) relM[h] = (hubSide[h] == X) ? M2[h] : M3[h];
        /* init */
        memset(cnt, 0, sizeof(int) * n); memset(inN, 0, sizeof(int) * n);
        for (int h = 0; h < nh; h++) cc[h] = 0;
        int kk = 0;
        if (getenv("INIT") && attempt == 1) {   /* start from a given candidate (ids after ':' on the line) */
            FILE *fi = fopen(getenv("INIT"), "r"); char ln[4096];
            if (fi && fgets(ln, sizeof ln, fi)) { char *p = strchr(ln, ':'); int t, o; if (p) { p++;
                while (kk < MD && sscanf(p, " %d%n", &t, &o) == 1) { p += o; if (side[t] == Y && !used[t] && !inN[t]) { inN[t] = 1; N[kk++] = t; } } } }
            if (fi) fclose(fi);
            fprintf(stderr, "init from file: %d usable of 17\n", kk);
        }
        for (; kk < MD; kk++) { int t; do { t = freel[rnd64() % nfree]; } while (inN[t]); inN[t] = 1; N[kk] = t; }
        U = 0; V = 0;
        for (int s = 0; s < n; s++) if (side[s] == X) U++;
        for (int h = 0; h < nh; h++) V++;   /* counters start at 0 */
        for (int k = 0; k < MD; k++) cover_update(N[k], +1);
        int ok = 0;
        double cost = U + LAM * V;
        for (long it = 0; it < iters; it++) {
            double T = TT0 * pow(TT1 / TT0, (double)it / iters);
            int i = rnd64() % MD; int t; do { t = freel[rnd64() % nfree]; } while (inN[t]);
            int old = N[i];
            cover_update(old, -1); cover_update(t, +1);
            double nc = U + LAM * V, d = nc - cost;
            if (d <= 0 || urand() < exp(-d / T)) { N[i] = t; inN[old] = 0; inN[t] = 1; cost = nc; }
            else { cover_update(t, -1); cover_update(old, +1); }
            if (cost == 0) { ok = 1; break; }
        }
        fprintf(stderr, "attempt %d side %c: final cost %.1f (U=%d V=%d)%s\n", attempt, X ? 'B' : 'A', cost, U, V, ok ? " SUCCESS" : "");
        if (ok) {
            FILE *g = fopen(argv[3], "a");
            fprintf(g, "%c", X ? 'B' : 'A');
            for (int k = 0; k < MD; k++) fprintf(g, " %d", N[k]);
            fprintf(g, "\n"); fclose(g);
            int h = nh; hubSide[h] = X; hubSz[h] = MD;
            for (int k = 0; k < MD; k++) { hubN[h][k] = N[k]; used[N[k]] = 1; }
            M2[h] = calloc(NW, 8); M3[h] = calloc(NW, 8); make_hub_masks(h); nh++;
            fprintf(stderr, "committed single #%d on side %c\n", nh - nstatic, X ? 'B' : 'A');
        } else fails[X]++;
        /* clear counters for next attempt */
        for (int k = 0; k < MD; k++) inN[N[k]] = 0;
    }
    fprintf(stderr, "done, singles total %d\n", nh - nstatic);
    return 0;
}
