/* e05: fill leftover slots of the 34,848 graph (G34848.edges) with single hubs by simulated annealing.
 * A single hub on side X has N subset of Y (|N| = 17, all old vertices of Y with no hub neighbour yet).
 * Conditions checked on the static graph G (adding hubs only shortens distances, so they stay sufficient):
 *   (1) every X-vertex (old and orbit hubs) within distance 3 of N            -> coverage count cnt[]
 *   (2) every existing hub h on side X: N meets M2_h = ball2(N(h))            (d(h,h') <= 4)
 *   (3) every existing hub h on side Y: N meets M3_h = ball3(N(h))            (d(h,h') <= 5)
 * Cost = uncovered X-vertices + LAM * (hubs with no compatible neighbour).
 * usage: fill EDGES SINGLES_IN SINGLES_OUT SECS SEED LAM ITERS
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
static double LAM = 2.0;
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
    /* check EDGES SINGLES_IN CANDFILE SIDE(A|B: side of the new hub) : count candidates with cost 0 */
    rs ^= 12345; for (int i = 0; i < 10; i++) rnd64();
    FILE *f = fopen(argv[1], "r");
    if (fscanf(f, "%d", &n) != 1) return 1;
    int u, v;
    while (fscanf(f, "%d %d", &u, &v) == 2) { adj[u][deg[u]++] = v; adj[v][deg[v]++] = u; }
    fclose(f);
    for (int i = 0; i < n; i++) side[i] = -1;
    int *q = malloc(sizeof(int) * n), qh = 0, qt = 0; side[0] = 0; q[qt++] = 0;
    while (qh < qt) { int x = q[qh++]; for (int a = 0; a < deg[x]; a++) { int y = adj[x][a];
        if (side[y] < 0) { side[y] = 1 - side[x]; q[qt++] = y; } } }
    for (int i = 0; i < n; i++) setb(SM[side[i]], i);
    for (int i = 0; i < n; i++) { if (i < NOLD && deg[i] >= 17) used[i] = 1; }
    B2 = calloc((size_t)n * NW, 8);
    for (int x = 0; x < n; x++) {
        uint64_t *b = B2 + (size_t)x * NW;
        setb(b, x);
        for (int a = 0; a < deg[x]; a++) { int y = adj[x][a]; setb(b, y);
            for (int c = 0; c < deg[y]; c++) setb(b, adj[y][c]); }
    }
    for (int h = 0; h < n - NOLD; h++) {
        int hv = NOLD + h; hubSide[nh] = side[hv]; hubSz[nh] = deg[hv];
        for (int a = 0; a < deg[hv]; a++) hubN[nh][a] = adj[hv][a];
        nh++;
    }
    for (int h = 0; h < nh; h++) { M2[h] = calloc(NW, 8); M3[h] = calloc(NW, 8); make_hub_masks(h); }
    load_singles(argv[2]);
    B3 = calloc((size_t)n * NW, 8);
    for (int x = 0; x < n; x++) { uint64_t *b = B3 + (size_t)x * NW;
        for (int a = 0; a < deg[x]; a++) { const uint64_t *s = B2 + (size_t)adj[x][a] * NW;
            for (int w = 0; w < NW; w++) b[w] |= s[w]; } }
    X = argv[4][0] == 'B'; Y = 1 - X;
    for (int h = 0; h < nh; h++) relM[h] = (hubSide[h] == X) ? M2[h] : M3[h];
    FILE *g = fopen(argv[3], "r");
    char line[4096]; long ncand = 0, nfreeok = 0, nok = 0, bestc = 1 << 30; int bestV = 0, bestU = 0;
    while (fgets(line, sizeof line, g)) {
        int N1[MD], k = 0, t, o; char *p = line; int bad = 0;
        while (sscanf(p, " %d%n", &t, &o) == 1 && k < MD) { N1[k++] = t; p += o; }
        if (k == 0) continue;
        ncand++;
        for (int i = 0; i < k; i++) if (side[N1[i]] != Y || used[N1[i]]) bad = 1;
        if (bad) continue;
        nfreeok++;
        memset(cnt, 0, sizeof(int) * n); memset(inN, 0, sizeof(int) * n);
        for (int h = 0; h < nh; h++) cc[h] = 0;
        U = 0; V = nh;
        for (int s = 0; s < n; s++) if (side[s] == X) U++;
        for (int i = 0; i < k; i++) { N[i] = N1[i]; cover_update(N1[i], +1); }
        if (U == 0 && V == 0) nok++;
        if (U + V < bestc) { bestc = U + V; bestU = U; bestV = V; FILE *bo = fopen("best_cand.txt", "a"); fprintf(bo, "%c %d %d :", argv[4][0], U, V); for (int i = 0; i < k; i++) fprintf(bo, " %d", N1[i]); fprintf(bo, "\n"); fclose(bo); }
    }
    printf("candidates %ld free %ld cost0 %ld best U=%d V=%d\n", ncand, nfreeok, nok, bestU, bestV);
    return 0;
}
