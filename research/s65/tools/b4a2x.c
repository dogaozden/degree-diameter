/* b4a2x.c: exact search over all lifts of the 2+2 base [[2,3],[3,2]] by a group G (|G| <= 128), D = 5.
 *
 * Edges (A -> B voltages): A0-B0 {1, x}, A0-B1 {1, y2, y3}, A1-B0 {z1, z2, z3}, A1-B1 {1, w}. The identities are a
 * spanning tree (A0B0, A0B1, A1B1), so every lift is isomorphic to one of these. Walk products multiply on the right.
 * Exact filter: the closed walks of length <= 4 at A0 and at B0 (own fibres) must cover G. They are generated here
 * by a DFS over the base; each uses the edge w at most once (checked), so for the walks through w the product is
 * P w^e Q and the element m is covered iff w = (P^-1 m Q^-1)^e. For fixed (x, y, z) every element missed by the
 * w-free walks gives a set of allowed w; their intersection is tested in full.
 * Automorphisms (file) reduce (x, {y2, y3}) to orbit representatives.
 * usage: b4a2x GROUP AUTFILE      [env G_ONLY=k: only the k-th canonical (x,y); NOFILTER=1: test every w]
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

typedef unsigned __int128 u128;
static int m, mul[128][128], inv_[128]; static u128 ALL;
static inline u128 bit(int x) { return ((u128)1) << x; }
static inline int pc(u128 x) { return __builtin_popcountll((uint64_t)x) + __builtin_popcountll((uint64_t)(x >> 64)); }

/* base: vertices A0=0 A1=1 B0=2 B1=3; edges with variable slots */
enum { E_X0, E_X1, E_Y0, E_Y1, E_Y2, E_Z0, E_Z1, E_Z2, E_W0, E_W1, NE };
static const int eu[NE] = {0, 0, 0, 0, 0, 1, 1, 1, 1, 1};
static const int ew[NE] = {2, 2, 3, 3, 3, 2, 2, 2, 3, 3};
static int volt[NE];
static int side[4] = {0, 0, 1, 1};

/* walk lists: each walk = sequence of (edge, dir) tokens; dir +1 = A->B */
#define MAXW 512
typedef struct { int len, e[4], d[4], wpos, hasz; } Walk;
static Walk wA[MAXW], wB[MAXW]; static int nwA, nwB;
static Walk cur; static Walk *dst; static int *ndst;
static void gen(int v, int laste, int len, int start) {
    if (len > 0 && v == start) { if (*ndst >= MAXW) exit(3); dst[(*ndst)++] = cur; }
    if (len == 4) return;
    for (int e = 0; e < NE; e++) {
        if (e == laste) continue;
        int to; if (eu[e] == v) to = ew[e]; else if (ew[e] == v) to = eu[e]; else continue;
        cur.e[len] = e; cur.d[len] = (eu[e] == v) ? 1 : -1; cur.len = len + 1;
        gen(to, e, len + 1, start);
    }
}
static void classify(Walk *W, int n) {
    for (int i = 0; i < n; i++) { W[i].wpos = -1; int c = 0; W[i].hasz = 0;
        for (int k = 0; k < W[i].len; k++) if (W[i].e[k] == E_Z0 || W[i].e[k] == E_Z1 || W[i].e[k] == E_Z2) W[i].hasz = 1;
        for (int k = 0; k < W[i].len; k++) if (W[i].e[k] == E_W1) { W[i].wpos = k; c++; }
        if (c > 1) { fprintf(stderr, "w used twice\n"); exit(3); } }
}
static inline int tok(const Walk *w, int k) { int g = volt[w->e[k]]; return w->d[k] > 0 ? g : inv_[g]; }
/* coverage of w-free walks (plus identity) */
static u128 cover_free_z(Walk *W, int n, int wantz) {   /* w-free walks with (wantz=1) or without (0) z edges */
    u128 c = 0;
    for (int i = 0; i < n; i++) { if (W[i].wpos >= 0 || W[i].hasz != wantz) continue;
        int h = 0; for (int k = 0; k < W[i].len; k++) h = mul[h][tok(&W[i], k)]; c |= bit(h); }
    return c;
}
static u128 cover_free(Walk *W, int n) {
    u128 c = bit(0);
    for (int i = 0; i < n; i++) { if (W[i].wpos >= 0) continue; int h = 0; for (int k = 0; k < W[i].len; k++) h = mul[h][tok(&W[i], k)]; c |= bit(h); }
    return c;
}
/* allowed w for missed element x: union over walks through w */
static u128 allowed(Walk *W, int n, int x) {
    u128 a = 0;
    for (int i = 0; i < n; i++) { if (W[i].wpos < 0) continue; int P = 0, Q = 0, p = W[i].wpos;
        for (int k = 0; k < p; k++) P = mul[P][tok(&W[i], k)];
        for (int k = p + 1; k < W[i].len; k++) Q = mul[Q][tok(&W[i], k)];
        int t = mul[mul[inv_[P]][x]][inv_[Q]];          /* = w^d */
        a |= bit(W[i].d[p] > 0 ? t : inv_[t]); }
    return a;
}
/* full test */
static int deg[4], an[4][12], ae[4][12], ag[4][12]; static u128 cov[4]; static int Lm;
static void dfs(int v, int laste, int h, int len) {
    cov[v] |= bit(h); if (len == Lm) return;
    for (int i = 0; i < deg[v]; i++) { if (ae[v][i] == laste) continue; dfs(an[v][i], ae[v][i], mul[h][ag[v][i]], len + 1); }
}
static int full_ok(void) {
    memset(deg, 0, sizeof deg);
    for (int e = 0; e < NE; e++) { int u = eu[e], w = ew[e];
        an[u][deg[u]] = w; ae[u][deg[u]] = e; ag[u][deg[u]] = volt[e]; deg[u]++;
        an[w][deg[w]] = u; ae[w][deg[w]] = e; ag[w][deg[w]] = inv_[volt[e]]; deg[w]++; }
    for (int s = 0; s < 4; s++) { memset(cov, 0, sizeof cov); Lm = side[s] == 0 ? 5 : 4; dfs(s, -1, 0, 0);
        for (int v = 0; v < 4; v++) { if (side[s] == 1 && side[v] == 0) continue; if (cov[v] != ALL) return 0; } }
    return 1;
}
static int naut; static int (*aut)[128];

int main(int argc, char **argv) {
    if (argc < 3) return 2;
    FILE *f = fopen(argv[1], "r"); if (!f || fscanf(f, "%d", &m) != 1 || m > 128) return 2;
    for (int i = 0; i < m; i++) for (int j = 0; j < m; j++) if (fscanf(f, "%d", &mul[i][j]) != 1) return 2;
    fclose(f);
    for (int i = 0; i < m; i++) for (int j = 0; j < m; j++) if (mul[i][j] == 0) inv_[i] = j;
    ALL = (m == 128) ? ~(u128)0 : bit(m) - 1;
    f = fopen(argv[2], "r"); if (!f || fscanf(f, "%d", &naut) != 1) return 2;
    aut = malloc(sizeof(int[128]) * naut);
    for (int a = 0; a < naut; a++) for (int x = 0; x < m; x++) if (fscanf(f, "%d", &aut[a][x]) != 1) return 2;
    fclose(f);
    int GONLY = getenv("G_ONLY") ? atoi(getenv("G_ONLY")) : -1, NOFILTER = getenv("NOFILTER") ? 1 : 0;
    dst = wA; ndst = &nwA; gen(0, -1, 0, 0); dst = wB; ndst = &nwB; gen(2, -1, 0, 2);
    classify(wA, nwA); classify(wB, nwB);
    int nwa_w = 0, nwb_w = 0; for (int i = 0; i < nwA; i++) nwa_w += wA[i].wpos >= 0; for (int i = 0; i < nwB; i++) nwb_w += wB[i].wpos >= 0;
    fprintf(stderr, "closed walks: A0 %d (%d through w), B0 %d (%d through w)\n", nwA + 1, nwa_w, nwB + 1, nwb_w);
    volt[E_X0] = 0; volt[E_Y0] = 0; volt[E_W0] = 0;
    long long ncanon = 0, nouter = 0, ncand = 0, nsol = 0; clock_t t0 = clock();
    for (int x = 1; x < m; x++) for (int y1 = 1; y1 < m; y1++) for (int y2 = y1 + 1; y2 < m; y2++) {
        int canon = 1;
        for (int a = 1; a < naut && canon; a++) {
            int X = aut[a][x], Y1 = aut[a][y1], Y2 = aut[a][y2]; if (Y2 < Y1) { int t = Y1; Y1 = Y2; Y2 = t; }
            if (X < x || (X == x && (Y1 < y1 || (Y1 == y1 && Y2 < y2)))) canon = 0;
        }
        if (!canon) continue;
        if (GONLY >= 0 && ncanon != GONLY) { ncanon++; continue; }
        ncanon++;
        volt[E_X1] = x; volt[E_Y1] = y1; volt[E_Y2] = y2;
        u128 baseA = bit(0) | cover_free_z(wA, nwA, 0), baseB = bit(0) | cover_free_z(wB, nwB, 0);
        for (int z0 = 0; z0 < m; z0++) for (int z1 = z0 + 1; z1 < m; z1++) for (int z2 = z1 + 1; z2 < m; z2++) {
            nouter++;
            volt[E_Z0] = z0; volt[E_Z1] = z1; volt[E_Z2] = z2;
            u128 C = ALL & ~bit(0);                       /* w != 1 (parallel to the tree edge) */
            if (!NOFILTER) {
                u128 missA = ALL & ~(baseA | cover_free_z(wA, nwA, 1)); if (pc(missA) > nwa_w) continue;
                u128 missB = ALL & ~(baseB | cover_free_z(wB, nwB, 1));
                if (pc(missA) > nwa_w || pc(missB) > nwb_w) continue;
                for (u128 mm = missA; mm && C; ) { uint64_t lo = (uint64_t)mm, hi = (uint64_t)(mm >> 64);
                    int e = lo ? __builtin_ctzll(lo) : 64 + __builtin_ctzll(hi); mm &= ~bit(e); C &= allowed(wA, nwA, e); }
                for (u128 mm = missB; mm && C; ) { uint64_t lo = (uint64_t)mm, hi = (uint64_t)(mm >> 64);
                    int e = lo ? __builtin_ctzll(lo) : 64 + __builtin_ctzll(hi); mm &= ~bit(e); C &= allowed(wB, nwB, e); }
            }
            for (int w = 1; w < m; w++) if (C >> w & 1) {
                ncand++; volt[E_W1] = w;
                if (full_ok()) { nsol++; printf("SOL x %d y %d %d z %d %d %d w %d\n", x, y1, y2, z0, z1, z2, w); fflush(stdout); }
            }
        }
    }
    fprintf(stderr, "m %d autos %d canonical %lld outer %lld candidates %lld solutions %lld secs %.1f\n",
            m, naut, ncanon, nouter, ncand, nsol, (double)(clock() - t0) / CLOCKS_PER_SEC);
    return 0;
}
