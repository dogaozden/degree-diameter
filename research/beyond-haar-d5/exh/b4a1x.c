/* b4a1x.c: exact search over all lifts of the 2+2 base [[1,4],[4,1]] by a group G (any group, |G| <= 128), D = 5.
 *
 * Base: A0-B0 one edge (voltage 1), A0-B1 four edges (1, g2, g3, g4), A1-B0 four edges (1, d2, d3, d4) (oriented
 * A1 -> B0), A1-B1 one edge (c). This is a spanning-tree normalisation, so every lift of the base is isomorphic to
 * one of these. Walk products multiply on the right ((a,h) ~ (b, h x) for an edge a -> b of voltage x).
 * Filter (exact, no solution is lost): the closed walks of length <= 4 at A0 are
 *   {1} u {g_i g_j^-1} u {g_i g_j^-1 g_k g_l^-1 (NB)} u {d_j^-1 d_k}  u  W u W^-1,   W = {g_i c^-1 d_j},
 * and at B0 they are {1} u {d_j^-1 d_k} u {d^-1 d d^-1 d (NB)} u {g_i g_k^-1}  u  W u W^-1 (the same W).
 * Both self-fibres must be all of G, so the elements missed by the c-free parts must lie in W u W^-1, which gives
 * for each missed m the 32 values c = d_j m^-1 g_i or d_j m g_i. Survivors get the full diameter test.
 * Automorphisms of G (optional file) reduce g to orbit representatives (G acts on lifts by applying an automorphism
 * to every voltage).
 * usage: b4a1x GROUP [AUTFILE]     AUTFILE: k, then k lines of m images (element 0 = identity)
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

typedef unsigned __int128 u128;
static int m; static int mul[128][128], inv_[128];
static u128 ALL;
static int nsub; static int (*sub)[3];
static u128 *R1, *L1, *UA, *UL;
static int naut; static int GONLY_quiet = 0; static int (*aut)[128];

static inline u128 bit(int x) { return ((u128)1) << x; }
static inline int M3(int a, int b, int c) { return mul[mul[a][b]][c]; }

/* ---- full test of a lift of the base ---- */
static int side[4] = {0, 0, 1, 1};
static int eu[10], ew[10], ev[10];
static int deg[4], an[4][10], ae[4][10], ag[4][10];
static u128 cov[4];
static int L_;
static void dfs(int v, int laste, int h, int len) {
    cov[v] |= bit(h);
    if (len == L_) return;
    for (int i = 0; i < deg[v]; i++) { if (ae[v][i] == laste) continue; dfs(an[v][i], ae[v][i], mul[h][ag[v][i]], len + 1); }
}
static int full_ok(const int *g, const int *d, int c) {
    int E = 0;
    eu[E] = 0; ew[E] = 2; ev[E] = 0; E++;                                   /* A0-B0 */
    eu[E] = 0; ew[E] = 3; ev[E] = 0; E++;                                   /* A0-B1 */
    for (int i = 0; i < 3; i++) { eu[E] = 0; ew[E] = 3; ev[E] = g[i]; E++; }
    eu[E] = 1; ew[E] = 2; ev[E] = 0; E++;                                   /* A1-B0 */
    for (int i = 0; i < 3; i++) { eu[E] = 1; ew[E] = 2; ev[E] = d[i]; E++; }
    eu[E] = 1; ew[E] = 3; ev[E] = c; E++;                                   /* A1-B1 */
    memset(deg, 0, sizeof deg);
    for (int e = 0; e < E; e++) { int u = eu[e], w = ew[e];
        an[u][deg[u]] = w; ae[u][deg[u]] = e; ag[u][deg[u]] = ev[e]; deg[u]++;
        an[w][deg[w]] = u; ae[w][deg[w]] = e; ag[w][deg[w]] = inv_[ev[e]]; deg[w]++; }
    for (int s = 0; s < 4; s++) {
        memset(cov, 0, sizeof cov); L_ = side[s] == 0 ? 5 : 4; dfs(s, -1, 0, 0);
        for (int v = 0; v < 4; v++) { if (side[s] == 1 && side[v] == 0) continue; if (cov[v] != ALL) return 0; }
    }
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 2) return 2;
    FILE *f = fopen(argv[1], "r"); if (!f || fscanf(f, "%d", &m) != 1 || m > 128) return 2;
    for (int i = 0; i < m; i++) for (int j = 0; j < m; j++) if (fscanf(f, "%d", &mul[i][j]) != 1) return 2;
    fclose(f);
    for (int i = 0; i < m; i++) for (int j = 0; j < m; j++) if (mul[i][j] == 0) inv_[i] = j;
    ALL = (m == 128) ? ~(u128)0 : (bit(m) - 1);
    naut = 1; aut = malloc(sizeof(int[128]));
    for (int x = 0; x < m; x++) aut[0][x] = x;
    if (argc > 2) { f = fopen(argv[2], "r"); int k; if (!f || fscanf(f, "%d", &k) != 1) return 2;
        aut = realloc(aut, sizeof(int[128]) * (k + 1)); naut = 0;
        for (int a = 0; a < k; a++) { for (int x = 0; x < m; x++) if (fscanf(f, "%d", &aut[naut][x]) != 1) return 2; naut++; }
        fclose(f); }
    /* all 3-subsets of non-identity elements, i < j < k */
    nsub = 0; sub = malloc(sizeof(int[3]) * 400000);
    for (int a = 1; a < m; a++) for (int b = a + 1; b < m; b++) for (int c = b + 1; c < m; c++) { sub[nsub][0] = a; sub[nsub][1] = b; sub[nsub][2] = c; nsub++; }
    R1 = calloc(nsub, sizeof(u128)); L1 = calloc(nsub, sizeof(u128)); UA = calloc(nsub, sizeof(u128)); UL = calloc(nsub, sizeof(u128));
    for (int s = 0; s < nsub; s++) {
        int x[4] = {0, sub[s][0], sub[s][1], sub[s][2]};
        u128 r = 0, l = 0, r2 = 0, l2 = 0;
        for (int i = 0; i < 4; i++) for (int j = 0; j < 4; j++) if (i != j) {
            r |= bit(mul[x[i]][inv_[x[j]]]); l |= bit(mul[inv_[x[i]]][x[j]]);
            for (int k = 0; k < 4; k++) if (k != j) for (int q = 0; q < 4; q++) if (q != k) {
                r2 |= bit(mul[mul[x[i]][inv_[x[j]]]][mul[x[k]][inv_[x[q]]]]);
                l2 |= bit(mul[mul[inv_[x[i]]][x[j]]][mul[inv_[x[k]]][x[q]]]);
            }
        }
        R1[s] = r; L1[s] = l; UA[s] = bit(0) | r | r2; UL[s] = bit(0) | l | l2;
    }
    /* canonical g: subset is the lexicographically smallest image under the automorphisms */
    long long npairs = 0, ncand = 0, nsol = 0, ncanon = 0; clock_t t0 = clock();
    int GONLY = getenv("G_ONLY") ? atoi(getenv("G_ONLY")) : -1, NOFILTER = getenv("NOFILTER") ? 1 : 0;
    for (int s = 0; s < nsub; s++) {
        if (GONLY >= 0 && s != GONLY) continue;
        int canon = 1;
        for (int a = 1; a < naut && canon; a++) {
            int y[3] = {aut[a][sub[s][0]], aut[a][sub[s][1]], aut[a][sub[s][2]]};
            for (int i = 0; i < 3; i++) for (int j = i + 1; j < 3; j++) if (y[j] < y[i]) { int t = y[i]; y[i] = y[j]; y[j] = t; }
            for (int i = 0; i < 3; i++) { if (y[i] < sub[s][i]) { canon = 0; break; } if (y[i] > sub[s][i]) break; }
        }
        if (!canon) continue;
        ncanon++;
        int gg[4] = {0, sub[s][0], sub[s][1], sub[s][2]};
        u128 ua = UA[s], rg = R1[s];
        for (int t = 0; t < nsub; t++) {
            npairs++;
            u128 miss = ALL & ~(ua | L1[t]);            /* A0 */
            miss |= ALL & ~(UL[t] | rg);                 /* B0 */
            if (NOFILTER) miss = 0;
            if (__builtin_popcountll((uint64_t)miss) + __builtin_popcountll((uint64_t)(miss >> 64)) > 32) continue;
            int dd[4] = {0, sub[t][0], sub[t][1], sub[t][2]};
            u128 C = ALL;
            for (u128 mm = miss; mm && C; ) {
                uint64_t lo = (uint64_t)mm, hi = (uint64_t)(mm >> 64);
                int x = lo ? __builtin_ctzll(lo) : 64 + __builtin_ctzll(hi);
                mm &= ~bit(x);
                u128 al = 0; int xi = inv_[x];
                for (int j = 0; j < 4; j++) for (int i = 0; i < 4; i++) { al |= bit(M3(dd[j], xi, gg[i])); al |= bit(M3(dd[j], x, gg[i])); }
                C &= al;
            }
            for (int c = 0; c < m; c++) if (C >> c & 1) {
                ncand++;
                if (full_ok(sub[s], sub[t], c)) {
                    nsol++;
                    if (!GONLY_quiet) printf("SOL g %d %d %d d %d %d %d c %d\n", sub[s][0], sub[s][1], sub[s][2], sub[t][0], sub[t][1], sub[t][2], c);
                    fflush(stdout);
                }
            }
        }
    }
    fprintf(stderr, "m %d autos %d subsets %d canonical %lld pairs %lld candidates %lld solutions %lld secs %.1f\n",
            m, naut, nsub, ncanon, npairs, ncand, nsol, (double)(clock() - t0) / CLOCKS_PER_SEC);
    return 0;
}
