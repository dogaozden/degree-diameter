/* b4a2y.c: exact search over all lifts of the 2+2 base [[2,3],[3,2]] by a group G (|G| <= 128), D = 5.
 * Same lifts and the same final test as ../../beyond-haar-d5/exh/b4a2x.c, organised for speed:
 *
 * Edges (A -> B voltages): A0-B0 {1, x}, A0-B1 {1, y1, y2}, A1-B0 {z0, z1, z2}, A1-B1 {1, w}; an edge a -> b of
 * voltage g joins (a, h) and (b, h g). The identities are a spanning tree, so every lift is equivalent to one of these.
 * Symmetries used (each maps lifts to isomorphic lifts):
 *   - automorphisms of G (generators read from a file; orbits by union-find on the (x, {y1, y2}) states);
 *   - x -> x^-1 (relabel the B0 fibre by right multiplication with x^-1; z_i -> z_i x^-1);
 *   - Y = {1, y1, y2} -> Y y^-1 for y in Y (relabel B1 by y^-1, then A1 by y);
 *   - w -> w^-1 for fixed (x, Y) (relabel A1 by w^-1; z_i -> w^-1 z_i);
 *   - the base rotation A0 <-> A1, B0 <-> B1, which after renormalising gives x' = w and w' = z0 x z0^-1. With
 *     cls(g) = the orbit of g under Aut(G) and inversion (numbered by its smallest element), the Y translations,
 *     x inversion and w inversion keep cls(x) and cls(w), so we may require cls(x) <= cls(w).
 * Search: for each canonical (x, Y) and each w with w <= w^-1, the closed walks of length <= 4 at A0 and at B0 (own
 * fibres; they must cover G) are split by which z slots they use. Walks without z give a base cover; walks using one
 * slot give per-value bitsets S(v); walks using two or three slots are evaluated in the z0 < z1 < z2 loops, with
 * counting bounds that prune a branch as soon as the remaining walks cannot cover the missed elements. Survivors get the
 * full test (all four fibres, as b4a2x full_ok). Every candidate triple that is not pruned by a valid bound is tested.
 * usage: b4a2y GROUP AUTGENS      (GROUP: m then the m x m table, identity 0; AUTGENS: k then k image lists)
 *   env X_ONLY=k: only the k-th canonical (x, Y) (0-based);  NOSYM=1: no symmetry at all (for validation).
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

enum { E_X0, E_X1, E_Y0, E_Y1, E_Y2, E_Z0, E_Z1, E_Z2, E_W0, E_W1, NE };
static const int eu[NE] = {0, 0, 0, 0, 0, 1, 1, 1, 1, 1};
static const int ew[NE] = {2, 2, 3, 3, 3, 2, 2, 2, 3, 3};
static int volt[NE];
static const int side[4] = {0, 0, 1, 1};

#define MAXW 512
typedef struct { int len, e[4], d[4], mask; } Walk;
static Walk cur;
/* walk classes per source (0 = A0, 1 = B0): by z-slot mask */
static Walk W0[2][MAXW], W1[2][MAXW], W2[2][MAXW], W3[2][MAXW]; static int n0[2], n1[2], n2[2], n3[2];
static int src;
static void gen(int v, int laste, int len, int start) {
    if (len > 0 && v == start) {
        int mask = 0; for (int k = 0; k < cur.len; k++) if (cur.e[k] >= E_Z0 && cur.e[k] <= E_Z2) mask |= 1 << (cur.e[k] - E_Z0);
        cur.mask = mask;
        if (mask == 0) W0[src][n0[src]++] = cur;
        else if (mask == 1) W1[src][n1[src]++] = cur;          /* slot 0 only (slots 1, 2 by symmetry) */
        else if (mask == 3) W2[src][n2[src]++] = cur;          /* slots 0, 1 (other pairs by symmetry) */
        else if (mask == 7) W3[src][n3[src]++] = cur;
    }
    if (len == 4) return;
    for (int e = 0; e < NE; e++) {
        if (e == laste) continue;
        int to; if (eu[e] == v) to = ew[e]; else if (ew[e] == v) to = eu[e]; else continue;
        cur.e[len] = e; cur.d[len] = (eu[e] == v) ? 1 : -1; cur.len = len + 1;
        gen(to, e, len + 1, start);
    }
}
static inline int prod(const Walk *w) {
    int h = 0;
    for (int k = 0; k < w->len; k++) { int g = volt[w->e[k]]; h = mul[h][w->d[k] > 0 ? g : inv_[g]]; }
    return h;
}
static inline u128 cover(const Walk *W, int n) { u128 c = 0; for (int i = 0; i < n; i++) c |= bit(prod(&W[i])); return c; }

/* full test (as b4a2x) */
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

static int *uf;
static int find(int a) { while (uf[a] != a) { uf[a] = uf[uf[a]]; a = uf[a]; } return a; }
static void unite(int a, int b) { a = find(a); b = find(b); if (a == b) return; if (a < b) uf[b] = a; else uf[a] = b; }
static inline int sidx(int x, int a, int b) { if (a > b) { int t = a; a = b; b = t; } return (x * m + a) * m + b; }

int main(int argc, char **argv) {
    if (argc < 3) return 2;
    FILE *f = fopen(argv[1], "r"); if (!f || fscanf(f, "%d", &m) != 1 || m > 128) return 2;
    for (int i = 0; i < m; i++) for (int j = 0; j < m; j++) if (fscanf(f, "%d", &mul[i][j]) != 1) return 2;
    fclose(f);
    for (int i = 0; i < m; i++) for (int j = 0; j < m; j++) if (mul[i][j] == 0) inv_[i] = j;
    ALL = (m == 128) ? ~(u128)0 : bit(m) - 1;
    int ngen; f = fopen(argv[2], "r"); if (!f || fscanf(f, "%d", &ngen) != 1) return 2;
    int (*gens)[128] = malloc(sizeof(int[128]) * (ngen + 1));
    for (int a = 0; a < ngen; a++) for (int x = 0; x < m; x++) if (fscanf(f, "%d", &gens[a][x]) != 1) return 2;
    fclose(f);
    int XONLY = getenv("X_ONLY") ? atoi(getenv("X_ONLY")) : -1, NOSYM = getenv("NOSYM") ? 1 : 0;

    for (src = 0; src < 2; src++) gen(src == 0 ? 0 : 2, -1, 0, src == 0 ? 0 : 2);
    fprintf(stderr, "closed walks A0: %d z-free, %d one slot, %d two, %d three; B0: %d, %d, %d, %d\n",
            n0[0], n1[0], n2[0], n3[0], n0[1], n1[1], n2[1], n3[1]);

    /* orbits of states (x, {a, b}) */
    long ns = (long)m * m * m; uf = malloc(sizeof(int) * ns);
    for (long i = 0; i < ns; i++) uf[i] = (int)i;
    if (!NOSYM) {
        for (int x = 1; x < m; x++) for (int a = 1; a < m; a++) for (int b = a + 1; b < m; b++) {
            int s = sidx(x, a, b);
            for (int g = 0; g < ngen; g++) unite(s, sidx(gens[g][x], gens[g][a], gens[g][b]));
            unite(s, sidx(inv_[x], a, b));
            unite(s, sidx(x, inv_[a], mul[b][inv_[a]]));          /* Y a^-1 = {a^-1, 1, b a^-1} */
            unite(s, sidx(x, mul[a][inv_[b]], inv_[b]));          /* Y b^-1 */
        }
    }
    /* element classes under Aut(G) and inversion (for the rotation symmetry) */
    int *euf = malloc(sizeof(int) * m), cls[128];
    for (int g = 0; g < m; g++) euf[g] = g;
    #define EFIND(a) ({ int _a = (a); while (euf[_a] != _a) _a = euf[_a]; _a; })
    for (int g = 0; g < m; g++) { int t[24], nt = 0; t[nt++] = inv_[g]; for (int k = 0; k < ngen && nt < 24; k++) t[nt++] = gens[k][g];
        for (int k = 0; k < nt; k++) { int r1 = EFIND(g), r2 = EFIND(t[k]); if (r1 < r2) euf[r2] = r1; else if (r2 < r1) euf[r1] = r2; } }
    for (int g = 0; g < m; g++) cls[g] = NOSYM ? 0 : EFIND(g);
    long ncanon = 0, nw = 0, nfull = 0, nsol = 0; clock_t t0 = clock();
    u128 S[2][128];
    volt[E_X0] = 0; volt[E_Y0] = 0; volt[E_W0] = 0;
    for (int x = 1; x < m; x++) for (int a = 1; a < m; a++) for (int b = a + 1; b < m; b++) {
        int s = sidx(x, a, b); if (find(s) != s) continue;
        if (XONLY >= 0 && ncanon != XONLY) { ncanon++; continue; }
        ncanon++;
        volt[E_X1] = x; volt[E_Y1] = a; volt[E_Y2] = b;
        for (int w = 1; w < m; w++) {
            if (!NOSYM && (inv_[w] < w || cls[w] < cls[x])) continue;
            nw++; volt[E_W1] = w;
            u128 c0[2]; for (int t = 0; t < 2; t++) c0[t] = bit(0) | cover(W0[t], n0[t]);
            for (int v = 0; v < m; v++) { volt[E_Z0] = v; for (int t = 0; t < 2; t++) S[t][v] = cover(W1[t], n1[t]); }
            int b1[2], b2[2], b3[2];
            for (int t = 0; t < 2; t++) { b1[t] = 2 * n1[t] + 3 * n2[t] + n3[t]; b2[t] = n1[t] + 2 * n2[t] + n3[t]; b3[t] = 2 * n2[t] + n3[t]; }
            for (int z0 = 0; z0 < m; z0++) {
                u128 c1[2]; int ok = 1;
                for (int t = 0; t < 2; t++) { c1[t] = c0[t] | S[t][z0]; if (pc(ALL & ~c1[t]) > b1[t]) ok = 0; }
                if (!ok) continue;
                for (int z1 = z0 + 1; z1 < m; z1++) {
                    u128 c2[2]; ok = 1;
                    volt[E_Z0] = z0; volt[E_Z1] = z1;
                    for (int t = 0; t < 2 && ok; t++) { c2[t] = c1[t] | S[t][z1] | cover(W2[t], n2[t]); if (pc(ALL & ~c2[t]) > b2[t]) ok = 0; }
                    if (!ok) continue;
                    u128 m2A = ALL & ~c2[0], m2B = ALL & ~c2[1];
                    for (int z2 = z1 + 1; z2 < m; z2++) {
                        u128 rA = m2A & ~S[0][z2]; if (pc(rA) > b3[0]) continue;
                        u128 rB = m2B & ~S[1][z2]; if (pc(rB) > b3[1]) continue;
                        /* pairs (z0, z2) and (z1, z2) via the slot-(0,1) walks, triples via slot-(0,1,2) walks */
                        volt[E_Z0] = z0; volt[E_Z1] = z2; rA &= ~cover(W2[0], n2[0]); if (!rA) goto A_ok;
                        volt[E_Z0] = z1; volt[E_Z1] = z2; rA &= ~cover(W2[0], n2[0]); if (rA) continue;
                      A_ok:
                        volt[E_Z0] = z0; volt[E_Z1] = z2; rB &= ~cover(W2[1], n2[1]);
                        if (rB) { volt[E_Z0] = z1; volt[E_Z1] = z2; rB &= ~cover(W2[1], n2[1]); }
                        if (rB && n3[1]) { volt[E_Z0] = z0; volt[E_Z1] = z1; volt[E_Z2] = z2; rB &= ~cover(W3[1], n3[1]); }
                        if (rB) continue;
                        nfull++;
                        volt[E_Z0] = z0; volt[E_Z1] = z1; volt[E_Z2] = z2;
                        if (full_ok()) { nsol++; printf("SOL x %d y %d %d z %d %d %d w %d\n", x, a, b, z0, z1, z2, w); fflush(stdout); }
                    }
                }
            }
        }
    }
    fprintf(stderr, "m %d autgens %d canonical %ld w-branches %ld full-tests %ld solutions %ld secs %.1f\n",
            m, ngen, ncanon, nw, nfull, nsol, (double)(clock() - t0) / CLOCKS_PER_SEC);
    return 0;
}
