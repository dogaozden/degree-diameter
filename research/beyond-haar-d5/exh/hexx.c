/* hexx.c: exact search over all lifts, by a group G (|G| <= 128), of a "hexagon of dipoles" base for D = 5:
 * base vertices v0..v5 around a 6-cycle (v_even on side A, v_odd on side B), dipole i = m_i parallel edges between
 * v_i and v_{i+1}, with m_i = a (i even) or DELTA - a (i odd), so every vertex has degree DELTA.
 * P_i = forward voltages of dipole i (traversal v_i -> v_{i+1}); the backward traversal uses inverses.
 * Normalisation (switching at v1..v5 in turn): P_0..P_4 contain the identity; P_5 is any m_5-subset (holonomy).
 * Automorphisms of G (file) reduce P_0 to orbit representatives.
 * Pruning: the closed walks of length <= 4 at v_j are
 *   local loops in dipoles j-1, j  |  P_j D_{j+1} P_j^-1 (D_{j+1} = {r r'^-1, r != r' in P_{j+1}})
 *   |  P_{j-1}^-1 D'_{j-2} P_{j-1} (D'_{j-2} = {s^-1 s', s != s' in P_{j-2}}),
 * and must cover G (own fibre). With some dipoles still unknown, the known classes must miss at most as many
 * elements as the unknown classes have walks. Full test (all pairs, exact) for every complete survivor.
 * usage: hexx GROUP AUTFILE a [DELTA=5]     prints SOL lines (vl base+voltage format on one line)
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

typedef unsigned __int128 u128;
static int n, DELTA = 5, A;
static int mul[128][128], inv_[128];
static u128 ALL;
static int mi[6], P[6][8];
static int naut, (*aut)[128];
static inline u128 bit(int x) { return ((u128)1) << x; }
static inline int pc(u128 x) { return __builtin_popcountll((uint64_t)x) + __builtin_popcountll((uint64_t)(x >> 64)); }

/* --- coverage classes for vertex j --- */
static u128 local_loops(int j) {          /* needs P_{j-1}, P_j */
    int jm = (j + 5) % 6; u128 c = bit(0);
    /* edges at v_j: forward (dipole j, out p, back p^-1), backward (dipole j-1, out q^-1, back q) */
    int ne = mi[j] + mi[jm], outv[16], backv[16], grp[16];
    for (int k = 0; k < mi[j]; k++) { outv[k] = P[j][k]; backv[k] = inv_[P[j][k]]; grp[k] = 0; }
    for (int k = 0; k < mi[jm]; k++) { outv[mi[j] + k] = inv_[P[jm][k]]; backv[mi[j] + k] = P[jm][k]; grp[mi[j] + k] = 1; }
    for (int o1 = 0; o1 < ne; o1++) for (int r1 = 0; r1 < ne; r1++) {
        if (r1 == o1 || grp[r1] != grp[o1]) continue;
        int h1 = mul[outv[o1]][backv[r1]]; c |= bit(h1);
        for (int o2 = 0; o2 < ne; o2++) { if (o2 == r1) continue;
            for (int r2 = 0; r2 < ne; r2++) { if (r2 == o2 || grp[r2] != grp[o2]) continue;
                c |= bit(mul[h1][mul[outv[o2]][backv[r2]]]); } }
    }
    return c;
}
static u128 fwd_exc(int j) {             /* needs P_j, P_{j+1} */
    int j1 = (j + 1) % 6; u128 c = 0;
    for (int b = 0; b < mi[j1]; b++) for (int b2 = 0; b2 < mi[j1]; b2++) if (b != b2) {
        int d = mul[P[j1][b]][inv_[P[j1][b2]]];
        for (int p = 0; p < mi[j]; p++) for (int p2 = 0; p2 < mi[j]; p2++) c |= bit(mul[mul[P[j][p]][d]][inv_[P[j][p2]]]); }
    return c;
}
static u128 bwd_exc(int j) {             /* needs P_{j-1}, P_{j-2} */
    int j1 = (j + 5) % 6, j2 = (j + 4) % 6; u128 c = 0;
    for (int s = 0; s < mi[j2]; s++) for (int s2 = 0; s2 < mi[j2]; s2++) if (s != s2) {
        int d = mul[inv_[P[j2][s]]][P[j2][s2]];
        for (int q = 0; q < mi[j1]; q++) for (int q2 = 0; q2 < mi[j1]; q2++) c |= bit(mul[mul[inv_[P[j1][q]]][d]][P[j1][q2]]); }
    return c;
}
static int nfwd(int j) { int j1 = (j + 1) % 6; return mi[j] * mi[j] * mi[j1] * (mi[j1] - 1); }
static int nbwd(int j) { int j1 = (j + 5) % 6, j2 = (j + 4) % 6; return mi[j1] * mi[j1] * mi[j2] * (mi[j2] - 1); }

static int known[6];
/* 0 if vertex j's own fibre cannot be covered given the known dipoles */
static int self_ok(int j) {
    int jm = (j + 5) % 6, jp = (j + 1) % 6, jmm = (j + 4) % 6;
    u128 c = 0; int unk = 0;
    if (known[jm] && known[j]) c |= local_loops(j); else return 1;   /* local loops are most walks: need them */
    if (known[jp]) c |= fwd_exc(j); else unk += nfwd(j);
    if (known[jmm]) c |= bwd_exc(j); else unk += nbwd(j);
    return pc(ALL & ~c) <= unk;
}

/* --- full test --- */
static int side_[6] = {0, 1, 0, 1, 0, 1};
static int deg[6], an[6][16], ae[6][16], ag[6][16];
static u128 cov[6]; static int Lmax;
static void dfs(int v, int laste, int h, int len) {
    cov[v] |= bit(h); if (len == Lmax) return;
    for (int i = 0; i < deg[v]; i++) { if (ae[v][i] == laste) continue; dfs(an[v][i], ae[v][i], mul[h][ag[v][i]], len + 1); }
}
static int full_ok(void) {
    memset(deg, 0, sizeof deg); int e = 0;
    for (int i = 0; i < 6; i++) { int u = i, w = (i + 1) % 6;
        for (int k = 0; k < mi[i]; k++, e++) { int p = P[i][k];
            an[u][deg[u]] = w; ae[u][deg[u]] = e; ag[u][deg[u]] = p; deg[u]++;
            an[w][deg[w]] = u; ae[w][deg[w]] = e; ag[w][deg[w]] = inv_[p]; deg[w]++; } }
    for (int s = 0; s < 6; s++) {
        memset(cov, 0, sizeof cov); Lmax = side_[s] == 0 ? 5 : 4; dfs(s, -1, 0, 0);
        for (int v = 0; v < 6; v++) { if (side_[s] == 1 && side_[v] == 0) continue; if (cov[v] != ALL) return 0; }
    }
    return 1;
}
static long long nsol = 0, nfull = 0, nodes[7];
static void print_sol(void) {
    /* vl format: base vertex ids A0=0 A1=1 A2=2 B0=3 B1=4 B2=5; hexagon v0=A0 v1=B1 v2=A1 v3=B0 v4=A2 v5=B2 */
    static const int id[6] = {0, 4, 1, 3, 2, 5};
    printf("SOL 6 %d | 0 0 0 1 1 1 |", 3 * DELTA);
    for (int i = 0; i < 6; i++) for (int k = 0; k < mi[i]; k++) {
        int u = id[i], w = id[(i + 1) % 6], p = P[i][k];
        if (side_[i] == 0) printf(" %d %d %d ,", u, w, p); else printf(" %d %d %d ,", w, u, inv_[p]);
    }
    printf("\n"); fflush(stdout);
}

/* choose P_i: sorted subset; for i < 5 it contains the identity (element 0) */
static int canon_i = 0;
static int canon_a(int a) { for (int t = 1; t < naut; t++) if (aut[t][a] < a) return 0; return 1; }
static void level(int i);
static void choose(int i, int k, int start) {
    if (k == mi[i]) {
        known[i] = 1; nodes[i]++;
        int ok = 1;
        for (int j = 0; j < 6 && ok; j++) ok = self_ok(j);
        if (ok) level(i + 1);
        known[i] = 0; return;
    }
    for (int x = start; x < n; x++) {
        if (i == canon_i && k == 1 && !canon_a(x)) continue;
        P[i][k] = x; choose(i, k + 1, x + 1);
    }
}
static void level(int i) {
    if (i == 6) { nfull++; if (full_ok()) { nsol++; print_sol(); } return; }
    if (i < 5) { P[i][0] = 0; choose(i, 1, 1); } else choose(i, 0, 0);
}

int main(int argc, char **argv) {
    if (argc < 4) return 2;
    FILE *f = fopen(argv[1], "r"); if (!f || fscanf(f, "%d", &n) != 1 || n > 128) return 2;
    for (int i = 0; i < n; i++) for (int j = 0; j < n; j++) if (fscanf(f, "%d", &mul[i][j]) != 1) return 2;
    fclose(f);
    for (int i = 0; i < n; i++) for (int j = 0; j < n; j++) if (mul[i][j] == 0) inv_[i] = j;
    ALL = (n == 128) ? ~(u128)0 : bit(n) - 1;
    f = fopen(argv[2], "r"); if (!f || fscanf(f, "%d", &naut) != 1) return 2;
    aut = malloc(sizeof(int[128]) * naut);
    for (int a = 0; a < naut; a++) for (int x = 0; x < n; x++) if (fscanf(f, "%d", &aut[a][x]) != 1) return 2;
    fclose(f);
    A = atoi(argv[3]); if (argc > 4) DELTA = atoi(argv[4]);
    for (int i = 0; i < 6; i++) mi[i] = (i % 2 == 0) ? A : DELTA - A;
    for (canon_i = 0; canon_i < 5 && mi[canon_i] < 2; canon_i++) {}
    clock_t t0 = clock();
    level(0);
    fprintf(stderr, "n %d a %d nodes", n, A); for (int i = 0; i < 6; i++) fprintf(stderr, " %lld", nodes[i]);
    fprintf(stderr, " full %lld solutions %lld secs %.1f\n", nfull, nsol, (double)(clock() - t0) / CLOCKS_PER_SEC);
    return 0;
}
