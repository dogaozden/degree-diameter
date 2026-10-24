/* Grow a bipartite 4-regular controller by one vertex per side and repair it by annealing double-edge swaps.
   Objective = (# ordered same-side pairs at distance > 4) + W * (# vertices on no 4-cycle).
   Input: edge list "n" then "u v" lines with side A = 0..n/2-1. usage: grow45 EDGES seed maxgrow steps T0 W out_prefix
   Writes out_prefix_N.edges (N per side) whenever a valid controller (objective 0) with N per side is reached. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <stdint.h>
#define MAXV 256
static int n, half, adj[MAXV][4];
static uint64_t nb[MAXV][4], r2[MAXV][4];
static unsigned long long rs = 88172645463325252ULL;
static unsigned long long rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static double urand(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }
static int W;
static int objective(void) {
    for (int u = 0; u < n; u++) { memset(nb[u], 0, sizeof nb[u]); for (int i = 0; i < 4; i++) nb[u][adj[u][i] >> 6] |= 1ULL << (adj[u][i] & 63); }
    for (int u = 0; u < n; u++) { memset(r2[u], 0, sizeof r2[u]); r2[u][u >> 6] |= 1ULL << (u & 63);
        for (int i = 0; i < 4; i++) { int w = adj[u][i]; for (int j = 0; j < 4; j++) r2[u][j] |= nb[w][j]; } }
    int miss = 0, no4 = 0;
    for (int u = 0; u < n; u++) {
        uint64_t r4[4] = {0, 0, 0, 0};
        for (int j = 0; j < 4; j++) { uint64_t x = r2[u][j]; while (x) { int b = __builtin_ctzll(x); x &= x - 1; int v = j * 64 + b; for (int t = 0; t < 4; t++) r4[t] |= r2[v][t]; } }
        int lo = u < half ? 0 : half, cnt = 0;
        for (int v = lo; v < lo + half; v++) if (r4[v >> 6] >> (v & 63) & 1) cnt++;
        miss += half - cnt;
        /* 4-cycle: some v != u with two common neighbours */
        static int c[MAXV]; int found = 0;
        for (int i = 0; i < 4; i++) { int w = adj[u][i]; for (int j = 0; j < 4; j++) c[adj[w][j]] = 0; }
        for (int i = 0; i < 4 && !found; i++) { int w = adj[u][i]; for (int j = 0; j < 4; j++) { int v = adj[w][j]; if (v != u && ++c[v] >= 2) { found = 1; break; } } }
        if (!found) no4++;
    }
    return miss + W * no4; }
static int hasedge(int a, int b) { for (int i = 0; i < 4; i++) if (adj[a][i] == b) return 1; return 0; }
static void repl(int a, int old, int nw) { for (int i = 0; i < 4; i++) if (adj[a][i] == old) { adj[a][i] = nw; return; } }
static void save(const char *pre) {
    char fn[512]; sprintf(fn, "%s_%d.edges", pre, half); FILE *f = fopen(fn, "w"); fprintf(f, "%d\n", n);
    for (int u = 0; u < half; u++) for (int i = 0; i < 4; i++) fprintf(f, "%d %d\n", u, adj[u][i]); fclose(f); }
int main(int argc, char **argv) {
    FILE *f = fopen(argv[1], "r"); int n0; if (fscanf(f, "%d", &n0) != 1) return 1; int deg[MAXV] = {0}, a, b;
    half = n0 / 2;
    /* relabel: A side 0..half-1 stays, B side shifted later; keep ids, grow inserts new A id at half (shift B) */
    static int tmpadj[MAXV][4]; while (fscanf(f, "%d %d", &a, &b) == 2) { tmpadj[a][deg[a]++] = b; tmpadj[b][deg[b]++] = a; }
    n = n0; memcpy(adj, tmpadj, sizeof adj);
    rs ^= (unsigned long long)atoll(argv[2]) * 0x9E3779B97F4A7C15ULL; int maxgrow = atoi(argv[3]); long steps = atol(argv[4]); double T0 = atof(argv[5]); W = atoi(argv[6]);
    printf("start: %d per side, objective %d\n", half, (W = atoi(argv[6]), objective())); fflush(stdout);
    for (int g = 0; g < maxgrow; g++) {
        /* insert: new A vertex at index half (B ids shift by 1), new B vertex at the end */
        int nn = n + 2; static int na[MAXV][4];
        for (int u = 0; u < n; u++) { int uu = u < half ? u : u + 1; for (int i = 0; i < 4; i++) { int v = adj[u][i]; na[uu][i] = v < half ? v : v + 1; } }
        int A0 = half, B0 = nn - 1; half++; n = nn; memcpy(adj, na, sizeof adj);
        /* pick 3 edges (x_i, y_i) with distinct endpoints, x in A (old), y in B (old) */
        int xs[3], ys[3];
        for (int i = 0; i < 3; i++) { while (1) { int x = rnd() % (half - 1); int y = adj[x][rnd() % 4]; int ok = 1; for (int j = 0; j < i; j++) if (xs[j] == x || ys[j] == y) ok = 0; if (ok) { xs[i] = x; ys[i] = y; break; } } }
        for (int i = 0; i < 3; i++) { repl(xs[i], ys[i], B0); repl(ys[i], xs[i], A0); adj[A0][i] = ys[i]; adj[B0][i] = xs[i]; }
        adj[A0][3] = B0; adj[B0][3] = A0;
        int c = objective(), best = c;
        for (long it = 0; it < steps && c > 0; it++) {
            double temp = T0 * (1.0 - (double)it / steps);
            int a1 = rnd() % half, a2 = rnd() % half; if (a1 == a2) continue;
            int i1 = rnd() % 4, i2 = rnd() % 4, b1 = adj[a1][i1], b2 = adj[a2][i2];
            if (b1 == b2 || hasedge(a1, b2) || hasedge(a2, b1)) continue;
            adj[a1][i1] = b2; adj[a2][i2] = b1; repl(b1, a1, a2); repl(b2, a2, a1);
            int c2 = objective();
            if (c2 <= c || (temp > 0 && urand() < exp((c - c2) / temp))) { c = c2; if (c < best) best = c; }
            else { adj[a1][i1] = b1; adj[a2][i2] = b2; repl(b1, a2, a1); repl(b2, a1, a2); }
        }
        printf("grown to %d per side: objective %d (best %d)\n", half, c, best); fflush(stdout);
        if (c > 0) break;
        save(argv[7]);
    }
    return 0; }
