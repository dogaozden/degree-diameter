/* scafopt: exact-cost local search over slab-scaffold designs (director, job beyond-small).
 * Reads G and the two design dumps of slabD (side 0: A-structure, side 1: B-structure). State: for each side and each
 * line l of PG(2,3), a "good triple" of covering quadruples (12 fibres with a line direction each). Hyperplanes at a
 * fibre are handed out to the lines using it in line order; copy j of line l takes slab j of each of its hyperplanes;
 * the 4 lines of a slab go to the 4 hubs of a quadruple in a Latin pattern. Connector index c = j*13 + l, connector c
 * of side 0 is matched to connector match[c] of side 1. Cost = exact number of (new vertex, vertex) pairs farther than
 * 5 (same side: 4), BFS from all new vertices. Moves: replace one line's triple (fibre capacity <= 4), permute matching.
 * usage: scafopt EDGES DUMP0 DUMP1 SEED SECS OUT_EDGES OUT_STATE */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>
#define MAXN 36000
#define DEG 17
#define NPT 13
#define K 4
#define NCON 52
#define HPC 12
static int n0, n, adj[MAXN][DEG], dg[MAXN], base_adj[MAXN][DEG], base_dg[MAXN];
static int lines[NPT][K];
static int nq[2], (*Q[2])[4], ngt[2], (*GT[2])[3];
static int (*L4[2])[4][4][5][4][4];
static int Phi[2][NPT][3], match_[NCON];
static unsigned long long rs = 88172645463325252ULL;
static inline unsigned rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return (unsigned)(rs >> 11); }
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }
static void make_plane(void) {
    int q = 3, P[NPT][3], np = 0;
    for (int x = 0; x < q; x++) for (int y = 0; y < q; y++) { P[np][0] = 1; P[np][1] = x; P[np][2] = y; np++; }
    for (int y = 0; y < q; y++) { P[np][0] = 0; P[np][1] = 1; P[np][2] = y; np++; }
    P[np][0] = 0; P[np][1] = 0; P[np][2] = 1; np++;
    for (int l = 0; l < NPT; l++) { int c = 0; for (int p = 0; p < NPT; p++) { int s = 0; for (int k = 0; k < 3; k++) s += P[l][k] * P[p][k]; if (s % q == 0) lines[l][c++] = p; } }
}
static int hubv(int s, int c, int j) { return n0 + s * (NCON * HPC) + c * HPC + j; }
static int connv(int s, int c) { return n0 + 2 * NCON * HPC + s * NCON + c; }
static int rootv(int s, int r) { return n0 + 2 * NCON * HPC + 2 * NCON + s * NPT + r; }
static void add_edge(int u, int v) { adj[u][dg[u]++] = v; adj[v][dg[v]++] = u; }
static int capok(int s) {
    int cap[66] = {0};
    for (int l = 0; l < NPT; l++) for (int qq = 0; qq < 3; qq++) for (int i = 0; i < 4; i++) if (++cap[Q[s][GT[s][Phi[s][l][qq]][qq] >= 0 ? 0 : 0][0] * 0 + Q[s][Phi[s][l][qq]][i] / 5] > 4) return 0;
    return 1;
}
static int build(void) {
    memcpy(dg, base_dg, sizeof(int) * n0); memcpy(adj, base_adj, sizeof(int) * DEG * n0);
    for (int v = n0; v < n; v++) dg[v] = 0;
    for (int s = 0; s < 2; s++) {
        int hc[66] = {0};
        for (int l = 0; l < NPT; l++) {
            int hyp[12];
            for (int qq = 0; qq < 3; qq++) for (int i = 0; i < 4; i++) { int f = Q[s][Phi[s][l][qq]][i] / 5; if (hc[f] >= 4) return 0; hyp[qq * 4 + i] = hc[f]++; }
            for (int j = 0; j < 4; j++) { int c = j * NPT + l;
                for (int qq = 0; qq < 3; qq++) for (int hb = 0; hb < 4; hb++) { int h = hubv(s, c, qq * 4 + hb);
                    for (int i = 0; i < 4; i++) { int e = Q[s][Phi[s][l][qq]][i], f = e / 5, d = e % 5;
                        for (int m = 0; m < 4; m++) { int x = L4[s][f][hyp[qq * 4 + i]][j][d][(hb + i) % 4][m]; if (dg[x] >= DEG) return 0; add_edge(h, x); } }
                    add_edge(h, connv(s, c)); }
                for (int k = 0; k < K; k++) add_edge(connv(s, c), rootv(s, lines[l][k])); }
        }
    }
    for (int c = 0; c < NCON; c++) add_edge(connv(0, c), connv(1, match_[c]));
    return 1;
}
static uint64_t vis[MAXN], fr[MAXN], nx[MAXN];
static long cost(long cap) {
    long far = 0; int ns_tot = n - n0;
    for (int k0 = 0; k0 < ns_tot; k0 += 64) {
        int ns = ns_tot - k0 < 64 ? ns_tot - k0 : 64;
        memset(vis, 0, n * 8); memset(fr, 0, n * 8);
        for (int k = 0; k < ns; k++) { vis[n0 + k0 + k] |= 1ULL << k; fr[n0 + k0 + k] |= 1ULL << k; }
        for (int lev = 0; lev < 5; lev++) {
            for (int x = 0; x < n; x++) { uint64_t a = 0; for (int i = 0; i < dg[x]; i++) a |= fr[adj[x][i]]; nx[x] = a & ~vis[x]; }
            for (int x = 0; x < n; x++) { vis[x] |= nx[x]; fr[x] = nx[x]; }
        }
        uint64_t full = ns == 64 ? ~0ULL : ((1ULL << ns) - 1);
        for (int x = 0; x < n; x++) far += __builtin_popcountll(full & ~vis[x]);
        if (far >= cap) return far;
    }
    return far;
}
static void load(int s, const char *fn) {
    FILE *f = fopen(fn, "rb"); if (!f) { perror(fn); exit(1); }
    if (fread(&nq[s], 4, 1, f) != 1) exit(1); Q[s] = malloc(sizeof(int[4]) * nq[s]); if (fread(Q[s], sizeof(int[4]), nq[s], f) != (size_t)nq[s]) exit(1);
    if (fread(&ngt[s], 4, 1, f) != 1) exit(1); GT[s] = malloc(sizeof(int[3]) * ngt[s]); if (fread(GT[s], sizeof(int[3]), ngt[s], f) != (size_t)ngt[s]) exit(1);
    L4[s] = malloc(sizeof(int[4][4][5][4][4]) * 66); if (fread(L4[s], sizeof(int[4][4][5][4][4]), 66, f) != 66) exit(1);
    if (fread(Phi[s], sizeof(int[3]), NPT, f) != NPT) exit(1);
    fclose(f);
}
int main(int argc, char **argv) {
    if (argc < 8) { fprintf(stderr, "usage: scafopt EDGES DUMP0 DUMP1 SEED SECS OUT_EDGES OUT_STATE\n"); return 2; }
    rs ^= (unsigned long long)atoll(argv[4]) * 0x9E3779B97F4A7C15ULL; double secs = atof(argv[5]);
    make_plane();
    FILE *f = fopen(argv[1], "r"); long u, v; if (fscanf(f, "%d", &n0) != 1) return 3;
    while (fscanf(f, "%ld %ld", &u, &v) == 2) { base_adj[u][base_dg[u]++] = v; base_adj[v][base_dg[v]++] = u; }
    fclose(f);
    load(0, argv[2]); load(1, argv[3]);
    n = n0 + 2 * NCON * HPC + 2 * NCON + 2 * NPT;
    for (int c = 0; c < NCON; c++) match_[c] = c;
    if (!build()) { fprintf(stderr, "start design invalid\n"); return 4; }
    long cur = cost(1L << 60), best = cur; double t0 = now();
    printf("n = %d, start cost %ld\n", n, cur); fflush(stdout);
    int bPhi[2][NPT][3], bmatch[NCON]; memcpy(bPhi, Phi, sizeof Phi); memcpy(bmatch, match_, sizeof match_);
    long it = 0;
    while (now() - t0 < secs && best > 0) {
        it++;
        int s = rnd() & 1, mv = (rnd() % 4 == 0) ? 1 : 0, l = rnd() % NPT, old[3], a = 0, b = 0;
        if (mv == 0) { memcpy(old, Phi[s][l], sizeof old); int g = rnd() % ngt[s]; memcpy(Phi[s][l], GT[s][g], sizeof old); }
        else { a = rnd() % NCON; b = rnd() % NCON; int t = match_[a]; match_[a] = match_[b]; match_[b] = t; }
        long c = (1L << 60);
        if (build()) c = cost(cur + 1 + (rnd() % 4 == 0 ? (cur / 50 + 1) : 0));
        if (c <= cur) { cur = c; if (c < best) { best = c; memcpy(bPhi, Phi, sizeof Phi); memcpy(bmatch, match_, sizeof match_); printf("it %ld cost %ld (%.0fs)\n", it, best, now() - t0); fflush(stdout); } }
        else { if (mv == 0) memcpy(Phi[s][l], old, sizeof old); else { int t = match_[a]; match_[a] = match_[b]; match_[b] = t; } }
    }
    memcpy(Phi, bPhi, sizeof Phi); memcpy(match_, bmatch, sizeof match_); build();
    printf("FINAL cost %ld after %ld iterations, n = %d\n", cost(1L << 60), it, n);
    FILE *g = fopen(argv[6], "w"); fprintf(g, "%d\n", n);
    for (int x = 0; x < n; x++) for (int i = 0; i < dg[x]; i++) if (adj[x][i] > x) fprintf(g, "%d %d\n", x, adj[x][i]);
    fclose(g);
    g = fopen(argv[7], "wb"); fwrite(Phi, sizeof Phi, 1, g); fwrite(match_, sizeof match_, 1, g); fclose(g);
    (void)capok;
    return 0;
}
