/* ctrl: cubic bipartite controllers for route-chart lifts at D = 5 (hunt-d5).
   Wanted: m + m vertices, 3-regular, simple; every two vertices on the same side within distance 4; every vertex on a
   4-cycle (needed when the fibre is F_3^4 or F_q^4 with q >= 3; NO4=0 drops it).
   Usage: ctrl m seconds seed OUT [mode]   mode sq (default): m/2 disjoint squares K_{2,2} plus an A-B perfect matching
          between different squares, annealed by swapping partners; mode gen: any cubic bipartite graph, double-edge
          switches.  Cost = far same-side unordered pairs + W4 * (vertices on no 4-cycle).  Writes OUT ("2m" then
          "u v" lines, A = 0..m-1, B = m..2m-1) at cost 0.  Env W4 (default 2), NO4 (1), T0 (1.5), COOL (2e5 steps). */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>
static int m, n, adj[128][3], W4 = 2, NO4 = 1, FARW = 1, g_far, g_no4;
static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }
typedef struct { uint64_t w[2]; } bs;
static inline void bor(bs *a, const bs *b) { a->w[0] |= b->w[0]; a->w[1] |= b->w[1]; }
static bs nb[128];
static int cost(void) {
    for (int x = 0; x < n; x++) { nb[x].w[0] = nb[x].w[1] = 0; for (int k = 0; k < 3; k++) { int y = adj[x][k]; nb[x].w[y >> 6] |= 1ULL << (y & 63); } }
    int far = 0;
    for (int s = 0; s < n; s++) {
        bs b1 = nb[s], b2 = {{0, 0}}, b3 = {{0, 0}}, b4 = {{0, 0}};
        for (int k = 0; k < 3; k++) bor(&b2, &nb[adj[s][k]]);
        for (int y = 0; y < n; y++) if ((b2.w[y >> 6] >> (y & 63)) & 1) bor(&b3, &nb[y]);
        for (int y = 0; y < n; y++) if ((b3.w[y >> 6] >> (y & 63)) & 1) bor(&b4, &nb[y]);
        (void)b1;
        int lo = s < m ? 0 : m;
        for (int t = lo; t < lo + m; t++) if (!((b4.w[t >> 6] >> (t & 63)) & 1) && t != s) far++;
    }
    int no4 = 0;
    if (NO4) for (int x = 0; x < n; x++) {
        int ok = 0;
        for (int i = 0; i < 3 && !ok; i++) for (int j = i + 1; j < 3 && !ok; j++) {
            bs c = nb[adj[x][i]]; c.w[0] &= nb[adj[x][j]].w[0]; c.w[1] &= nb[adj[x][j]].w[1];
            if (__builtin_popcountll(c.w[0]) + __builtin_popcountll(c.w[1]) >= 2) ok = 1;
        }
        if (!ok) no4++;
    }
    g_far = far / 2; g_no4 = no4;
    return FARW * (far / 2) + W4 * no4;
}
static int has(int x, int y) { for (int k = 0; k < 3; k++) if (adj[x][k] == y) return 1; return 0; }
static void setnb(int x, int old, int nw) { for (int k = 0; k < 3; k++) if (adj[x][k] == old) { adj[x][k] = nw; return; } }
int main(int argc, char **argv) {
    m = atoi(argv[1]); n = 2 * m; double secs = atof(argv[2]); rs ^= strtoull(argv[3], 0, 10) * 0x9E3779B97F4A7C15ULL;
    const char *out = argv[4]; const char *mode = argc > 5 ? argv[5] : "sq";
    if (getenv("W4")) W4 = atoi(getenv("W4")); if (getenv("FARW")) FARW = atoi(getenv("FARW")); if (getenv("NO4")) NO4 = atoi(getenv("NO4"));
    double T0 = getenv("T0") ? atof(getenv("T0")) : 1.5, COOL = getenv("COOL") ? atof(getenv("COOL")) : 2e5;
    for (int i = 0; i < 30; i++) rnd();
    int sq = !strcmp(mode, "sq"); int ext[128];
    if (sq && m % 2) { fprintf(stderr, "sq needs even m\n"); return 2; }
    /* initial graph */
    for (;;) {
        if (sq) {
            int perm[128]; for (int i = 0; i < m; i++) perm[i] = i;
            for (int i = m - 1; i > 0; i--) { int j = rnd() % (i + 1); int t = perm[i]; perm[i] = perm[j]; perm[j] = t; }
            int ok = 1; for (int u = 0; u < m; u++) if (perm[u] / 2 == u / 2) ok = 0;
            if (!ok) continue;
            for (int u = 0; u < m; u++) { int q = u / 2; adj[u][0] = m + 2 * q; adj[u][1] = m + 2 * q + 1; ext[u] = perm[u]; adj[u][2] = m + perm[u]; }
            for (int v = 0; v < m; v++) { int q = v / 2; adj[m + v][0] = 2 * q; adj[m + v][1] = 2 * q + 1; }
            for (int u = 0; u < m; u++) adj[m + ext[u]][2] = u;
        } else {
            int perm[3][128]; int ok = 1;
            for (int c = 0; c < 3; c++) { for (int i = 0; i < m; i++) perm[c][i] = i; for (int i = m - 1; i > 0; i--) { int j = rnd() % (i + 1); int t = perm[c][i]; perm[c][i] = perm[c][j]; perm[c][j] = t; } }
            for (int u = 0; u < m; u++) if (perm[0][u] == perm[1][u] || perm[0][u] == perm[2][u] || perm[1][u] == perm[2][u]) ok = 0;
            if (!ok) continue;
            for (int c = 0; c < 3; c++) for (int u = 0; u < m; u++) { adj[u][c] = m + perm[c][u]; adj[m + perm[c][u]][c] = u; }
        }
        break;
    }
    int cur = cost(), best = cur; int badj[128][3]; memcpy(badj, adj, sizeof adj);
    double t0 = now(); long step = 0;
    while (best > 0 && now() - t0 < secs) {
        step++;
        double T = T0 * exp(-(double)(step % (long)(5 * COOL)) / COOL) + 0.02;
        int sadj[128][3]; memcpy(sadj, adj, sizeof adj);
        if (sq) {
            int u1 = rnd() % m, u2 = rnd() % m; if (u1 == u2) continue;
            int v1 = adj[u1][2], v2 = adj[u2][2];
            if ((v2 - m) / 2 == u1 / 2 || (v1 - m) / 2 == u2 / 2) continue;
            adj[u1][2] = v2; adj[u2][2] = v1; setnb(v1, u1, u2); setnb(v2, u2, u1);
        } else {
            int a1 = rnd() % m, a2 = rnd() % m; if (a1 == a2) continue;
            int k1 = rnd() % 3, k2 = rnd() % 3; int b1 = adj[a1][k1], b2 = adj[a2][k2];
            if (b1 == b2 || has(a1, b2) || has(a2, b1)) continue;
            adj[a1][k1] = b2; adj[a2][k2] = b1; setnb(b1, a1, a2); setnb(b2, a2, a1);
        }
        int c = cost();
        if (c <= cur || rnd01() < exp(-(c - cur) / T)) { cur = c; if (c < best) { best = c; memcpy(badj, adj, sizeof adj); fprintf(stderr, "t=%.1f step=%ld best=%d\n", now() - t0, step, best); } }
        else memcpy(adj, sadj, sizeof adj);
    }
    memcpy(adj, badj, sizeof adj);
    cost(); printf("RESULT ctrl m=%d mode=%s best=%d far=%d no4=%d steps=%ld time=%.1f\n", m, mode, best, g_far, g_no4, step, now() - t0);
    if (out) { FILE *f = fopen(out, "w"); fprintf(f, "%d\n", n); for (int u = 0; u < m; u++) for (int k = 0; k < 3; k++) fprintf(f, "%d %d\n", u, adj[u][k]); fclose(f); }
    return best == 0 ? 0 : 1;
}
