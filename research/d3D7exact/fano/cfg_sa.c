/* cfg_sa: annealing over the "configuration family" suggested by the n = 248 structure theorem (notes §2.6 item 7)
   and by the extremal (3,5) graph on 56 vertices (7 six-cycles + 14 spokes on the Fano plane).
   Family F(N): N 10-cycles C_j (vertex (j, i), i in Z_10, side i mod 2) and b = 5N/3 "lines", each line a set of 3
   cycles; every cycle lies on 5 lines and gives each of its lines one antipodal pair {i, i+5} (a bijection
   lines -> {0..4}). Line l has spokes y_l (adjacent to the even member of its three pairs) and y'_l (adjacent to the
   odd members). n = 10N + 2b = 40N/3; cubic bipartite.
   State: incidence list inc[l][0..2] (cycle ids) and pair index pr[l][0..2]. Moves: (a) swap the pair indices of two
   lines at one cycle; (b) swap two incidences between two lines (cycle j in line l <-> cycle j' in line l', with
   their pair indices), keeping every cycle on 5 lines and lines without repeated cycles.
   Cost: number of ordered same-side pairs at distance > 6 (0 iff diameter <= 7), bit-parallel BFS.
   Usage: cfg_sa N seed seconds [T0 T1]  -> prints best cost; writes best graph to cfg_N<N>_s<seed>.edges if cost 0 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>
#define MAXN 260
static int N, B, n; static int inc[64][3], pr[64][3];
static int adj[MAXN][3];
static uint64_t rng = 88172645463325252ULL;
static uint64_t xr(void) { rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17; return rng; }
static double ur(void) { return (xr() >> 11) * (1.0 / 9007199254740992.0); }
static void build(void) {
    int deg[MAXN] = {0};
    #define ADD(a,b) do { adj[a][deg[a]++] = b; adj[b][deg[b]++] = a; } while (0)
    for (int j = 0; j < N; j++) for (int i = 0; i < 10; i++) { int a = j * 10 + i, b = j * 10 + (i + 1) % 10; if (i % 2 == 0) { ADD(a, b); } else { ADD(a, b); } }
    for (int l = 0; l < B; l++) { int y = 10 * N + 2 * l, y2 = y + 1;
        for (int t = 0; t < 3; t++) { int j = inc[l][t], r = pr[l][t]; int e = (r % 2 == 0) ? r : r + 5, o = (r % 2 == 0) ? r + 5 : r;
            ADD(y, j * 10 + e); ADD(y2, j * 10 + o); } }
}
static long cost(void) {
    /* sides: cycle vertex (j,i): i%2; y (even index 10N+2l) adjacent to even vertices -> side 1; y' -> side 0 */
    static uint64_t R[MAXN][4], R2[MAXN][4]; int W = (n + 63) / 64;
    long bad = 0;
    for (int s0 = 0; s0 < n; s0 += 256) {
        memset(R, 0, sizeof R);
        for (int v = s0; v < n && v < s0 + 256; v++) R[v][(v - s0) >> 6] |= 1ULL << ((v - s0) & 63);
        for (int step = 0; step < 6; step++) {
            for (int v = 0; v < n; v++) for (int w = 0; w < 4; w++) R2[v][w] = R[v][w] | R[adj[v][0]][w] | R[adj[v][1]][w] | R[adj[v][2]][w];
            memcpy(R, R2, sizeof R);
        }
        /* count same-side pairs (source s, target v) not reached */
        for (int v = 0; v < n; v++) for (int s = s0; s < n && s < s0 + 256; s++) {
            int sv = (v < 10 * N) ? (v % 10) % 2 : ((v - 10 * N) % 2 == 0 ? 1 : 0);
            int ss = (s < 10 * N) ? (s % 10) % 2 : ((s - 10 * N) % 2 == 0 ? 1 : 0);
            if (sv == ss && !(R[v][(s - s0) >> 6] >> ((s - s0) & 63) & 1)) bad++; }
    }
    (void)W; return bad;
}
static int valid_lines(void) { for (int l = 0; l < B; l++) if (inc[l][0] == inc[l][1] || inc[l][0] == inc[l][2] || inc[l][1] == inc[l][2]) return 0; return 1; }
int main(int argc, char **argv) {
    N = atoi(argv[1]); rng ^= (uint64_t)atol(argv[2]) * 2654435761ULL; double secs = atof(argv[3]);
    double T0 = argc > 4 ? atof(argv[4]) : 30, T1 = argc > 5 ? atof(argv[5]) : 0.5;
    if ((5 * N) % 3) { fprintf(stderr, "N must be divisible by 3\n"); return 2; }
    B = 5 * N / 3; n = 10 * N + 2 * B;
    /* random initial incidence: list of 5N slots (each cycle 5 times), shuffle until lines have distinct cycles */
    int slots[320]; do { for (int j = 0; j < N; j++) for (int t = 0; t < 5; t++) slots[j * 5 + t] = j;
        for (int i = 5 * N - 1; i > 0; i--) { int r = xr() % (i + 1), tmp = slots[i]; slots[i] = slots[r]; slots[r] = tmp; }
        for (int l = 0; l < B; l++) for (int t = 0; t < 3; t++) inc[l][t] = slots[3 * l + t]; } while (!valid_lines());
    /* pair indices: per cycle a random bijection */
    for (int j = 0; j < N; j++) { int perm[5] = {0, 1, 2, 3, 4}; for (int i = 4; i > 0; i--) { int r = xr() % (i + 1), tmp = perm[i]; perm[i] = perm[r]; perm[r] = tmp; }
        int c = 0; for (int l = 0; l < B; l++) for (int t = 0; t < 3; t++) if (inc[l][t] == j) pr[l][t] = perm[c++]; }
    build(); long cur = cost(), best = cur; clock_t st = clock(); long it = 0;
    int binc[64][3], bpr[64][3]; memcpy(binc, inc, sizeof inc); memcpy(bpr, pr, sizeof pr);
    while (best > 0) {
        double el = (double)(clock() - st) / CLOCKS_PER_SEC; if (el > secs) break;
        double T = T0 * pow(T1 / T0, el / secs);
        int sinc[64][3], spr[64][3]; memcpy(sinc, inc, sizeof inc); memcpy(spr, pr, sizeof pr);
        if (xr() % 2) { /* swap pair indices of two incidences of the same cycle */
            int j = xr() % N, a[5][2], c = 0; for (int l = 0; l < B; l++) for (int t = 0; t < 3; t++) if (inc[l][t] == j) { a[c][0] = l; a[c][1] = t; c++; }
            int u = xr() % 5, v = xr() % 5; if (u == v) continue;
            int tmp = pr[a[u][0]][a[u][1]]; pr[a[u][0]][a[u][1]] = pr[a[v][0]][a[v][1]]; pr[a[v][0]][a[v][1]] = tmp;
        } else { /* swap incidences between two lines */
            int l1 = xr() % B, l2 = xr() % B, t1 = xr() % 3, t2 = xr() % 3; if (l1 == l2) continue;
            int tmp = inc[l1][t1]; inc[l1][t1] = inc[l2][t2]; inc[l2][t2] = tmp; tmp = pr[l1][t1]; pr[l1][t1] = pr[l2][t2]; pr[l2][t2] = tmp;
            if (!valid_lines()) { memcpy(inc, sinc, sizeof inc); memcpy(pr, spr, sizeof pr); continue; }
        }
        build(); long c2 = cost(); it++;
        if (c2 <= cur || ur() < exp((cur - c2) / T)) { cur = c2; if (cur < best) { best = cur; memcpy(binc, inc, sizeof inc); memcpy(bpr, pr, sizeof pr); } }
        else { memcpy(inc, sinc, sizeof inc); memcpy(pr, spr, sizeof pr); }
    }
    memcpy(inc, binc, sizeof inc); memcpy(pr, bpr, sizeof pr); build();
    printf("N=%d n=%d best=%ld iters=%ld\n", N, n, best, it);
    char fn[64]; sprintf(fn, "cfg_N%d_s%s.edges", N, argv[2]);
    FILE *f = fopen(fn, "w"); fprintf(f, "%d\n", n); for (int v = 0; v < n; v++) for (int t = 0; t < 3; t++) if (adj[v][t] > v) fprintf(f, "%d %d\n", v, adj[v][t]); fclose(f);
    return 0;
}
