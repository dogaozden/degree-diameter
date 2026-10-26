/* shrink: top-down repair of a near-miss. Repeatedly contracts an edge x-y of a cubic bipartite graph (x white with
   other neighbours b1 b2, y black with other neighbours a1 a2: delete x, y and add a1-b1, a2-b2 or a1-b2, a2-b1),
   choosing at random among the K contractions with the lowest cost, until n = target. Writes the result in sa3's
   format (whites 0..m-1, blacks m..n-1, "white black" edges) for annealing with sa3.
   Usage: shrink IN.edges target seed K OUT.edges        cost = ordered pairs at distance > 7 (env D) */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#define MAXN 512
#define W 8
static int n, D = 7, nb[MAXN][3], col[MAXN];
static uint64_t ra[MAXN][W], rb[MAXN][W];
static uint64_t rng = 88172645463325252ULL;
static uint64_t xr(void) { rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17; return rng; }

static long costg(int nn, int (*g)[3]) {
    int nw = (nn + 63) / 64; uint64_t (*cur)[W] = ra, (*nx)[W] = rb;
    for (int x = 0; x < nn; x++) { memset(cur[x], 0, sizeof cur[x]); cur[x][x >> 6] |= 1ULL << (x & 63); }
    for (int t = 0; t < D; t++) {
        for (int x = 0; x < nn; x++) for (int w = 0; w < nw; w++) nx[x][w] = cur[x][w] | cur[g[x][0]][w] | cur[g[x][1]][w] | cur[g[x][2]][w];
        uint64_t (*tmp)[W] = cur; cur = nx; nx = tmp;
    }
    long r = 0; for (int x = 0; x < nn; x++) for (int w = 0; w < nw; w++) r += __builtin_popcountll(cur[x][w]);
    return (long)nn * nn - r;
}
static int g2[MAXN][3], c2[MAXN];
/* contraction of edge x-y (col[x]=0), variant v; returns new n or -1 if not simple */
static int contract(int x, int y, int v) {
    int b[2], a[2], nbn = 0, nan = 0;
    for (int j = 0; j < 3; j++) { if (nb[x][j] != y) b[nbn++] = nb[x][j]; if (nb[y][j] != x) a[nan++] = nb[y][j]; }
    if (nbn != 2 || nan != 2) return -1;
    if (v) { int t = b[0]; b[0] = b[1]; b[1] = t; }
    for (int i = 0; i < 2; i++) for (int j = 0; j < 3; j++) if (nb[a[i]][j] == b[i]) return -1;
    int map[MAXN], k = 0;
    for (int z = 0; z < n; z++) map[z] = (z == x || z == y) ? -1 : k++;
    for (int z = 0; z < n; z++) { if (map[z] < 0) continue; c2[map[z]] = col[z];
        for (int j = 0; j < 3; j++) { int w = nb[z][j];
            if (w == x) w = (z == b[0]) ? a[0] : a[1];        /* b_i loses x, gains a_i */
            else if (w == y) w = (z == a[0]) ? b[0] : b[1];   /* a_i loses y, gains b_i */
            g2[map[z]][j] = map[w]; } }
    return n - 2;
}
int main(int argc, char **argv) {
    if (argc < 6) { fprintf(stderr, "usage: shrink IN target seed K OUT\n"); return 2; }
    if (getenv("D")) D = atoi(getenv("D"));
    FILE *f = fopen(argv[1], "r"); if (fscanf(f, "%d", &n) != 1) return 2;
    int dg[MAXN] = {0}, a, b; while (fscanf(f, "%d %d", &a, &b) == 2) { nb[a][dg[a]++] = b; nb[b][dg[b]++] = a; } fclose(f);
    int target = atoi(argv[2]); rng ^= (uint64_t)atoll(argv[3]) * 0x9E3779B97F4A7C15ULL; int K = atoi(argv[4]);
    /* colour */
    for (int i = 0; i < n; i++) col[i] = -1; col[0] = 0; int q[MAXN], h = 0, t = 0; q[t++] = 0;
    while (h < t) { int z = q[h++]; for (int j = 0; j < 3; j++) if (col[nb[z][j]] < 0) { col[nb[z][j]] = 1 - col[z]; q[t++] = nb[z][j]; } }
    printf("n=%d cost=%ld\n", n, costg(n, nb));
    while (n > target) {
        long bc[4096]; int bx[4096], by[4096], bv[4096], nc = 0;
        for (int x = 0; x < n; x++) if (col[x] == 0) for (int j = 0; j < 3; j++) for (int v = 0; v < 2; v++) {
            int y = nb[x][j]; if (contract(x, y, v) < 0) continue;
            bc[nc] = costg(n - 2, g2); bx[nc] = x; by[nc] = y; bv[nc] = v; nc++; }
        /* pick uniformly among the K best */
        for (int i = 0; i < nc && i < K; i++) { int m = i; for (int j = i + 1; j < nc; j++) if (bc[j] < bc[m]) m = j;
            long tc = bc[i]; bc[i] = bc[m]; bc[m] = tc; int ti = bx[i]; bx[i] = bx[m]; bx[m] = ti; ti = by[i]; by[i] = by[m]; by[m] = ti; ti = bv[i]; bv[i] = bv[m]; bv[m] = ti; }
        int pick = xr() % (K < nc ? K : nc);
        contract(bx[pick], by[pick], bv[pick]); n -= 2;
        memcpy(nb, g2, sizeof(int) * 3 * n); memcpy(col, c2, sizeof(int) * n);
        printf("n=%d cost=%ld (best option %ld)\n", n, bc[pick], bc[0]); fflush(stdout);
    }
    /* write in sa3 format */
    int lab[MAXN], m = 0; for (int z = 0; z < n; z++) if (col[z] == 0) lab[z] = m++;
    int mb = m; for (int z = 0; z < n; z++) if (col[z] == 1) lab[z] = mb++;
    FILE *o = fopen(argv[5], "w"); fprintf(o, "%d\n", n);
    for (int z = 0; z < n; z++) if (col[z] == 0) for (int j = 0; j < 3; j++) fprintf(o, "%d %d\n", lab[z], lab[nb[z][j]]);
    fclose(o); return 0;
}
