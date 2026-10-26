/* Voltage-lift controller annealer for the F_3 route-chart lift.
   Base: k+k bipartite multigraph from a file "i j colour" (colours 0..5, proper: each colour once per base vertex).
   Voltages v_e in Z_n. Controller vertices: A (i,g) -> id i*n+g ; B (j,h) -> id m+j*n+h ; edge (i,g)~(j,g+v_e), colour c_e.
   Cost = number of (same-side) ordered pairs (u,v) with no nonsingular NB 4-walk of the chart (both sides),
   plus 1000 per base pair with two equal voltages (parallel edges).
   usage: ctrl3 base.txt n chart.txt seconds seed out.edges */
#include "f3.h"
#include <time.h>
#include <math.h>
static uint64_t rs = 88172645463325252ULL;
static uint64_t xr(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int k, nE, n, m;
static int be_i[200], be_j[200], be_c[200], be_v[200];
static int *nbA, *nbB; /* nbA[u*6+c] = B-vertex, nbB[w*6+c] = A-vertex */
static int goodlist[2][1500][4]; static int ngood[2];
static int mark[4096]; static int stamp = 0;
static void build(void) {
    for (int e = 0; e < nE; e++) for (int g = 0; g < n; g++) {
        int a = be_i[e] * n + g, b = be_j[e] * n + (g + be_v[e]) % n;
        nbA[a * 6 + be_c[e]] = b; nbB[b * 6 + be_c[e]] = a;
    }
}
static int penalty(void) {
    int p = 0;
    for (int e = 0; e < nE; e++) for (int f = e + 1; f < nE; f++)
        if (be_i[e] == be_i[f] && be_j[e] == be_j[f] && be_v[e] == be_v[f]) p += 1000;
    return p;
}
static int cost(void) {
    int tot = penalty();
    for (int side = 0; side < 2; side++) {
        for (int u = 0; u < m; u++) {
            stamp++; int cov = 0;
            for (int q = 0; q < ngood[side]; q++) {
                const int *c = goodlist[side][q]; int x, y;
                if (side == 0) { x = nbA[u * 6 + c[0]]; y = nbB[x * 6 + c[1]]; x = nbA[y * 6 + c[2]]; y = nbB[x * 6 + c[3]]; }
                else { x = nbB[u * 6 + c[0]]; y = nbA[x * 6 + c[1]]; x = nbB[y * 6 + c[2]]; y = nbA[x * 6 + c[3]]; }
                if (mark[y] != stamp) { mark[y] = stamp; cov++; }
            }
            tot += m - cov;
        }
    }
    return tot;
}
static void dump_edges(const char *path) {
    FILE *f = fopen(path, "w");
    fprintf(f, "%d %d\n", m, 6 * m);
    for (int u = 0; u < m; u++) for (int c = 0; c < 6; c++) fprintf(f, "%d %d %d\n", u, nbA[u * 6 + c], c);
    fclose(f);
}
int main(int argc, char **argv) {
    FILE *bf = fopen(argv[1], "r"); nE = 0; int i, j, c; int maxi = 0;
    while (fscanf(bf, "%d %d %d", &i, &j, &c) == 3) { be_i[nE] = i; be_j[nE] = j; be_c[nE] = c; nE++; if (i + 1 > maxi) maxi = i + 1; if (j + 1 > maxi) maxi = j + 1; }
    fclose(bf); k = maxi; n = atoi(argv[2]); m = k * n;
    if (!chart_read(argv[3])) { printf("bad chart\n"); return 1; }
    compute_good();
    for (int s = 0; s < 2; s++) { ngood[s] = 0; for (int c1 = 0; c1 < 6; c1++) for (int c2 = 0; c2 < 6; c2++) for (int c3 = 0; c3 < 6; c3++) for (int c4 = 0; c4 < 6; c4++)
        if (good[s][c1][c2][c3][c4]) { goodlist[s][ngood[s]][0] = c1; goodlist[s][ngood[s]][1] = c2; goodlist[s][ngood[s]][2] = c3; goodlist[s][ngood[s]][3] = c4; ngood[s]++; } }
    printf("good patterns A %d B %d\n", ngood[0], ngood[1]);
    double secs = atof(argv[4]); rs ^= (uint64_t)atoll(argv[5]) * 0x9E3779B97F4A7C15ULL; rs |= 1;
    nbA = malloc(sizeof(int) * m * 6); nbB = malloc(sizeof(int) * m * 6);
    for (int e = 0; e < nE; e++) be_v[e] = xr() % n;
    build(); int cur = cost(), best = cur; int bestv[200]; memcpy(bestv, be_v, sizeof be_v);
    time_t t0 = time(NULL); long it = 0; double T0 = 3.0, T1 = 0.2;
    while (best > 0) {
        it++;
        if ((it & 15) == 0) { double el = difftime(time(NULL), t0); if (el >= secs) break; }
        double el = difftime(time(NULL), t0); double T = T0 * pow(T1 / T0, el / secs);
        int e = xr() % nE; int old = be_v[e]; int nv = xr() % n; if (nv == old) continue;
        be_v[e] = nv; build();
        int nc = cost();
        if (nc <= cur || (double)(xr() % 1000000) / 1e6 < exp(-(nc - cur) / T)) {
            cur = nc; if (cur < best) { best = cur; memcpy(bestv, be_v, sizeof be_v); }
        } else { be_v[e] = old; build(); }
    }
    memcpy(be_v, bestv, sizeof be_v); build();
    { int diag=0, off=0; for (int u=0;u<m;u++){ stamp++; int cov=0; int hit[4096]; (void)hit;
        for (int q=0;q<ngood[0];q++){ const int*c=goodlist[0][q]; int x=nbA[u*6+c[0]]; int y=nbB[x*6+c[1]]; x=nbA[y*6+c[2]]; y=nbB[x*6+c[3]]; if(mark[y]!=stamp){mark[y]=stamp;cov++;} }
        for (int v=0; v<m; v++) if (mark[v]!=stamp) { if (v==u) diag++; else off++; } }
      printf("A-side uncovered: diagonal %d off-diagonal %d\n", diag, off); }
    printf("m %d n %d best uncovered-cost %d iterations %ld secs %.0f\n", m, n, best, it, difftime(time(NULL), t0));
    if (best == 0) { dump_edges(argv[6]); printf("wrote %s\n", argv[6]); }
    return 0;
}
