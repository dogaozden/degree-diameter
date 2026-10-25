/* walk.c: combinatorial "cluster model" of same-side hub distances for a hubs3 layout.
   Model: H-edges cost 1; two hubs owned by the same point (co-owners, same level) cost 2; two hubs whose owners lie on
   the same spread line at a level cost 4 (real path hub-(p,i)-(L,i)-(p',i)-hub). Model distance is an upper bound on the
   real distance. Usage: walk HUBS3 SRC [side]  -> walk-count statistics for same-side targets from SRC (side 0 = L). */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
int HL, HP, m, NV; int *own; int *eu, *ev; int *deg, *adjs, *adj; int *cl_start, *cl_mem; /* clusters: per (side,level,line) */
int *hub_cl; /* hub_cl[v*5+i] = cluster id */ int ncl;
int main(int argc, char **argv) {
    FILE *f = fopen(argv[1], "r"); int src = atoi(argv[2]);
    if (fscanf(f, "%d %d %d", &HL, &HP, &m) != 3) return 1; NV = HL + HP;
    own = malloc(sizeof(int) * 5 * NV);
    for (int v = 0; v < NV; v++) for (int i = 0; i < 5; i++) if (fscanf(f, "%d", &own[v * 5 + i]) != 1) return 1;
    eu = malloc(sizeof(int) * m); ev = malloc(sizeof(int) * m); deg = calloc(NV, sizeof(int));
    for (int e = 0; e < m; e++) { int j, k; if (fscanf(f, "%d %d", &j, &k) != 2) return 1; eu[e] = j; ev[e] = HL + k; deg[j]++; deg[HL + k]++; }
    adjs = malloc(sizeof(int) * (NV + 1)); adjs[0] = 0; for (int v = 0; v < NV; v++) adjs[v + 1] = adjs[v] + deg[v];
    adj = malloc(sizeof(int) * 2 * m); int *pos = calloc(NV, sizeof(int));
    for (int e = 0; e < m; e++) { adj[adjs[eu[e]] + pos[eu[e]]++] = ev[e]; adj[adjs[ev[e]] + pos[ev[e]]++] = eu[e]; }
    /* clusters: key = side*5*731 + level*731 + line (lines < 730 assumed, owner/10 < 7300/10 = 730) */
    int NK = 2 * 5 * 731; int *cnt = calloc(NK, sizeof(int));
    hub_cl = malloc(sizeof(int) * NV * 5);
    for (int v = 0; v < NV; v++) { int side = v >= HL; for (int i = 0; i < 5; i++) { int key = (side * 5 + i) * 731 + own[v * 5 + i] / 10; hub_cl[v * 5 + i] = key; cnt[key]++; } }
    int *cs = malloc(sizeof(int) * (NK + 1)); cs[0] = 0; for (int k = 0; k < NK; k++) cs[k + 1] = cs[k] + cnt[k];
    cl_mem = malloc(sizeof(int) * NV * 5); int *cp = calloc(NK, sizeof(int));
    for (int v = 0; v < NV; v++) for (int i = 0; i < 5; i++) { int key = hub_cl[v * 5 + i]; cl_mem[cs[key] + cp[key]++] = v; }
    cl_start = cs;
    /* walk DP with exact model costs 1,2,4 */
    double *W = malloc(sizeof(double) * 7 * NV); memset(W, 0, sizeof(double) * 7 * NV);
    W[0 * NV + src] = 1.0;
    for (int t = 1; t <= 6; t++) {
        double *Wt = W + t * NV;
        for (int v = 0; v < NV; v++) {
            double s = 0;
            for (int a = adjs[v]; a < adjs[v + 1]; a++) s += W[(t - 1) * NV + adj[a]];
            if (t >= 2) for (int i = 0; i < 5; i++) {
                int key = hub_cl[v * 5 + i];
                for (int c = cl_start[key]; c < cl_start[key + 1]; c++) {
                    int u = cl_mem[c]; if (u == v) continue;
                    int co = (own[u * 5 + i] == own[v * 5 + i]); int w = co ? 2 : 4;
                    if (t - w >= 0) s += W[(t - w) * NV + u];
                }
            }
            Wt[v] = s;
        }
    }
    int side = (argc > 3) ? atoi(argv[3]) : 0; (void)side;
    int tgt_lo = 0, tgt_hi = HL; if (argc > 3 && atoi(argv[3]) == 1) { tgt_lo = HL; tgt_hi = NV; }
    double mn = 1e300, mx = 0, tot = 0; long unreached = 0, le1 = 0, le2 = 0; long hist[8] = {0};
    for (int v = tgt_lo; v < tgt_hi; v++) {
        double c = 0; for (int t = 0; t <= 6; t++) c += W[t * NV + v];
        if (c == 0) unreached++; if (c <= 1) le1++; if (c <= 2) le2++;
        if (c < mn) mn = c; if (c > mx) mx = c; tot += c;
        int b = c == 0 ? 0 : (c < 2 ? 1 : (c < 4 ? 2 : (c < 8 ? 3 : (c < 16 ? 4 : (c < 64 ? 5 : 6)))));
        hist[b]++;
    }
    printf("src=%d targets=[%d,%d): unreached=%ld  count<=1: %ld  count<=2: %ld  min=%.0f max=%.0f mean=%.2f\n", src, tgt_lo, tgt_hi, unreached, le1, le2, mn, mx, tot / (tgt_hi - tgt_lo));
    printf("hist(0,1-1.99,2-3.99,4-7.99,8-15.9,16-63,64+): %ld %ld %ld %ld %ld %ld %ld\n", hist[0], hist[1], hist[2], hist[3], hist[4], hist[5], hist[6]);
    return 0;
}
