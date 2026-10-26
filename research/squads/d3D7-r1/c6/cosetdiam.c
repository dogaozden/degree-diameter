/* Coset graphs with point stabilisers of order 2 (card c6).
 * Input: dump file from dump.g. For each group G (order n), pair (a,b) of involutions (H1=<a>, H2=<b>),
 * and each D = union of H1 g H2 double cosets with |D| = 6, build the bipartite graph
 * (white cosets xH1, black cosets yH2, x~y iff x^-1 y in D), check connectivity, and compute
 * cost = #unordered same-side pairs at distance > 6 (diameter <= 7 iff cost = 0).
 * Usage: cosetdiam DUMP OUTPREFIX [minorder] */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAXV 512
static int ord, nh;
static int *M;
static int wid[256], bid[256], wrep[256], brep[256];
static int adjw[128][3], adjb[128][3], degb[128];
static int dist[MAXV], queue[MAXV];

static int bfs(int s, int nv, int *d) {
    int h = 0, t = 0, v, k, u;
    for (v = 0; v < nv; v++) d[v] = -1;
    d[s] = 0; queue[t++] = s;
    while (h < t) {
        v = queue[h++];
        if (v < nh) {
            for (k = 0; k < 3; k++) { u = nh + adjw[v][k]; if (d[u] < 0) { d[u] = d[v] + 1; queue[t++] = u; } }
        } else {
            for (k = 0; k < degb[v - nh]; k++) { u = adjb[v - nh][k]; if (d[u] < 0) { d[u] = d[v] + 1; queue[t++] = u; } }
        }
    }
    return t;
}

int main(int argc, char **argv) {
    FILE *f = fopen(argv[1], "r");
    const char *prefix = argv[2];
    int minorder = argc > 3 ? atoi(argv[3]) : 0;
    char tok[64];
    int gi = 0;
    int curn = 0;
    long tried = 0, conn = 0;
    int bestcost_all = -1, bestdiam_all = 1000;
    int histo[64]; memset(histo, 0, sizeof histo);
    long bestcost_g = -1; int bestdiam_g = 0, bestpairs7_g = 0;
    char gname[64] = "";
    int ngroups = 0;
    int bestcost_order = -1; long triedorder = 0; int bestdiam_order = 1000, bestp7_order = -1;
    int found = 0;
    int a = 0, b = 0;
    int dsz[256], dele[256][8], ndc;
    int ndcs;
    (void)ndc; (void)ndcs;

    if (!f) { perror("dump"); return 1; }
    while (fscanf(f, "%63s", tok) == 1) {
        if (strcmp(tok, "GROUP") == 0) {
            int n, i;
            fscanf(f, "%d %d", &n, &i);
            if (curn && n != curn) { /* order change: print order summary below */ }
            ord = n; nh = n / 2; curn = n;
            if (M) free(M);
            M = malloc(sizeof(int) * n * n);
            for (int x = 0; x < n * n; x++) fscanf(f, "%d", &M[x]);
            gi = i; ngroups++;
            bestcost_g = -1; bestdiam_g = 0; bestpairs7_g = 0;
            /* ensure the dump is consistent */
            if (M[0] != 0) { fprintf(stderr, "identity not 0\n"); return 2; }
            continue;
        }
        if (strcmp(tok, "PAIR") == 0) {
            int nd;
            fscanf(f, "%d %d %d", &a, &b, &nd);
            ndcs = nd;
            ndc = 0;
            for (int k = 0; k < nd; k++) {
                int s; fscanf(f, "%d", &s);
                dsz[k] = s;
                for (int j = 0; j < s; j++) fscanf(f, "%d", &dele[k][j]);
            }
            if (minorder && ord < minorder) continue;
            /* white cosets {x, xa}; black cosets {y, yb} */
            if (ord > 256) continue;
            for (int x = 0; x < ord; x++) wid[x] = bid[x] = -1;
            int w = 0, bb = 0;
            for (int x = 0; x < ord; x++) if (wid[x] < 0) {
                wid[x] = w; wid[M[x * ord + a]] = w; wrep[w] = x; w++; }
            for (int y = 0; y < ord; y++) if (bid[y] < 0) {
                bid[y] = bb; bid[M[y * ord + b]] = bb; brep[bb] = y; bb++; }
            if (w != nh || bb != nh) { fprintf(stderr, "coset count mismatch\n"); return 3; }
            /* double cosets of size 2 (S) and 4 (F) */
            int S[256], ns = 0, F[256], nf = 0;
            for (int k = 0; k < nd; k++) { if (dsz[k] == 2) S[ns++] = k; else if (dsz[k] == 4) F[nf++] = k; }
            /* enumerate candidate D: one F + one S, or three S */
            int total = 0;
            int cand[64][2]; int ncand = 0; /* (type, index) encoded below */
            (void)total; (void)cand; (void)ncand;
            int list_i[3];
            int nopts = nf * ns + (ns * (ns - 1) * (ns - 2)) / 6;
            static int triples[200000][3];
            int ntr = 0;
            for (int i0 = 0; i0 < ns; i0++) for (int i1 = i0 + 1; i1 < ns; i1++) for (int i2 = i1 + 1; i2 < ns; i2++) {
                triples[ntr][0] = i0; triples[ntr][1] = i1; triples[ntr][2] = i2; ntr++; }
            for (int opt = 0; opt < nopts; opt++) {
                int sel[8], nsel = 0;
                if (opt < nf * ns) {
                    int fi = opt / ns, si = opt % ns;
                    sel[nsel++] = F[fi]; sel[nsel++] = S[si];
                } else {
                    int r = opt - nf * ns;
                    int t0 = triples[r][0], t1 = triples[r][1], t2 = triples[r][2];
                    sel[nsel++] = S[t0]; sel[nsel++] = S[t1]; sel[nsel++] = S[t2];
                    (void)list_i;
                }
                /* D elements */
                int De[8], nde = 0;
                for (int s = 0; s < nsel; s++) for (int j = 0; j < dsz[sel[s]]; j++) De[nde++] = dele[sel[s]][j];
                if (nde != 6) { fprintf(stderr, "bad |D|\n"); return 4; }
                /* build white adjacency */
                int ok = 1;
                for (int w2 = 0; w2 < nh && ok; w2++) {
                    int x = wrep[w2], cntn = 0;
                    for (int j = 0; j < 6; j++) {
                        int y = M[x * ord + De[j]];
                        int bl = bid[y], dup = 0;
                        for (int q = 0; q < cntn; q++) if (adjw[w2][q] == bl) dup = 1;
                        if (!dup) { if (cntn < 3) adjw[w2][cntn] = bl; cntn++; }
                    }
                    if (cntn != 3) ok = 0;
                }
                if (!ok) { fprintf(stderr, "white degree != 3\n"); return 5; }
                for (int q = 0; q < nh; q++) degb[q] = 0;
                for (int w2 = 0; w2 < nh; w2++) for (int q = 0; q < 3; q++) {
                    int bl = adjw[w2][q];
                    if (degb[bl] >= 3) { ok = 0; break; }
                    adjb[bl][degb[bl]++] = w2;
                }
                if (!ok) { fprintf(stderr, "black degree\n"); return 6; }
                tried++; triedorder++;
                int nv = 2 * nh;
                int cnt0 = bfs(0, nv, dist);
                if (cnt0 < nv) continue; /* disconnected */
                conn++;
                int ecc = 0, f7W = 0, cW = 0;
                for (int v = 0; v < nv; v++) {
                    if (dist[v] > ecc) ecc = dist[v];
                    if (dist[v] > 7) f7W++;
                    if (v < nh && dist[v] > 6) cW++;
                }
                int ecc2 = 0, f7B = 0, cB = 0;
                bfs(nh, nv, dist);
                for (int v = 0; v < nv; v++) {
                    if (dist[v] > ecc2) ecc2 = dist[v];
                    if (dist[v] > 7) f7B++;
                    if (v >= nh && dist[v] > 6) cB++;
                }
                int diam = ecc > ecc2 ? ecc : ecc2;
                long ordered = (long)nh * cW + (long)nh * cB;
                long cost = ordered / 2;
                long pairs7 = ((long)nh * f7W + (long)nh * f7B) / 2;
                if (diam <= 63) histo[diam]++;
                if (diam < bestdiam_order) bestdiam_order = diam;
                if (bestcost_order < 0 || cost < bestcost_order) bestcost_order = (int)cost;
                if (bestcost_g < 0 || cost < bestcost_g || (cost == bestcost_g && diam < bestdiam_g)) {
                    bestcost_g = cost; bestdiam_g = diam; bestpairs7_g = (int)pairs7;
                }
                if (bestp7_order < 0 || (cost == bestcost_order && pairs7 < bestp7_order)) bestp7_order = (int)pairs7;
                if (getenv("DBG")) printf("DBG g%d a%d b%d opt%d cost %ld diam %d\n", gi, a, b, opt, cost, diam);
                if (cost == 0 && !found) {
                    char fn[256];
                    sprintf(fn, "%s_n%d_g%d_a%d_b%d_o%d.edges", prefix, 2 * nh, gi, a, b, opt);
                    FILE *o = fopen(fn, "w");
                    fprintf(o, "%d\n", nv);
                    for (int w2 = 0; w2 < nh; w2++) for (int q = 0; q < 3; q++) fprintf(o, "%d %d\n", w2, nh + adjw[w2][q]);
                    fclose(o);
                    printf("FOUND diam %d cost 0: %s\n", diam, fn);
                    found = 1;
                }
            }
        }
    }
    printf("ORDER %d tried %ld connected %ld bestcost %d bestdiam %d bestpairs7 %d\n",
           curn, triedorder, conn, bestcost_order, bestdiam_order, bestp7_order);
    fclose(f);
    return 0;
}
