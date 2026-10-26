/* Voltage controller for the 5-letter F4 route-chart lift (degree 5*4 = 20, fibre F4^4 = 256).
   Base: bipartite, 5-regular, properly 5-edge-coloured, k+k vertices. Lift group Z_G:
   controller vertex (a_i, g) ~ (b_j, g + v_e) for base edge e = (a_i, b_j), colour t; the lift joins
   (a_i, g, x) ~ (b_j, g+v_e, A_t x + lambda b_t) for lambda in F4.
   Coverage (sufficient, from nonsingular nonbacktracking walks; see gf4.h word_full):
     same side: for side S, orbit i, orbit j, voltage h in Z_G: some NB walk of length 4 from (S,i) to (S,j) with
       voltage h and nonsingular colour word;
     cross: some NB walk of length 5 from A-orbit i to B-orbit j with voltage h and nonsingular word.
   Cost = number of uncovered triples. Cost 0 => lift has diameter <= 5 (to be confirmed by apsp).
   usage: ctrl5 CHART BASE G seconds seed OUT [T0]
   BASE: "k" then 5k lines "a b colour". OUT: "k G" then "a b colour v" lines (v = voltage), then "cost C". */
#include "gf4.h"
static int k, ne, G, EA[64], EB[64], COL[64], VOLT[64], istree[64];
static int nbe[2][16][5];
typedef struct { int s, i, j, L; int e[5], sg[5]; } walk;
static walk *W4, *W5; static int nW4 = 0, nW5 = 0;
static unsigned char *h4, *h5;
static void add_walks(int s0, int i0, int L, int depth, int side, int orb, int *colw, int *ed, int *sg, walk *arr, int *cnt) {
    if (depth == L) {
        if (word_full(colw, L, s0)) { walk *w = &arr[*cnt]; w->s = s0; w->i = i0; w->j = orb; w->L = L;
            for (int d = 0; d < L; d++) { w->e[d] = ed[d]; w->sg[d] = sg[d]; } (*cnt)++; }
        return;
    }
    for (int c = 0; c < 5; c++) {
        if (depth > 0 && c == colw[depth - 1]) continue;
        int e = nbe[side][orb][c];
        colw[depth] = c; ed[depth] = e; sg[depth] = side == 0 ? 1 : -1;
        add_walks(s0, i0, L, depth + 1, 1 - side, side == 0 ? EB[e] : EA[e], colw, ed, sg, arr, cnt);
    }
}
static int cost(void) {
    memset(h4, 0, 2 * k * k * G); memset(h5, 0, k * k * G);
    for (int q = 0; q < nW4; q++) { walk *w = &W4[q]; int h = 0;
        for (int d = 0; d < 4; d++) { int v = VOLT[w->e[d]]; h += w->sg[d] > 0 ? v : (G - v) % G; }
        h4[((w->s * k + w->i) * k + w->j) * G + h % G] = 1; }
    for (int q = 0; q < nW5; q++) { walk *w = &W5[q]; int h = 0;
        for (int d = 0; d < 5; d++) { int v = VOLT[w->e[d]]; h += w->sg[d] > 0 ? v : (G - v) % G; }
        h5[(w->i * k + w->j) * G + h % G] = 1; }
    int c = 0;
    for (int t = 0; t < 2 * k * k * G; t++) c += !h4[t];
    for (int t = 0; t < k * k * G; t++) c += !h5[t];
    return c;
}
int main(int argc, char **argv) {
    if (argc < 7) { fprintf(stderr, "usage: ctrl5 CHART BASE G seconds seed OUT [T0]\n"); return 1; }
    if (!read_chart(argv[1])) { printf("bad chart\n"); return 2; }
    FILE *f = fopen(argv[2], "r"); if (!f || fscanf(f, "%d", &k) != 1) return 3; ne = 5 * k;
    for (int e = 0; e < ne; e++) if (fscanf(f, "%d %d %d", &EA[e], &EB[e], &COL[e]) != 3) return 4; fclose(f);
    G = atoi(argv[3]); double secs = atof(argv[4]); rs ^= (uint64_t)atoll(argv[5]) * 0x9E3779B97F4A7C15ULL; const char *out = argv[6];
    double T0 = argc > 7 ? atof(argv[7]) : 1.0;
    for (int s = 0; s < 2; s++) for (int i = 0; i < k; i++) for (int c = 0; c < 5; c++) nbe[s][i][c] = -1;
    for (int e = 0; e < ne; e++) { if (nbe[0][EA[e]][COL[e]] >= 0 || nbe[1][EB[e]][COL[e]] >= 0) { printf("not proper\n"); return 5; }
        nbe[0][EA[e]][COL[e]] = e; nbe[1][EB[e]][COL[e]] = e; }
    for (int s = 0; s < 2; s++) for (int i = 0; i < k; i++) for (int c = 0; c < 5; c++) if (nbe[s][i][c] < 0) { printf("not 5-regular\n"); return 6; }
    int seen[32] = {0}, q[32], hd = 0, tl = 0; seen[0] = 1; q[tl++] = 0;
    while (hd < tl) { int x = q[hd++]; for (int e = 0; e < ne; e++) { int a = EA[e], b = k + EB[e], y = -1;
        if (x == a && !seen[b]) y = b; else if (x == b && !seen[a]) y = a; if (y >= 0) { seen[y] = 1; q[tl++] = y; istree[e] = 1; } } }
    if (tl != 2 * k) { printf("base disconnected\n"); return 7; }
    int cap = 1 << 20; W4 = malloc(sizeof(walk) * cap); W5 = malloc(sizeof(walk) * cap);
    int colw[5], ed[5], sg[5];
    for (int s0 = 0; s0 < 2; s0++) for (int i = 0; i < k; i++) add_walks(s0, i, 4, 0, s0, i, colw, ed, sg, W4, &nW4);
    for (int i = 0; i < k; i++) add_walks(0, i, 5, 0, 0, i, colw, ed, sg, W5, &nW5);
    h4 = malloc(2 * k * k * G + 1); h5 = malloc(k * k * G + 1);
    printf("k %d G %d NB4-full walks %d NB5-full walks %d\n", k, G, nW4, nW5);
    /* random initial voltages (tree edges 0), annealing over free edges */
    int freeE[64], nfree = 0; for (int e = 0; e < ne; e++) if (!istree[e]) freeE[nfree++] = e;
    for (int e = 0; e < ne; e++) VOLT[e] = istree[e] ? 0 : (int)(xr() % G);
    int c = cost(), best = c; int bestV[64]; memcpy(bestV, VOLT, sizeof VOLT);
    clock_t t0 = clock(); long it = 0;
    while (c > 0 && (double)(clock() - t0) / CLOCKS_PER_SEC < secs) {
        it++;
        double T = T0 * (1.0 - (double)((clock() - t0) / CLOCKS_PER_SEC) / secs) + 0.02;
        int e = freeE[xr() % nfree]; int old = VOLT[e]; int nv = (int)(xr() % G); if (nv == old) continue;
        VOLT[e] = nv; int c2 = cost();
        double u = (xr() >> 11) * (1.0 / 9007199254740992.0);
        if (c2 <= c || u < __builtin_exp(-(c2 - c) / T)) c = c2; else VOLT[e] = old;
        if (c < best) { best = c; memcpy(bestV, VOLT, sizeof VOLT); }
    }
    memcpy(VOLT, bestV, sizeof VOLT); c = cost();
    printf("best cost %d after %ld iters (time %.1f s)\n", c, it, (double)(clock() - t0) / CLOCKS_PER_SEC);
    f = fopen(out, "w"); fprintf(f, "%d %d\n", k, G);
    for (int e = 0; e < ne; e++) fprintf(f, "%d %d %d %d\n", EA[e], EB[e], COL[e], VOLT[e]);
    fprintf(f, "cost %d\n", c); fclose(f);
    return 0;
}
