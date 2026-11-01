/* Multi-orbit controllers for a PENCIL-COMPLETE chart (chart_search.c / chart2.py) with a known singular-pattern
   table (chart_patterns.py).  Base: 4-regular bipartite multigraph on k + k vertices, properly 4-edge-coloured here
   (Konig).  Lift by a group G (voltage v_e, (a_i,g) ~ (b_j, v_e g)); the controller edge inherits the base colour.
   A same-side controller pair (u, v) is covered in the route-chart lift iff
     - v != u and v is the end of a walk of length 2 from u (controller distance 2: pencil-complete chart), or
     - v is the end of a nonbacktracking walk of length 4 whose colour pattern is nonsingular for the chart.
   Cost = uncovered (source orbit, target) pairs; 0 means the lift has diameter <= 5.
   usage: mlift_chart BASE TABLE PATTERNS seconds seed [T0] [out.edges]
   out.edges: lines "a b colour" (A-vertex (a_i,g) -> i*n+g, B-vertex (b_j,h) -> j*n+h). */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <time.h>
#include <stdint.h>
static uint64_t rs = 88172645463325252ULL;
static inline uint64_t xr(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
int k, ne, EA[64], EB[64], col[64], n, *T, *Inv, e_id, istree[64], volt[64];
int singA[4][4][4][4], singB[4][4][4][4];
int nwA[32], wA[32][600][4], lenA[32][600], nwB[32], wB[32][600][4], lenB[32][600], endA[32][600], endB[32][600];
static inline int mul(int a, int b) { return T[a * n + b]; }
unsigned char *hit; int DIAGW = 1; int digon_of[64], h_inv = -1;
int cost(void) {
    int c = 0;
    for (int i = 0; i < k; i++) {
        memset(hit, 0, k * n);
        for (int w = 0; w < nwA[i]; w++) { int *E = wA[i][w], x;
            if (lenA[i][w] == 2) { x = mul(Inv[volt[E[1]]], volt[E[0]]); if (endA[i][w] == i && x == e_id) continue; }
            else x = mul(Inv[volt[E[3]]], mul(volt[E[2]], mul(Inv[volt[E[1]]], volt[E[0]])));
            hit[endA[i][w] * n + x] = 1; }
        for (int t = 0; t < k * n; t++) c += !hit[t];
        c += (DIAGW - 1) * !hit[i * n + e_id];
    }
    for (int j = 0; j < k; j++) {
        memset(hit, 0, k * n);
        for (int w = 0; w < nwB[j]; w++) { int *E = wB[j][w], x;
            if (lenB[j][w] == 2) { x = mul(volt[E[1]], Inv[volt[E[0]]]); if (endB[j][w] == j && x == e_id) continue; }
            else x = mul(volt[E[3]], mul(Inv[volt[E[2]]], mul(volt[E[1]], Inv[volt[E[0]]])));
            hit[endB[j][w] * n + x] = 1; }
        for (int t = 0; t < k * n; t++) c += !hit[t];
        c += (DIAGW - 1) * !hit[j * n + e_id];
    }
    return c;
}
int ncyc = 0, cyc_e[32][4], cyc_side[32], dep_e[32];
static void apply_cycles(void) {
    for (int c = 0; c < ncyc; c++) { int *E = cyc_e[c];
        /* A-side closed walk E0 E1 E2 E3 from a_i: word v3^-1 v2 v1^-1 v0 = e  =>  v3 = v2 v1^-1 v0
           B-side closed walk from b_j: word v3 v2^-1 v1 v0^-1 = e  =>  v3 = v0 v1^-1 v2 */
        if (cyc_side[c] == 0) volt[E[3]] = T[volt[E[2]] * n + T[Inv[volt[E[1]]] * n + volt[E[0]]]];
        else volt[E[3]] = T[volt[E[0]] * n + T[Inv[volt[E[1]]] * n + volt[E[2]]]];
    }
}
static void apply_digons(void) { apply_cycles(); if (h_inv < 0) return; for (int e = 0; e < ne; e++) if (digon_of[e] >= 0) volt[e] = T[volt[digon_of[e]] * n + h_inv]; }
int parallel_ok(void) { for (int a = 0; a < ne; a++) for (int b = a + 1; b < ne; b++) if (EA[a] == EA[b] && EB[a] == EB[b] && volt[a] == volt[b]) return 0; return 1; }
/* proper 4-edge-colouring of the bipartite multigraph by peeling perfect matchings (augmenting paths) */
int used[64], matchB[32], visB[32];
int aug(int a, int c) { for (int e = 0; e < ne; e++) if (!used[e] && EA[e] == a && !visB[EB[e]]) { visB[EB[e]] = 1;
        if (matchB[EB[e]] < 0 || aug(EA[matchB[EB[e]]], c)) { matchB[EB[e]] = e; return 1; } } return 0; }
void colour(void) {
    memset(used, 0, sizeof used);
    for (int c = 0; c < 4; c++) {
        for (int j = 0; j < k; j++) matchB[j] = -1;
        for (int a = 0; a < k; a++) { memset(visB, 0, sizeof visB); if (!aug(a, c)) { printf("colouring failed\n"); exit(9); } }
        for (int j = 0; j < k; j++) { col[matchB[j]] = c; used[matchB[j]] = 1; }
    }
}
int main(int argc, char **argv) {
    FILE *f = fopen(argv[1], "r"); if (fscanf(f, "%d", &k) != 1) return 2;
    ne = 4 * k; for (int i = 0; i < ne; i++) if (fscanf(f, "%d %d", &EA[i], &EB[i]) != 2) return 3; fclose(f);
    f = fopen(argv[2], "r"); if (fscanf(f, "%d", &n) != 1) return 4;
    T = malloc(sizeof(int) * n * n); Inv = malloc(sizeof(int) * n);
    for (int i = 0; i < n * n; i++) if (fscanf(f, "%d", &T[i]) != 1) return 5; fclose(f);
    for (int i = 0; i < n; i++) { int ok = 1; for (int j = 0; j < n; j++) if (T[i * n + j] != j) { ok = 0; break; } if (ok) e_id = i; }
    for (int i = 0; i < n; i++) for (int j = 0; j < n; j++) if (T[i * n + j] == e_id) Inv[i] = j;
    f = fopen(argv[3], "r"); char side[4]; int a1, a2, a3, a4, r, np = 0;
    while (fscanf(f, "%3s %d %d %d %d %d", side, &a1, &a2, &a3, &a4, &r) == 6) { np++; if (side[0] == 'A') singA[a1][a2][a3][a4] = (r < 4); else singB[a1][a2][a3][a4] = (r < 4); }
    fclose(f); if (np != 216) { printf("pattern file has %d lines\n", np); return 6; }
    double secs = atof(argv[4]); rs ^= (uint64_t)atoll(argv[5]) * 0x9E3779B97F4A7C15ULL;
    double T0 = argc > 6 ? atof(argv[6]) : 2.0; const char *out = argc > 7 ? argv[7] : NULL;
    hit = malloc(k * n + 1); if (getenv("DIAGW")) DIAGW = atoi(getenv("DIAGW"));
    colour();
    int seen[64] = {0}, q[64], h = 0, t = 0; seen[0] = 1; q[t++] = 0;
    while (h < t) { int x = q[h++];
        for (int i = 0; i < ne; i++) { int a = EA[i], b = k + EB[i], y = -1;
            if (x == a && !seen[b]) y = b; else if (x == b && !seen[a]) y = a;
            if (y >= 0) { seen[y] = 1; q[t++] = y; istree[i] = 1; } } }
    if (t != 2 * k) { printf("base disconnected\n"); return 7; }
    for (int i = 0; i < k; i++) { nwA[i] = 0;
        for (int e1 = 0; e1 < ne; e1++) if (EA[e1] == i)
        for (int e2 = 0; e2 < ne; e2++) if (EB[e2] == EB[e1]) {
            { int w = nwA[i]++; wA[i][w][0] = e1; wA[i][w][1] = e2; lenA[i][w] = 2; endA[i][w] = EA[e2]; }
            if (e2 == e1) continue;
            for (int e3 = 0; e3 < ne; e3++) if (e3 != e2 && EA[e3] == EA[e2])
            for (int e4 = 0; e4 < ne; e4++) if (e4 != e3 && EB[e4] == EB[e3]) {
                if (singA[col[e1]][col[e2]][col[e3]][col[e4]]) continue;
                int w = nwA[i]++; wA[i][w][0] = e1; wA[i][w][1] = e2; wA[i][w][2] = e3; wA[i][w][3] = e4; lenA[i][w] = 4; endA[i][w] = EA[e4]; } } }
    for (int j = 0; j < k; j++) { nwB[j] = 0;
        for (int e1 = 0; e1 < ne; e1++) if (EB[e1] == j)
        for (int e2 = 0; e2 < ne; e2++) if (EA[e2] == EA[e1]) {
            { int w = nwB[j]++; wB[j][w][0] = e1; wB[j][w][1] = e2; lenB[j][w] = 2; endB[j][w] = EB[e2]; }
            if (e2 == e1) continue;
            for (int e3 = 0; e3 < ne; e3++) if (e3 != e2 && EB[e3] == EB[e2])
            for (int e4 = 0; e4 < ne; e4++) if (e4 != e3 && EA[e4] == EA[e3]) {
                if (singB[col[e1]][col[e2]][col[e3]][col[e4]]) continue;
                int w = nwB[j]++; wB[j][w][0] = e1; wB[j][w][1] = e2; wB[j][w][2] = e3; wB[j][w][3] = e4; lenB[j][w] = 4; endB[j][w] = EB[e4]; } } }
    for (int e = 0; e < ne; e++) digon_of[e] = -1;
    if (getenv("DIGON")) {
        for (int x = 0; x < n; x++) if (x != e_id && T[x * n + x] == e_id) { h_inv = x; break; }
        if (getenv("HINV")) h_inv = atoi(getenv("HINV"));
        if (h_inv < 0) { printf("no involution in the group\n"); return 8; }
        for (int e = 0; e < ne; e++) for (int f = 0; f < e; f++)
            if (EA[e] == EA[f] && EB[e] == EB[f] && digon_of[f] < 0) { int used2 = 0; for (int g = 0; g < ne; g++) if (digon_of[g] == f) used2 = 1;
                if (!used2) { digon_of[e] = f; break; } }
        /* a tied edge must not be a spanning-tree edge: re-gauge by freeing it (tree edges stay at e only if untied) */
        for (int e = 0; e < ne; e++) if (digon_of[e] >= 0 && istree[e]) { printf("tied edge %d is a tree edge; reorder base\n", e); }
    }
    int isdep[64] = {0};
    if (getenv("CYC")) {
        /* greedy choice: cover every base vertex (both sides) by a closed NB 4-walk with a nonsingular pattern whose
           last edge is non-tree, not yet dependent, and whose other edges are not dependent edges of later cycles */
        int covered[64] = {0};
        for (int side = 0; side < 2; side++) for (int x = 0; x < k; x++) {
            if (covered[side * k + x]) continue;
            int found = 0;
            int nw = side ? nwB[x] : nwA[x];
            for (int w = 0; w < nw && !found; w++) {
                int *E = side ? wB[x][w] : wA[x][w]; int L = side ? lenB[x][w] : lenA[x][w], end = side ? endB[x][w] : endA[x][w];
                if (L != 4 || end != x) continue;
                if (E[0] == E[3]) continue;
                for (int r = 0; r < 4 && !found; r++) {   /* try each edge as the dependent one by rotating? keep last edge */
                    int d = E[3];
                    if (istree[d] || isdep[d]) break;
                    int bad = 0; for (int t = 0; t < 3; t++) if (isdep[E[t]]) bad = 1;
                    if (bad) break;
                    cyc_side[ncyc] = side; for (int t = 0; t < 4; t++) cyc_e[ncyc][t] = E[t]; dep_e[ncyc] = d; isdep[d] = 1; ncyc++; found = 1;
                    /* mark covered base vertices along the cycle */
                    if (side == 0) { covered[EA[E[0]]] = 1; covered[k + EB[E[0]]] = 1; covered[EA[E[1]]] = 1; covered[k + EB[E[2]]] = 1; }
                    else { covered[k + EB[E[0]]] = 1; covered[EA[E[0]]] = 1; covered[k + EB[E[1]]] = 1; covered[EA[E[2]]] = 1; }
                }
            }
            if (!found) { printf("no usable 4-cycle for base vertex %c%d\n", side ? 'b' : 'a', x); }
        }
        printf("forced %d base 4-cycles\n", ncyc);
    }
    do { for (int i = 0; i < ne; i++) volt[i] = istree[i] ? e_id : (int)(xr() % n); apply_digons(); } while (!parallel_ok());
    int c = cost(), best = c, bv[64]; memcpy(bv, volt, sizeof volt);
    clock_t t0 = clock(); long it = 0;
    int free_e[64], nf = 0; for (int i = 0; i < ne; i++) if (!istree[i] && digon_of[i] < 0 && !isdep[i]) free_e[nf++] = i;
    while (best > 0 && (double)(clock() - t0) / CLOCKS_PER_SEC < secs) {
        it++;
        double fr = (double)(clock() - t0) / CLOCKS_PER_SEC / secs; double TT = T0 * pow(0.02, fr);
        int ei = free_e[xr() % nf], old = volt[ei]; int sv[64]; memcpy(sv, volt, sizeof volt); volt[ei] = xr() % n; apply_digons();
        if (!parallel_ok()) { memcpy(volt, sv, sizeof volt); continue; }
        int c2 = cost();
        if (c2 <= c || exp((c - c2) / TT) > (double)(xr() % 1000000) / 1e6) { c = c2; if (c < best) { best = c; memcpy(bv, volt, sizeof volt); } }
        else memcpy(volt, sv, sizeof volt);
        (void)old;
        if (it % 200000 == 0 && c > best + 20) { memcpy(volt, bv, sizeof volt); c = best; }
    }
    printf("k=%d n=%d m=%d best_cost=%d iters=%ld volt=", k, n, k * n, best, it);
    for (int i = 0; i < ne; i++) printf("%d%c", bv[i], i + 1 < ne ? ',' : '\n');
    if (out && (best == 0 || getenv("WRITEBEST"))) { FILE *g = fopen(out, "w");
        for (int i = 0; i < ne; i++) for (int x = 0; x < n; x++) fprintf(g, "%d %d %d\n", EA[i] * n + x, EB[i] * n + mul(bv[i], x), col[i]);
        fclose(g); }
    return 0;
}
