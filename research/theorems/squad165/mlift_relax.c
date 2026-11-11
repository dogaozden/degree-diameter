/* RELAXED multi-orbit controllers (for pencil-complete charts, chart2.py / chart_search.c): every same-side pair
   within distance 4 (walks with backtracking allowed) and every vertex on a 4-cycle.  Derived from mlift.c:
   Multi-orbit controllers: voltage lift of a 4-regular bipartite base multigraph (k + k vertices) by a group G.
   Controller vertices (a_i, g), (b_j, g); base edge e = a_i b_j with voltage v_e: (a_i, g) ~ (b_j, v_e g).
   m = k |G| per side.  Exact-NB-4: from each source (a_i, e) [(b_j, e)] every (a_t, g) [(b_t, g)] must be the end of a
   walk e1 e2 e3 e4 of base edges with consecutive edges distinct.  Words: A source v4^-1 v3 v2^-1 v1, B source
   v4 v3^-1 v2 v1^-1.  Cost = uncovered (source, target) pairs (lifted cost = |G| * cost).  Spanning-tree voltages = e.
   Parallel base edges get distinct voltages (simple controller).
   usage: mlift BASE TABLE seconds seed [T0] [out.edges]
     BASE: first line k, then 4k lines "i j" (A-vertex i -- B-vertex j, 0-based), every vertex of degree 4.
     TABLE: first line n, then n*n ints, entry [i*n+j] = index of i*j.
   out.edges: lifted controller edge list "a b" with A-vertex (a_i,g) -> i*n+g, B-vertex (b_j,h) -> j*n+h. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <time.h>
#include <stdint.h>
static uint64_t rs = 88172645463325252ULL;
static inline uint64_t xr(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
int k, ne, EA[64], EB[64], n, *T, *Inv, e_id, istree[64];
int volt[64];
int nwA[32], wA[32][512][4], nwB[32], wB[32][512][4], endA[32][512], endB[32][512];
static inline int mul(int a, int b) { return T[a * n + b]; }
unsigned char *hit;
int has4cycle(void) {
    int miss = 0;
    for (int i = 0; i < k; i++) { int ok = 0;
        for (int w = 0; w < nwA[i] && !ok; w++) { int *E = wA[i][w];
            if (endA[i][w] != i || E[1] == E[0] || E[2] == E[1] || E[3] == E[2]) continue;
            if (mul(Inv[volt[E[3]]], mul(volt[E[2]], mul(Inv[volt[E[1]]], volt[E[0]]))) == e_id) ok = 1; }
        miss += !ok; }
    for (int j = 0; j < k; j++) { int ok = 0;
        for (int w = 0; w < nwB[j] && !ok; w++) { int *E = wB[j][w];
            if (endB[j][w] != j || E[1] == E[0] || E[2] == E[1] || E[3] == E[2]) continue;
            if (mul(volt[E[3]], mul(Inv[volt[E[2]]], mul(volt[E[1]], Inv[volt[E[0]]]))) == e_id) ok = 1; }
        miss += !ok; }
    return miss;
}
int cost(void) {
    int c = 4 * has4cycle();
    for (int i = 0; i < k; i++) {               /* A source a_i */
        memset(hit, 0, k * n);
        for (int w = 0; w < nwA[i]; w++) {
            int *E = wA[i][w];
            int x = mul(Inv[volt[E[3]]], mul(volt[E[2]], mul(Inv[volt[E[1]]], volt[E[0]])));
            hit[endA[i][w] * n + x] = 1;
        }
        for (int t = 0; t < k * n; t++) c += !hit[t];
    }
    for (int j = 0; j < k; j++) {               /* B source b_j */
        memset(hit, 0, k * n);
        for (int w = 0; w < nwB[j]; w++) {
            int *E = wB[j][w];
            int x = mul(volt[E[3]], mul(Inv[volt[E[2]]], mul(volt[E[1]], Inv[volt[E[0]]])));
            hit[endB[j][w] * n + x] = 1;
        }
        for (int t = 0; t < k * n; t++) c += !hit[t];
    }
    return c;
}
int parallel_ok(void) {
    for (int a = 0; a < ne; a++) for (int b = a + 1; b < ne; b++)
        if (EA[a] == EA[b] && EB[a] == EB[b] && volt[a] == volt[b]) return 0;
    return 1;
}
int main(int argc, char **argv) {
    FILE *f = fopen(argv[1], "r"); if (fscanf(f, "%d", &k) != 1) return 2;
    ne = 4 * k; for (int i = 0; i < ne; i++) if (fscanf(f, "%d %d", &EA[i], &EB[i]) != 2) return 3; fclose(f);
    f = fopen(argv[2], "r"); if (fscanf(f, "%d", &n) != 1) return 4;
    T = malloc(sizeof(int) * n * n); Inv = malloc(sizeof(int) * n);
    for (int i = 0; i < n * n; i++) if (fscanf(f, "%d", &T[i]) != 1) return 5; fclose(f);
    for (int i = 0; i < n; i++) { int ok = 1; for (int j = 0; j < n; j++) if (T[i * n + j] != j) { ok = 0; break; } if (ok) e_id = i; }
    for (int i = 0; i < n; i++) for (int j = 0; j < n; j++) if (T[i * n + j] == e_id) Inv[i] = j;
    double secs = atof(argv[3]); rs ^= (uint64_t)atoll(argv[4]) * 0x9E3779B97F4A7C15ULL;
    double T0 = argc > 5 ? atof(argv[5]) : 2.0; const char *out = argc > 6 ? argv[6] : NULL;
    hit = malloc(k * n + 1);
    /* degrees */
    int dA[32] = {0}, dB[32] = {0}; for (int i = 0; i < ne; i++) { dA[EA[i]]++; dB[EB[i]]++; }
    for (int i = 0; i < k; i++) if (dA[i] != 4 || dB[i] != 4) { printf("base not 4-regular\n"); return 6; }
    /* spanning tree by BFS over base vertices (A: 0..k-1, B: k..2k-1) */
    int seen[64] = {0}, q[64], h = 0, t = 0; seen[0] = 1; q[t++] = 0;
    while (h < t) { int x = q[h++];
        for (int i = 0; i < ne; i++) { int a = EA[i], b = k + EB[i], y = -1;
            if (x == a && !seen[b]) y = b; else if (x == b && !seen[a]) y = a;
            if (y >= 0) { seen[y] = 1; q[t++] = y; istree[i] = 1; } } }
    if (t != 2 * k) { printf("base disconnected\n"); return 7; }
    /* NB-4 walks: from A source i: e1 at a_i, e2 at b(e1) != e1, e3 at a(e2) != e2, e4 at b(e3) != e3, end a(e4) */
    for (int i = 0; i < k; i++) { nwA[i] = 0;
        for (int e1 = 0; e1 < ne; e1++) if (EA[e1] == i)
        for (int e2 = 0; e2 < ne; e2++) if (EB[e2] == EB[e1])
        for (int e3 = 0; e3 < ne; e3++) if (EA[e3] == EA[e2])
        for (int e4 = 0; e4 < ne; e4++) if (EB[e4] == EB[e3]) {
            int w = nwA[i]++; wA[i][w][0] = e1; wA[i][w][1] = e2; wA[i][w][2] = e3; wA[i][w][3] = e4; endA[i][w] = EA[e4]; } }
    for (int j = 0; j < k; j++) { nwB[j] = 0;
        for (int e1 = 0; e1 < ne; e1++) if (EB[e1] == j)
        for (int e2 = 0; e2 < ne; e2++) if (EA[e2] == EA[e1])
        for (int e3 = 0; e3 < ne; e3++) if (EB[e3] == EB[e2])
        for (int e4 = 0; e4 < ne; e4++) if (EA[e4] == EA[e3]) {
            int w = nwB[j]++; wB[j][w][0] = e1; wB[j][w][1] = e2; wB[j][w][2] = e3; wB[j][w][3] = e4; endB[j][w] = EB[e4]; } }
    /* random start */
    do { for (int i = 0; i < ne; i++) volt[i] = istree[i] ? e_id : (int)(xr() % n); } while (!parallel_ok());
    int c = cost(), best = c, bv[64]; memcpy(bv, volt, sizeof volt);
    clock_t t0 = clock(); long it = 0;
    int free_e[64], nf = 0; for (int i = 0; i < ne; i++) if (!istree[i]) free_e[nf++] = i;
    while (best > 0 && (double)(clock() - t0) / CLOCKS_PER_SEC < secs) {
        it++;
        double fr = (double)(clock() - t0) / CLOCKS_PER_SEC / secs; double TT = T0 * pow(0.02, fr);
        int ei = free_e[xr() % nf], old = volt[ei]; volt[ei] = xr() % n;
        if (!parallel_ok()) { volt[ei] = old; continue; }
        int c2 = cost();
        if (c2 <= c || exp((c - c2) / TT) > (double)(xr() % 1000000) / 1e6) { c = c2; if (c < best) { best = c; memcpy(bv, volt, sizeof volt); } }
        else volt[ei] = old;
        if (it % 200000 == 0 && c > best + 20) { memcpy(volt, bv, sizeof volt); c = best; } /* restart from best */
    }
    memcpy(volt, bv, sizeof volt); { int c4 = has4cycle(); printf("k=%d n=%d m=%d best_cost=%d (4cycle-missing %d, coverage %d) iters=%ld volt=", k, n, k * n, best, c4, best - 4 * c4, it); }
    for (int i = 0; i < ne; i++) printf("%d%c", bv[i], i + 1 < ne ? ',' : '\n');
    if (out && best == 0) { FILE *g = fopen(out, "w");
        for (int i = 0; i < ne; i++) for (int x = 0; x < n; x++) fprintf(g, "%d %d\n", EA[i] * n + x, EB[i] * n + mul(bv[i], x));
        fclose(g); }
    return 0;
}
