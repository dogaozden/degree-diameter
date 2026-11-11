/* ctrl5.c: controllers for the Delta = 10 route-chart lift (5 letters x GF(2), fibre GF(2)^4; job cell-10-5).

   Base: 5-regular bipartite multigraph on k + k vertices (a_0..a_{k-1} | b_0..b_{k-1}), properly 5-edge-coloured here
   (Konig, by peeling perfect matchings in a seeded random order); the colour of a base edge, after the letter
   permutation PERM, is its chart letter.  Controller = voltage lift by a group G given by its table:
   (a_i, g) ~ (b_j, v_e g).  Right multiplication by G is an automorphism, so the k + k sources (a_i, 1), (b_j, 1)
   suffice.
   A same-side controller pair (u, w) is covered in the route-chart lift when
     - w = u (chart is diagonal-complete), or
     - w is the end of a walk of length 2 from u along two different controller edges (chart is pencil-complete), or
     - w is the end of a nonbacktracking walk of length 4 whose letter pattern is nonsingular (pattern table).
   Cost = uncovered (source, target) pairs over both sides.  Cost 0 => the lift has diameter <= 5 (check it!).

   usage: ctrl5 search BASE TABLE PATTERNS SECONDS SEED [OUT]
          ctrl5 sample BASE TABLE PATTERNS COUNT SEED          (cost quantiles of random voltage assignments)
   env:   PERM=01234 (letter of colour c is PERM[c]; PERM=rand picks one from SEED), T0 (default 2), CSEED (colouring
          seed, default SEED), WRITEBEST=1 (write OUT even when cost > 0)
   BASE: "k" then 5k lines "i j" (edge a_i -- b_j).  TABLE: "n" then n*n entries (row-major, T[x*n+y] = x*y).
   PATTERNS: 640 lines "S i1 i2 i3 i4 ok" from chart2 show.
   OUT: "ctrl5 k K n N cost C" then one line "i j voltage letter" per base edge.                                     */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <time.h>
#include <stdint.h>

static uint64_t rs = 88172645463325252ULL;
static inline uint64_t xr(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }

#define MAXK 32
#define MAXE (5 * MAXK)
static int k, ne, EA[MAXE], EB[MAXE], col[MAXE], let[MAXE], n, *T, *Inv, e_id, istree[MAXE], volt[MAXE];
static int nsA[5][5][5][5], nsB[5][5][5][5];
static int nwA[MAXK], nwB[MAXK], (*wA)[340][4], (*wB)[340][4], lenA[MAXK][340], lenB[MAXK][340], endA[MAXK][340], endB[MAXK][340];
static unsigned char *hit;
static inline int mul(int a, int b) { return T[a * n + b]; }

static int cost(void) {
    int c = 0;
    for (int i = 0; i < k; i++) {
        memset(hit, 0, k * n); hit[i * n + e_id] = 1;
        for (int w = 0; w < nwA[i]; w++) { int *E = wA[i][w], x;
            if (lenA[i][w] == 2) x = mul(Inv[volt[E[1]]], volt[E[0]]);
            else x = mul(Inv[volt[E[3]]], mul(volt[E[2]], mul(Inv[volt[E[1]]], volt[E[0]])));
            hit[endA[i][w] * n + x] = 1; }
        for (int t = 0; t < k * n; t++) c += !hit[t];
    }
    for (int j = 0; j < k; j++) {
        memset(hit, 0, k * n); hit[j * n + e_id] = 1;
        for (int w = 0; w < nwB[j]; w++) { int *E = wB[j][w], x;
            if (lenB[j][w] == 2) x = mul(volt[E[1]], Inv[volt[E[0]]]);
            else x = mul(volt[E[3]], mul(Inv[volt[E[2]]], mul(volt[E[1]], Inv[volt[E[0]]])));
            hit[endB[j][w] * n + x] = 1; }
        for (int t = 0; t < k * n; t++) c += !hit[t];
    }
    return c;
}
static int parallel_ok(void) {
    for (int a = 0; a < ne; a++) for (int b = a + 1; b < ne; b++) if (EA[a] == EA[b] && EB[a] == EB[b] && volt[a] == volt[b]) return 0;
    return 1;
}
/* proper 5-edge-colouring: peel perfect matchings by augmenting paths, vertices tried in a random order */
static int used[MAXE], matchB[MAXK], visB[MAXK], ordA[MAXK];
static int aug(int a) {
    int es[MAXE], m = 0; for (int e = 0; e < ne; e++) if (!used[e] && EA[e] == a) es[m++] = e;
    for (int i = m - 1; i > 0; i--) { int j = xr() % (i + 1), t = es[i]; es[i] = es[j]; es[j] = t; }
    for (int q = 0; q < m; q++) { int e = es[q]; if (visB[EB[e]]) continue; visB[EB[e]] = 1;
        if (matchB[EB[e]] < 0 || aug(EA[matchB[EB[e]]])) { matchB[EB[e]] = e; return 1; } }
    return 0;
}
static void colour(void) {
    memset(used, 0, sizeof used);
    for (int c = 0; c < 5; c++) {
        for (int j = 0; j < k; j++) matchB[j] = -1;
        for (int a = 0; a < k; a++) ordA[a] = a;
        for (int i = k - 1; i > 0; i--) { int j = xr() % (i + 1), t = ordA[i]; ordA[i] = ordA[j]; ordA[j] = t; }
        for (int q = 0; q < k; q++) { memset(visB, 0, sizeof visB); if (!aug(ordA[q])) { printf("colouring failed\n"); exit(9); } }
        for (int j = 0; j < k; j++) { col[matchB[j]] = c; used[matchB[j]] = 1; }
    }
}
static void build_walks(void) {
    wA = malloc(sizeof(*wA) * k); wB = malloc(sizeof(*wB) * k);
    for (int i = 0; i < k; i++) { nwA[i] = 0;
        for (int e1 = 0; e1 < ne; e1++) if (EA[e1] == i)
        for (int e2 = 0; e2 < ne; e2++) if (e2 != e1 && EB[e2] == EB[e1]) {
            { int w = nwA[i]++; wA[i][w][0] = e1; wA[i][w][1] = e2; lenA[i][w] = 2; endA[i][w] = EA[e2]; }
            for (int e3 = 0; e3 < ne; e3++) if (e3 != e2 && EA[e3] == EA[e2])
            for (int e4 = 0; e4 < ne; e4++) if (e4 != e3 && EB[e4] == EB[e3]) {
                if (!nsA[let[e1]][let[e2]][let[e3]][let[e4]]) continue;
                int w = nwA[i]++; wA[i][w][0] = e1; wA[i][w][1] = e2; wA[i][w][2] = e3; wA[i][w][3] = e4; lenA[i][w] = 4; endA[i][w] = EA[e4]; } } }
    for (int j = 0; j < k; j++) { nwB[j] = 0;
        for (int e1 = 0; e1 < ne; e1++) if (EB[e1] == j)
        for (int e2 = 0; e2 < ne; e2++) if (e2 != e1 && EA[e2] == EA[e1]) {
            { int w = nwB[j]++; wB[j][w][0] = e1; wB[j][w][1] = e2; lenB[j][w] = 2; endB[j][w] = EB[e2]; }
            for (int e3 = 0; e3 < ne; e3++) if (e3 != e2 && EB[e3] == EB[e2])
            for (int e4 = 0; e4 < ne; e4++) if (e4 != e3 && EA[e4] == EA[e3]) {
                if (!nsB[let[e1]][let[e2]][let[e3]][let[e4]]) continue;
                int w = nwB[j]++; wB[j][w][0] = e1; wB[j][w][1] = e2; wB[j][w][2] = e3; wB[j][w][3] = e4; lenB[j][w] = 4; endB[j][w] = EB[e4]; } } }
}
static void randomize(void) { do { for (int i = 0; i < ne; i++) volt[i] = istree[i] ? e_id : (int)(xr() % n); } while (!parallel_ok()); }

int main(int argc, char **argv) {
    if (argc < 7) { printf("usage: ctrl5 search|sample BASE TABLE PATTERNS SECONDS|COUNT SEED [OUT]\n"); return 1; }
    int mode_sample = !strcmp(argv[1], "sample");
    FILE *f = fopen(argv[2], "r"); if (!f || fscanf(f, "%d", &k) != 1 || k > MAXK) { printf("bad base\n"); return 2; }
    ne = 5 * k; for (int i = 0; i < ne; i++) if (fscanf(f, "%d %d", &EA[i], &EB[i]) != 2) { printf("bad base edge\n"); return 3; }
    fclose(f);
    f = fopen(argv[3], "r"); if (!f || fscanf(f, "%d", &n) != 1) { printf("bad table\n"); return 4; }
    T = malloc(sizeof(int) * n * n); Inv = malloc(sizeof(int) * n);
    for (int i = 0; i < n * n; i++) if (fscanf(f, "%d", &T[i]) != 1) { printf("bad table entry\n"); return 5; }
    fclose(f);
    e_id = -1; for (int i = 0; i < n && e_id < 0; i++) { int ok = 1; for (int j = 0; j < n; j++) if (T[i * n + j] != j) { ok = 0; break; } if (ok) e_id = i; }
    for (int i = 0; i < n; i++) { Inv[i] = -1; for (int j = 0; j < n; j++) if (T[i * n + j] == e_id) Inv[i] = j; if (Inv[i] < 0) { printf("not a group\n"); return 5; } }
    f = fopen(argv[4], "r"); char side[4]; int a1, a2, a3, a4, r, np = 0;
    while (f && fscanf(f, "%3s %d %d %d %d %d", side, &a1, &a2, &a3, &a4, &r) == 6) { np++; if (side[0] == 'A') nsA[a1][a2][a3][a4] = r; else nsB[a1][a2][a3][a4] = r; }
    if (f) fclose(f); if (np != 640) { printf("pattern file has %d lines\n", np); return 6; }
    uint64_t seed = (uint64_t)atoll(argv[6]);
    rs ^= (getenv("CSEED") ? (uint64_t)atoll(getenv("CSEED")) : seed) * 0x9E3779B97F4A7C15ULL + 12345; if (!rs) rs = 1;
    hit = malloc(k * n + 1);
    colour();
    int perm[5] = {0, 1, 2, 3, 4}; const char *P = getenv("PERM");
    if (P && !strcmp(P, "rand")) { for (int i = 4; i > 0; i--) { int j = xr() % (i + 1), t = perm[i]; perm[i] = perm[j]; perm[j] = t; } }
    else if (P && strlen(P) == 5) for (int c = 0; c < 5; c++) perm[c] = P[c] - '0';
    for (int e = 0; e < ne; e++) let[e] = perm[col[e]];
    rs ^= seed * 0xD1B54A32D192ED03ULL + 777; if (!rs) rs = 1;
    /* spanning tree for gauge fixing */
    int seen[2 * MAXK] = {0}, q[2 * MAXK], h = 0, t = 0; seen[0] = 1; q[t++] = 0;
    while (h < t) { int x = q[h++];
        for (int i = 0; i < ne; i++) { int a = EA[i], b = k + EB[i], y = -1;
            if (x == a && !seen[b]) y = b; else if (x == b && !seen[a]) y = a;
            if (y >= 0) { seen[y] = 1; q[t++] = y; istree[i] = 1; } } }
    if (t != 2 * k) { printf("base disconnected\n"); return 7; }
    build_walks();
    if (mode_sample) {
        int cnt = atoi(argv[5]); int *cs = malloc(sizeof(int) * cnt);
        for (int s = 0; s < cnt; s++) { randomize(); cs[s] = cost(); }
        for (int i = 1; i < cnt; i++) { int x = cs[i], j = i - 1; while (j >= 0 && cs[j] > x) { cs[j + 1] = cs[j]; j--; } cs[j + 1] = x; }
        printf("k=%d n=%d m=%d perm=%d%d%d%d%d sample min=%d p10=%d median=%d\n", k, n, k * n, perm[0], perm[1], perm[2], perm[3], perm[4], cs[0], cs[cnt / 10], cs[cnt / 2]);
        return 0;
    }
    double secs = atof(argv[5]); const char *out = argc > 7 ? argv[7] : NULL;
    double T0 = getenv("T0") ? atof(getenv("T0")) : 2.0;
    randomize();
    int c = cost(), best = c, bv[MAXE]; memcpy(bv, volt, sizeof volt);
    int free_e[MAXE], nf = 0; for (int i = 0; i < ne; i++) if (!istree[i]) free_e[nf++] = i;
    clock_t t0 = clock(); long it = 0, last_imp = 0;
    while (best > 0 && (double)(clock() - t0) / CLOCKS_PER_SEC < secs) {
        it++;
        double fr = (double)(clock() - t0) / CLOCKS_PER_SEC / secs, TT = T0 * pow(0.05, fr);
        int ei = free_e[xr() % nf], old = volt[ei]; volt[ei] = xr() % n;
        if (volt[ei] == old || !parallel_ok()) { volt[ei] = old; continue; }
        int c2 = cost();
        if (c2 <= c || exp((c - c2) / TT) > (double)(xr() % 1000000) / 1e6) { c = c2; if (c < best) { best = c; memcpy(bv, volt, sizeof volt); last_imp = it; } }
        else volt[ei] = old;
        if (it - last_imp > 300000 && c > best) { memcpy(volt, bv, sizeof volt); c = best; last_imp = it; }
    }
    printf("k=%d n=%d m=%d perm=%d%d%d%d%d best_cost=%d iters=%ld time=%.1f volt=", k, n, k * n, perm[0], perm[1], perm[2], perm[3], perm[4], best, it, (double)(clock() - t0) / CLOCKS_PER_SEC);
    for (int i = 0; i < ne; i++) printf("%d%c", bv[i], i + 1 < ne ? ',' : '\n');
    if (out && (best == 0 || getenv("WRITEBEST"))) { FILE *g = fopen(out, "w");
        fprintf(g, "ctrl5 k %d n %d cost %d\n", k, n, best);
        for (int i = 0; i < ne; i++) fprintf(g, "%d %d %d %d\n", EA[i], EB[i], bv[i], let[i]);
        fclose(g); }
    return 0;
}
