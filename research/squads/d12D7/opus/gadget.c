/* gadget.c (job cell-12-7): polygon cover of H(q) over Z_5 (shifts 1, 2) plus a "gadget" of 4 new vertices.
 *
 * Base: H(q) incidence graph (points 0..P-1, lines 0..P-1), matchings s1, s2 : points -> lines (bijections).
 * Cover: point (p,c) ~ line (L,c) for p on L;  point (p,c) ~ line (s_t(p), c+t), t = 1, 2.   [degree q+3]
 * Gadget at a point X (the same point in every copy): delete the edges (X,c)-(s_t(X), c+t) for all c, t (10 edges),
 * add new vertices W1, W2 (line side) adjacent to (X,c) for all c, and W1', W2' (point side) with W_t' adjacent to
 * (s_t(X), c) for all c. Degrees stay <= q+3. Order 2P*5 + 4.
 * Why only few pairs can break: the cover theorem's routes hop at an endpoint (or at one of the q+1 neighbours of a
 * line endpoint), so only pairs with an endpoint in {(X,c), (s1(X),c), (s2(X),c)} lose their theorem route.
 * The search makes those endpoints reach everything:
 *   F1(t): every point v outside Ball_4(X) is within distance 3 of s_t(x) for some x at distance 2 from X, or lies on
 *          s_t(x) for some x at distance 4 from X   (route X -> x -> hop -> v, length <= 6);
 *   F2(t): every line y outside Ball_4(L_t), L_t = s_t(X), is within distance 3 of s_t^-1(m) for a line m at
 *          distance 2 from L_t, or passes through s_t^-1(m) for m at distance 4 (route L_t -> m -> back-hop -> y).
 * Then it builds the graph and BFSes from all 15 special vertices and the 4 gadget vertices (exact check of every
 * pair that can have changed), optionally writes the edge list for apsp.
 * usage: gadget BASE seed iters [EDGES_OUT]        (D = 7, M = 5, shifts 1 2 fixed) */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

static int P, Q1;
static int *lines, *thru;          /* lines[k*Q1+i] = points on line k; thru[p*Q1+i] = lines through p */
static uint64_t rs;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }

/* BFS in the incidence graph: vertex v < P point, v >= P line (v-P) */
static void bfs_inc(int src, int8_t *d, int maxd, int *q) {
    memset(d, -1, 2 * P);
    int h = 0, t = 0; d[src] = 0; q[t++] = src;
    while (h < t) {
        int u = q[h++]; if (d[u] == maxd) continue;
        if (u < P) { for (int i = 0; i < Q1; i++) { int w = P + thru[u * Q1 + i]; if (d[w] < 0) { d[w] = d[u] + 1; q[t++] = w; } } }
        else { int k = u - P; for (int i = 0; i < Q1; i++) { int w = lines[k * Q1 + i]; if (d[w] < 0) { d[w] = d[u] + 1; q[t++] = w; } } }
    }
}

static int *sig[3], *sinv[3];
static int X, Lt[3];
static int8_t *dX, *dL[3];        /* incidence distances from X and from L_t (as line vertex) */
static int *S2X, nS2X, *S4X, nS4X, *S2L[3], nS2L[3], *S4L[3], nS4L[3];
/* ball3 of a line: points within distance 3 of line k (incidence distance 1 or 3); of a point: lines within 3 */
static int *b3line, *b3lineN, *b3pt, *b3ptN;   /* precomputed lists, (q+1)+(q+1)q^2 entries each */

static int *cov; /* scratch counts */

static long costF1(int t, int *unc) {      /* number of uncovered points (outside Ball_4(X)) */
    memset(cov, 0, P * sizeof(int));
    for (int i = 0; i < nS2X; i++) { int L = sig[t][S2X[i]]; int *lst = b3line + (size_t)L * b3lineN[0]; for (int j = 0; j < b3lineN[0]; j++) cov[lst[j]]++; }
    for (int i = 0; i < nS4X; i++) { int L = sig[t][S4X[i]]; for (int j = 0; j < Q1; j++) cov[lines[L * Q1 + j]]++; }
    long u = 0;
    for (int v = 0; v < P; v++) if (dX[v] > 4 && cov[v] == 0) { if (unc) unc[u] = v; u++; }
    return u;
}
static long costF2(int t, int *unc) {      /* number of uncovered lines (outside Ball_4(L_t)) */
    memset(cov, 0, P * sizeof(int));
    for (int i = 0; i < nS2L[t]; i++) { int p = sinv[t][S2L[t][i]]; int *lst = b3pt + (size_t)p * b3ptN[0]; for (int j = 0; j < b3ptN[0]; j++) cov[lst[j]]++; }
    for (int i = 0; i < nS4L[t]; i++) { int p = sinv[t][S4L[t][i]]; for (int j = 0; j < Q1; j++) cov[thru[p * Q1 + j]]++; }
    long u = 0;
    for (int y = 0; y < P; y++) if (dL[t][P + y] > 4 && cov[y] == 0) { if (unc) unc[u] = y; u++; }
    return u;
}
static void swap_sig(int t, int a, int b) {
    int la = sig[t][a], lb = sig[t][b]; sig[t][a] = lb; sig[t][b] = la; sinv[t][lb] = a; sinv[t][la] = b;
}

int main(int argc, char **argv) {
    if (argc < 4) { fprintf(stderr, "usage: gadget BASE seed iters [EDGES_OUT]\n"); return 1; }
    FILE *f = fopen(argv[1], "r"); if (!f) { perror("base"); return 1; }
    rs = 0x2545F4914F6CDD1DULL ^ (uint64_t)atoll(argv[2]) * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 10; i++) rnd();
    long iters = atol(argv[3]);
    if (fscanf(f, "%d", &P) != 1) return 2;
    char buf[4096]; fgets(buf, sizeof buf, f);
    for (int k = 0; k < P; k++) {
        if (!fgets(buf, sizeof buf, f)) return 2;
        int vals[64], c = 0; char *s = buf, *e;
        for (;;) { long v = strtol(s, &e, 10); if (e == s) break; vals[c++] = (int)v; s = e; }
        if (k == 0) { Q1 = c; lines = malloc((size_t)P * Q1 * sizeof(int)); }
        memcpy(lines + (size_t)k * Q1, vals, Q1 * sizeof(int));
    }
    thru = malloc((size_t)P * Q1 * sizeof(int)); int *tc = calloc(P, sizeof(int));
    for (int k = 0; k < P; k++) for (int i = 0; i < Q1; i++) { int p = lines[k * Q1 + i]; thru[p * Q1 + tc[p]++] = k; }
    int8_t *d = malloc(2 * P); int *qq = malloc(2 * P * sizeof(int));
    /* balls of radius 3 */
    int nb3 = Q1 + Q1 * (Q1 - 1) * (Q1 - 1);
    b3line = malloc((size_t)P * nb3 * sizeof(int)); b3pt = malloc((size_t)P * nb3 * sizeof(int));
    b3lineN = malloc(sizeof(int)); b3ptN = malloc(sizeof(int)); b3lineN[0] = nb3; b3ptN[0] = nb3;
    for (int k = 0; k < P; k++) {
        bfs_inc(P + k, d, 3, qq); int c = 0;
        for (int v = 0; v < P; v++) if (d[v] >= 0 && d[v] <= 3) b3line[(size_t)k * nb3 + c++] = v;
        if (c != nb3) { fprintf(stderr, "ball3(line) size %d != %d\n", c, nb3); return 3; }
    }
    for (int p = 0; p < P; p++) {
        bfs_inc(p, d, 3, qq); int c = 0;
        for (int y = 0; y < P; y++) if (d[P + y] >= 0 && d[P + y] <= 3) b3pt[(size_t)p * nb3 + c++] = y;
        if (c != nb3) { fprintf(stderr, "ball3(point) size %d != %d\n", c, nb3); return 3; }
    }
    for (int t = 1; t <= 2; t++) {
        sig[t] = malloc(P * sizeof(int)); sinv[t] = malloc(P * sizeof(int));
        for (int i = 0; i < P; i++) sig[t][i] = i;
        for (int i = P - 1; i > 0; i--) { int r = rnd() % (i + 1); int x = sig[t][i]; sig[t][i] = sig[t][r]; sig[t][r] = x; }
        for (int i = 0; i < P; i++) sinv[t][sig[t][i]] = i;
    }
    X = 0;
    dX = malloc(2 * P); bfs_inc(X, dX, 100, qq);
    /* make d(L1, L2) = 2: move s2(X) to a line meeting s1(X) */
    Lt[1] = sig[1][X];
    { int8_t *dd = malloc(2 * P); bfs_inc(P + Lt[1], dd, 100, qq);
      int target = -1; for (int y = 0; y < P; y++) if (dd[P + y] == 2) { target = y; break; }
      swap_sig(2, X, sinv[2][target]); free(dd); }
    Lt[2] = sig[2][X];
    for (int t = 1; t <= 2; t++) { dL[t] = malloc(2 * P); bfs_inc(P + Lt[t], dL[t], 100, qq); }
    S2X = malloc(P * sizeof(int)); S4X = malloc(P * sizeof(int)); nS2X = nS4X = 0;
    for (int v = 0; v < P; v++) { if (dX[v] == 2) S2X[nS2X++] = v; if (dX[v] == 4) S4X[nS4X++] = v; }
    for (int t = 1; t <= 2; t++) {
        S2L[t] = malloc(P * sizeof(int)); S4L[t] = malloc(P * sizeof(int)); nS2L[t] = nS4L[t] = 0;
        for (int y = 0; y < P; y++) { if (dL[t][P + y] == 2) S2L[t][nS2L[t]++] = y; if (dL[t][P + y] == 4) S4L[t][nS4L[t]++] = y; }
    }
    cov = malloc(P * sizeof(int)); int *unc = malloc(P * sizeof(int));
    printf("H: P=%d deg=%d |S2(X)|=%d |S4(X)|=%d |S2(L1)|=%d |S4(L1)|=%d  d(X,L1)=%d d(X,L2)=%d\n", P, Q1, nS2X, nS4X,
           nS2L[1], nS4L[1], dX[P + Lt[1]], dX[P + Lt[2]]);
    long c0 = 0; for (int t = 1; t <= 2; t++) c0 += costF1(t, NULL) + costF2(t, NULL);
    printf("initial cost (F1+F2 uncovered, both shifts) %ld\n", c0); fflush(stdout);
    /* repair: targeted swaps, accept if total cost does not increase */
    long cur = c0; time_t t0 = time(NULL);
    for (long it = 0; it < iters && cur > 0; it++) {
        int t = 1 + (rnd() & 1);
        long ct = costF1(t, unc);
        int a, b;
        if (ct > 0 && (rnd() & 1)) {           /* F1 fix: put a line through an uncovered point v onto some x in S4(X) */
            int v = unc[rnd() % ct];
            int L = thru[v * Q1 + rnd() % Q1];
            a = S4X[rnd() % nS4X]; b = sinv[t][L];
        } else {
            long c2 = costF2(t, unc);
            if (c2 == 0) { if (ct == 0) continue; int v = unc[0]; (void)v; continue; }
            int y = unc[rnd() % c2];           /* F2 fix: make s_t^-1(m) a point on uncovered line y, m in S4(L_t) */
            int m = S4L[t][rnd() % nS4L[t]];
            int pnt = lines[y * Q1 + rnd() % Q1];
            a = pnt; b = sinv[t][m];
        }
        if (a == X || b == X || a == b) continue;
        long before = costF1(t, NULL) + costF2(t, NULL);
        swap_sig(t, a, b);
        long after = costF1(t, NULL) + costF2(t, NULL);
        if (after > before) swap_sig(t, a, b);
        else cur += after - before;
        if (it % 2000 == 0) { long tot = 0; for (int s = 1; s <= 2; s++) tot += costF1(s, NULL) + costF2(s, NULL); cur = tot;
            printf("it %ld t=%lds cost %ld\n", it, (long)(time(NULL) - t0), cur); fflush(stdout); }
    }
    long tot = 0; for (int s = 1; s <= 2; s++) { long a1 = costF1(s, NULL), a2 = costF2(s, NULL); printf("final F1(%d)=%ld F2(%d)=%ld\n", s, a1, s, a2); tot += a1 + a2; }
    printf("repair cost %ld\n", tot); fflush(stdout);
    if (Lt[1] != sig[1][X] || Lt[2] != sig[2][X]) { fprintf(stderr, "X images moved\n"); return 4; }
    /* build the graph: (x,c) with x in 0..2P-1 (points, then lines P+k) -> x*5 + c; gadgets 10P + 0..3 */
    const int M = 5; long N = 2L * P * M + 4;
    int *deg = calloc(N, sizeof(int)); int maxdeg = Q1 + 2;
    int *adj = malloc((size_t)N * maxdeg * sizeof(int));
    #define ADD(u, w) do { adj[(size_t)(u) * maxdeg + deg[u]++] = (w); adj[(size_t)(w) * maxdeg + deg[w]++] = (u); } while (0)
    for (int k = 0; k < P; k++) for (int i = 0; i < Q1; i++) { int p = lines[k * Q1 + i]; for (int c = 0; c < M; c++) ADD(p * M + c, (P + k) * M + c); }
    for (int t = 1; t <= 2; t++) for (int p = 0; p < P; p++) { if (p == X) continue; for (int c = 0; c < M; c++) ADD(p * M + c, (P + sig[t][p]) * M + (c + t) % M); }
    long g = 2L * P * M;
    for (int c = 0; c < M; c++) { ADD(X * M + c, g + 0); ADD(X * M + c, g + 1); ADD((P + Lt[1]) * M + c, g + 2); ADD((P + Lt[2]) * M + c, g + 3); }
    int dmax = 0; for (long v = 0; v < N; v++) { if (deg[v] > dmax) dmax = deg[v]; if (deg[v] > maxdeg) { fprintf(stderr, "degree overflow\n"); return 5; } }
    printf("graph: N=%ld max degree %d\n", N, dmax); fflush(stdout);
    /* BFS from the special vertices and the gadgets */
    int8_t *dist = malloc(N); int *q = malloc(N * sizeof(int));
    long srcs[64]; int ns = 0;
    for (int c = 0; c < M; c++) { srcs[ns++] = X * M + c; srcs[ns++] = (P + Lt[1]) * M + c; srcs[ns++] = (P + Lt[2]) * M + c; }
    for (int i = 0; i < 4; i++) srcs[ns++] = g + i;
    long badtot = 0; int eccmax = 0;
    for (int si = 0; si < ns; si++) {
        memset(dist, -1, N); int h = 0, tl = 0; dist[srcs[si]] = 0; q[tl++] = (int)srcs[si]; int ecc = 0;
        while (h < tl) { int u = q[h++]; if (dist[u] > ecc) ecc = dist[u];
            for (int i = 0; i < deg[u]; i++) { int w = adj[(size_t)u * maxdeg + i]; if (dist[w] < 0) { dist[w] = dist[u] + 1; q[tl++] = w; } } }
        long bad = 0; for (long v = 0; v < N; v++) if (dist[v] < 0 || dist[v] > 7) bad++;
        if (tl != N) printf("  source %ld: only %d of %ld reached\n", srcs[si], tl, N);
        printf("  source %ld (%s): ecc %d, targets beyond 7: %ld\n", srcs[si], si < 15 ? (si % 3 == 0 ? "X" : si % 3 == 1 ? "L1" : "L2") : "gadget", ecc, bad);
        badtot += bad; if (ecc > eccmax) eccmax = ecc;
    }
    printf("RESULT special+gadget sources %d, max ecc %d, bad pairs %ld, N %ld\n", ns, eccmax, badtot, N);
    if (argc > 4) {
        FILE *o = fopen(argv[4], "w"); fprintf(o, "%ld\n", N);
        for (long u = 0; u < N; u++) for (int i = 0; i < deg[u]; i++) { int w = adj[(size_t)u * maxdeg + i]; if (w > u) fprintf(o, "%ld %d\n", u, w); }
        fclose(o); printf("wrote %s\n", argv[4]);
        /* also the matchings, so the graph can be rebuilt */
        char nm[1024]; snprintf(nm, sizeof nm, "%s.match", argv[4]); FILE *mm = fopen(nm, "w");
        fprintf(mm, "# gadget.c base %s seed %s X %d L1 %d L2 %d ; then 'p s1(p) s2(p)' per point\n", argv[1], argv[2], X, Lt[1], Lt[2]);
        for (int p = 0; p < P; p++) fprintf(mm, "%d %d %d\n", p, sig[1][p], sig[2][p]);
        fclose(mm);
    }
    return 0;
}
