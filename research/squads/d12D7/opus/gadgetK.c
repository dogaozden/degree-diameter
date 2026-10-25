/* gadgetK.c (job cell-12-7): polygon cover H(q) x Z_5 (shifts 1, 2) with K gadgets.
 * Hop-less points X_1..X_K (same point in every copy): their 2K*5 hop edges are deleted. Image lines L_{t,k} = s_t(X_k).
 * New vertices per gadget: B_{k,1}, B_{k,2} (line side) joined to (X_k, c) for all c; A_{k,t} (point side) joined to
 * (L_{t,k}, c) for all c. Among the 4K new vertices, a bipartite graph H (each new vertex gets up to HDEG more edges,
 * line-side new ~ point-side new) keeps new vertices of different gadgets close. Order 10P + 4K, max degree q+3.
 * Only pairs with an endpoint in {X_k, L_{t,k}} (any copy) or a new vertex can lose the cover theorem's route; the
 * matchings are repaired so that, for each k and t (sources of hops exclude hop-less points):
 *   F1(t,k): every point outside Ball_4(X_k) is within distance 3 of s_t(x), x at distance 2 from X_k, or on s_t(x), x at
 *            distance 4 (route X_k -> x -> hop -> v, length <= 6);
 *   F2(t,k): every line outside Ball_4(L_{t,k}) is within distance 3 of s_t^-1(m), m at distance 2 from L_{t,k}, or passes
 *            through s_t^-1(m), m at distance 4 (route L -> m -> back-hop -> y).
 * Then BFS from the special vertices of copy 0 and all new vertices (Z_5 symmetry), optional edge list.
 * usage: gadgetK BASE K seed iters [EDGES_OUT]       env: HDEG (default 7), TEMP (default 0) */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>
#include <math.h>

static int P, Q1, K, NB3;
static int *lines, *thru, *b3line, *b3pt;
static uint64_t rs;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static double urand(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

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
static int *Xs, *isX;               /* hop-less points; isX[p] = 1 + index or 0 */
static int *Lt[3];                  /* Lt[t][k] = s_t(X_k) */
static int8_t **dXk, **dLk[3];      /* incidence distances */
/* membership: for each point x, list of F1 terms (k, type); for each line m, per t, list of F2 terms (k, type) */
typedef struct { int k; int8_t type; } memb;
static memb **mp; static int *nmp;               /* points */
static memb **ml[3]; static int *nml[3];         /* lines, per t */
static uint16_t **covF1[3], **covF2[3];
static long *uncF1[3], *uncF2[3];
static long total;

static inline void f1_contrib(int t, int k, int type, int L, int s) {
    uint16_t *c = covF1[t][k]; int8_t *d = dXk[k];
    if (type == 2) { int *lst = b3line + (size_t)L * NB3;
        for (int j = 0; j < NB3; j++) { int v = lst[j]; if (s > 0) { if (c[v]++ == 0 && d[v] > 4) { uncF1[t][k]--; total--; } } else { if (--c[v] == 0 && d[v] > 4) { uncF1[t][k]++; total++; } } } }
    else { for (int j = 0; j < Q1; j++) { int v = lines[L * Q1 + j]; if (s > 0) { if (c[v]++ == 0 && d[v] > 4) { uncF1[t][k]--; total--; } } else { if (--c[v] == 0 && d[v] > 4) { uncF1[t][k]++; total++; } } } }
}
static inline void f2_contrib(int t, int k, int type, int p, int s) {
    uint16_t *c = covF2[t][k]; int8_t *d = dLk[t][k];
    if (type == 2) { int *lst = b3pt + (size_t)p * NB3;
        for (int j = 0; j < NB3; j++) { int y = lst[j]; if (s > 0) { if (c[y]++ == 0 && d[P + y] > 4) { uncF2[t][k]--; total--; } } else { if (--c[y] == 0 && d[P + y] > 4) { uncF2[t][k]++; total++; } } } }
    else { for (int j = 0; j < Q1; j++) { int y = thru[p * Q1 + j]; if (s > 0) { if (c[y]++ == 0 && d[P + y] > 4) { uncF2[t][k]--; total--; } } else { if (--c[y] == 0 && d[P + y] > 4) { uncF2[t][k]++; total++; } } } }
}
/* move point a's image under s_t from line la to line lb (only contributions, not the arrays) */
static void retarget(int t, int a, int la, int lb) {
    for (int i = 0; i < nmp[a]; i++) { memb m = mp[a][i]; f1_contrib(t, m.k, m.type, la, -1); f1_contrib(t, m.k, m.type, lb, +1); }
}
static void repreimage(int t, int L, int pa, int pb) {   /* line L's s_t-preimage changes from pa to pb */
    for (int i = 0; i < nml[t][L]; i++) { memb m = ml[t][L][i]; f2_contrib(t, m.k, m.type, pa, -1); f2_contrib(t, m.k, m.type, pb, +1); }
}
static void do_swap(int t, int a, int b) {     /* exchange s_t(a) and s_t(b); a, b not hop-less */
    int la = sig[t][a], lb = sig[t][b];
    retarget(t, a, la, lb); retarget(t, b, lb, la);
    repreimage(t, la, a, b); repreimage(t, lb, b, a);
    sig[t][a] = lb; sig[t][b] = la; sinv[t][lb] = a; sinv[t][la] = b;
}

int main(int argc, char **argv) {
    if (argc < 5) { fprintf(stderr, "usage: gadgetK BASE K seed iters [EDGES_OUT]\n"); return 1; }
    FILE *f = fopen(argv[1], "r"); if (!f) { perror("base"); return 1; }
    K = atoi(argv[2]);
    rs = 0x2545F4914F6CDD1DULL ^ (uint64_t)atoll(argv[3]) * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 10; i++) rnd();
    long iters = atol(argv[4]);
    int HDEG = getenv("HDEG") ? atoi(getenv("HDEG")) : 7;
    double TEMP = getenv("TEMP") ? atof(getenv("TEMP")) : 0.0;
    if (fscanf(f, "%d", &P) != 1) return 2;
    char buf[4096]; fgets(buf, sizeof buf, f);
    for (int k = 0; k < P; k++) {
        if (!fgets(buf, sizeof buf, f)) return 2;
        int vals[64], c = 0; char *s = buf, *e;
        for (;;) { long v = strtol(s, &e, 10); if (e == s) break; vals[c++] = (int)v; s = e; }
        if (k == 0) { Q1 = c; lines = malloc((size_t)P * Q1 * sizeof(int)); }
        memcpy(lines + (size_t)k * Q1, vals, Q1 * sizeof(int));
    }
    fclose(f);
    thru = malloc((size_t)P * Q1 * sizeof(int)); int *tc = calloc(P, sizeof(int));
    for (int k = 0; k < P; k++) for (int i = 0; i < Q1; i++) { int p = lines[k * Q1 + i]; thru[p * Q1 + tc[p]++] = k; }
    int8_t *d = malloc(2 * P); int *qq = malloc(2 * P * sizeof(int));
    NB3 = Q1 + Q1 * (Q1 - 1) * (Q1 - 1);
    b3line = malloc((size_t)P * NB3 * sizeof(int)); b3pt = malloc((size_t)P * NB3 * sizeof(int));
    for (int k = 0; k < P; k++) { bfs_inc(P + k, d, 3, qq); int c = 0; for (int v = 0; v < P; v++) if (d[v] >= 0) b3line[(size_t)k * NB3 + c++] = v; if (c != NB3) return 3; }
    for (int p = 0; p < P; p++) { bfs_inc(p, d, 3, qq); int c = 0; for (int y = 0; y < P; y++) if (d[P + y] >= 0) b3pt[(size_t)p * NB3 + c++] = y; if (c != NB3) return 3; }
    for (int t = 1; t <= 2; t++) {
        sig[t] = malloc(P * sizeof(int)); sinv[t] = malloc(P * sizeof(int));
        for (int i = 0; i < P; i++) sig[t][i] = i;
        for (int i = P - 1; i > 0; i--) { int r = rnd() % (i + 1); int x = sig[t][i]; sig[t][i] = sig[t][r]; sig[t][r] = x; }
        for (int i = 0; i < P; i++) sinv[t][sig[t][i]] = i;
    }
    /* hop-less points: random, pairwise not collinear (distance >= 4) */
    Xs = malloc(K * sizeof(int)); isX = calloc(P, sizeof(int));
    for (int k = 0; k < K; k++) {
        for (;;) {
            int x = rnd() % P; if (isX[x]) continue;
            int ok = 1; bfs_inc(x, d, 2, qq);
            for (int j = 0; j < k; j++) if (d[Xs[j]] >= 0) { ok = 0; break; }
            if (ok) { Xs[k] = x; isX[x] = 1 + k; break; }
        }
    }
    for (int t = 1; t <= 2; t++) { Lt[t] = malloc(K * sizeof(int)); for (int k = 0; k < K; k++) Lt[t][k] = sig[t][Xs[k]]; }
    dXk = malloc(K * sizeof(int8_t *)); for (int t = 1; t <= 2; t++) dLk[t] = malloc(K * sizeof(int8_t *));
    for (int k = 0; k < K; k++) {
        dXk[k] = malloc(2 * P); bfs_inc(Xs[k], dXk[k], 100, qq);
        for (int t = 1; t <= 2; t++) { dLk[t][k] = malloc(2 * P); bfs_inc(P + Lt[t][k], dLk[t][k], 100, qq); }
    }
    /* memberships */
    nmp = calloc(P, sizeof(int)); mp = malloc(P * sizeof(memb *));
    for (int x = 0; x < P; x++) { int c = 0; if (!isX[x]) for (int k = 0; k < K; k++) if (dXk[k][x] == 2 || dXk[k][x] == 4) c++;
        mp[x] = malloc((c + 1) * sizeof(memb)); nmp[x] = 0;
        if (!isX[x]) for (int k = 0; k < K; k++) if (dXk[k][x] == 2 || dXk[k][x] == 4) { mp[x][nmp[x]].k = k; mp[x][nmp[x]].type = dXk[k][x]; nmp[x]++; } }
    for (int t = 1; t <= 2; t++) {
        nml[t] = calloc(P, sizeof(int)); ml[t] = malloc(P * sizeof(memb *));
        for (int m = 0; m < P; m++) { int hopless_pre = isX[sinv[t][m]] != 0; int c = 0;
            if (!hopless_pre) for (int k = 0; k < K; k++) { int dd = dLk[t][k][P + m]; if (dd == 2 || dd == 4) c++; }
            ml[t][m] = malloc((c + 1) * sizeof(memb)); nml[t][m] = 0;
            if (!hopless_pre) for (int k = 0; k < K; k++) { int dd = dLk[t][k][P + m]; if (dd == 2 || dd == 4) { ml[t][m][nml[t][m]].k = k; ml[t][m][nml[t][m]].type = dd; nml[t][m]++; } } }
    }
    /* H among the new vertices, built first so its routes count as fixed coverage:
       line-side new b = 2k+i (joined to X_k), point-side new j = 2k+(t-1) (joined to L_{t,k}) */
    int nb = 2 * K; int *perm = malloc(nb * sizeof(int));
    int *hB = malloc((size_t)nb * 8 * sizeof(int)), *nhB = calloc(nb, sizeof(int));
    int *hA = malloc((size_t)nb * 8 * sizeof(int)), *nhA = calloc(nb, sizeof(int));
    for (int r = 0; r < HDEG && nb > 0; r++) {
        for (int i = 0; i < nb; i++) perm[i] = i;
        for (int i = nb - 1; i > 0; i--) { int j = rnd() % (i + 1); int x = perm[i]; perm[i] = perm[j]; perm[j] = x; }
        for (int i = 0; i < nb; i++) {
            int j = perm[i]; int dup = 0;
            for (int e = 0; e < nhB[i]; e++) if (hB[i * 8 + e] == j) dup = 1;
            if (!dup && nhB[i] < 7 && nhA[j] < 7) { hB[i * 8 + nhB[i]++] = j; hA[j * 8 + nhA[j]++] = i; }
        }
    }
    /* coverage init */
    total = 0;
    for (int t = 1; t <= 2; t++) {
        covF1[t] = malloc(K * sizeof(uint16_t *)); covF2[t] = malloc(K * sizeof(uint16_t *));
        uncF1[t] = calloc(K, sizeof(long)); uncF2[t] = calloc(K, sizeof(long));
        for (int k = 0; k < K; k++) {
            covF1[t][k] = calloc(P, sizeof(uint16_t)); covF2[t][k] = calloc(P, sizeof(uint16_t));
            for (int v = 0; v < P; v++) if (dXk[k][v] > 4) { uncF1[t][k]++; total++; }
            for (int y = 0; y < P; y++) if (dLk[t][k][P + y] > 4) { uncF2[t][k]++; total++; }
        }
        for (int x = 0; x < P; x++) for (int i = 0; i < nmp[x]; i++) f1_contrib(t, mp[x][i].k, mp[x][i].type, sig[t][x], +1);
        for (int m = 0; m < P; m++) for (int i = 0; i < nml[t][m]; i++) f2_contrib(t, ml[t][m][i].k, ml[t][m][i].type, sinv[t][m], +1);
    }
    /* fixed coverage through H: X_k -> b -> j -> L_{t_j,k_j} -> 3 hexagon steps; L_{t,k} -> j -> b -> X_{k_b} -> 3 steps */
    for (int t = 1; t <= 2; t++) for (int k = 0; k < K; k++) {
        for (int i = 2 * k; i <= 2 * k + 1; i++) for (int e = 0; e < nhB[i]; e++) { int j = hB[i * 8 + e]; f1_contrib(t, k, 2, Lt[1 + j % 2][j / 2], +1); }
        int j0 = 2 * k + (t - 1);
        for (int e = 0; e < nhA[j0]; e++) { int b = hA[j0 * 8 + e]; f2_contrib(t, k, 2, Xs[b / 2], +1); }
    }
    printf("H: P=%d deg=%d K=%d HDEG=%d; initial uncovered (all F1, F2 terms) %ld\n", P, Q1, K, HDEG, total); fflush(stdout);
    /* repair */
    time_t t0 = time(NULL); long acc = 0;
    int *S4buf = malloc(P * sizeof(int));
    int BEST = getenv("BEST") ? atoi(getenv("BEST")) : 1;
    /* terms with uncovered targets are picked from a list refreshed now and then */
    int *tl_t = malloc(4 * K * sizeof(int)), *tl_k = malloc(4 * K * sizeof(int)), *tl_f = malloc(4 * K * sizeof(int)); int ntl = 0;
    for (long it = 0; it < iters && total > 0; it++) {
        if (it % 1000 == 0 || ntl == 0) {
            ntl = 0;
            for (int t2 = 1; t2 <= 2; t2++) for (int k2 = 0; k2 < K; k2++) {
                if (uncF1[t2][k2] > 0) { tl_t[ntl] = t2; tl_k[ntl] = k2; tl_f[ntl] = 1; ntl++; }
                if (uncF2[t2][k2] > 0) { tl_t[ntl] = t2; tl_k[ntl] = k2; tl_f[ntl] = 2; ntl++; }
            }
            if (ntl == 0) break;
        }
        int pick = rnd() % ntl; int t = tl_t[pick], k = tl_k[pick], fam = tl_f[pick];
        if ((fam == 1 && uncF1[t][k] == 0) || (fam == 2 && uncF2[t][k] == 0)) { ntl = 0; continue; }
        int bestA = -1, bestB = -1; long bestDelta = 1L << 40;
        if (fam == 1) {
            /* an uncovered point of F1(t,k) */
            int v = -1; for (int tries = 0; tries < 200; tries++) { int z = rnd() % P; if (dXk[k][z] > 4 && covF1[t][k][z] == 0) { v = z; break; } }
            if (v < 0) { for (int z = 0; z < P; z++) if (dXk[k][z] > 4 && covF1[t][k][z] == 0) { v = z; break; } }
            for (int r = 0; r < BEST; r++) {
                int L = thru[v * Q1 + rnd() % Q1];
                int x; for (;;) { x = rnd() % P; if (dXk[k][x] == 4 && !isX[x]) break; }
                int a = x, b = sinv[t][L];
                if (a == b || isX[a] || isX[b]) continue;
                long before = total; do_swap(t, a, b); long delta = total - before; do_swap(t, a, b);
                if (delta < bestDelta) { bestDelta = delta; bestA = a; bestB = b; }
            }
        } else {
            int y = -1; for (int tries = 0; tries < 200; tries++) { int z = rnd() % P; if (dLk[t][k][P + z] > 4 && covF2[t][k][z] == 0) { y = z; break; } }
            if (y < 0) { for (int z = 0; z < P; z++) if (dLk[t][k][P + z] > 4 && covF2[t][k][z] == 0) { y = z; break; } }
            for (int r = 0; r < BEST; r++) {
                int m; for (;;) { m = rnd() % P; if (dLk[t][k][P + m] == 4 && !isX[sinv[t][m]]) break; }
                int pnt = lines[y * Q1 + rnd() % Q1];
                int a = pnt, b = sinv[t][m];
                if (a == b || isX[a] || isX[b]) continue;
                long before = total; do_swap(t, a, b); long delta = total - before; do_swap(t, a, b);
                if (delta < bestDelta) { bestDelta = delta; bestA = a; bestB = b; }
            }
        }
        if (bestA < 0) continue;
        long delta = bestDelta;
        if (delta <= 0 || (TEMP > 0 && urand() < exp(-delta / TEMP))) { do_swap(t, bestA, bestB); acc++; }
        if (it % 20000 == 0) { printf("it %ld t=%lds uncovered %ld acc %ld\n", it, (long)(time(NULL) - t0), total, acc); fflush(stdout); }
    }
    printf("repair done: uncovered %ld after %lds\n", total, (long)(time(NULL) - t0)); fflush(stdout);
    for (int t = 1; t <= 2; t++) for (int k = 0; k < K; k++) if (Lt[t][k] != sig[t][Xs[k]]) { fprintf(stderr, "image moved\n"); return 4; }
    /* build the graph */
    const int M = 5; long N0 = 2L * P * M; long N = N0 + 4L * K;
    int maxdeg = Q1 + 2;
    int *deg = calloc(N, sizeof(int)); int *adj = malloc((size_t)N * maxdeg * sizeof(int));
    int over = 0;
    #define ADD(u, w) do { if (deg[u] >= maxdeg || deg[w] >= maxdeg) over = 1; else { adj[(size_t)(u) * maxdeg + deg[u]++] = (w); adj[(size_t)(w) * maxdeg + deg[w]++] = (u); } } while (0)
    for (int k = 0; k < P; k++) for (int i = 0; i < Q1; i++) { int p = lines[k * Q1 + i]; for (int c = 0; c < M; c++) ADD(p * M + c, (P + k) * M + c); }
    for (int t = 1; t <= 2; t++) for (int p = 0; p < P; p++) { if (isX[p]) continue; for (int c = 0; c < M; c++) ADD(p * M + c, (P + sig[t][p]) * M + (c + t) % M); }
    /* new vertices: line side Bn[k][i] = N0 + 4k + i (i = 0,1); point side An[k][t-1] = N0 + 4k + 1 + t */
    for (int k = 0; k < K; k++) for (int c = 0; c < M; c++) {
        ADD(Xs[k] * M + c, N0 + 4L * k + 0); ADD(Xs[k] * M + c, N0 + 4L * k + 1);
        ADD((P + Lt[1][k]) * M + c, N0 + 4L * k + 2); ADD((P + Lt[2][k]) * M + c, N0 + 4L * k + 3);
    }
    for (int i = 0; i < nb; i++) for (int e = 0; e < nhB[i]; e++) {
        int j = hB[i * 8 + e];
        long u = N0 + 4L * (i / 2) + (i % 2);           /* line-side new i */
        long w = N0 + 4L * (j / 2) + 2 + (j % 2);       /* point-side new j */
        ADD(u, w);
    }
    if (over) { fprintf(stderr, "degree overflow\n"); return 5; }
    int dmax = 0; for (long v = 0; v < N; v++) if (deg[v] > dmax) dmax = deg[v];
    printf("graph: N=%ld (table 664300 at q=9) max degree %d\n", N, dmax); fflush(stdout);
    /* BFS from special vertices of copy 0 and from all new vertices */
    int8_t *dist = malloc(N); int *q = malloc(N * sizeof(int));
    long nsrc = 3L * K + 4L * K; long *src = malloc(nsrc * sizeof(long)); long ns = 0;
    for (int k = 0; k < K; k++) { src[ns++] = (long)Xs[k] * M; src[ns++] = (long)(P + Lt[1][k]) * M; src[ns++] = (long)(P + Lt[2][k]) * M; }
    for (long v = N0; v < N; v++) src[ns++] = v;
    long badtot = 0; int eccmax = 0; long badsrc = 0;
    for (long si = 0; si < ns; si++) {
        memset(dist, -1, N); int h = 0, tl = 0; dist[src[si]] = 0; q[tl++] = (int)src[si]; int ecc = 0;
        while (h < tl) { int u = q[h++]; if (dist[u] > ecc) ecc = dist[u];
            for (int i = 0; i < deg[u]; i++) { int w = adj[(size_t)u * maxdeg + i]; if (dist[w] < 0) { dist[w] = dist[u] + 1; q[tl++] = w; } } }
        long bad = (long)N - tl; for (long v = 0; v < N; v++) if (dist[v] > 7) bad++;
        if (bad) { badsrc++; if (badsrc <= 10) printf("  source %ld bad %ld ecc %d\n", src[si], bad, ecc); }
        badtot += bad; if (ecc > eccmax) eccmax = ecc;
    }
    printf("RESULT K %d N %ld sources %ld (special of copy 0 + new) max ecc %d bad pairs %ld bad sources %ld\n", K, N, ns, eccmax, badtot, badsrc);
    fflush(stdout);
    if (argc > 5 && badtot == 0) {
        FILE *o = fopen(argv[5], "w"); fprintf(o, "%ld\n", N);
        for (long u = 0; u < N; u++) for (int i = 0; i < deg[u]; i++) { int w = adj[(size_t)u * maxdeg + i]; if (w > u) fprintf(o, "%ld %d\n", u, w); }
        fclose(o);
        char nm[1024]; snprintf(nm, sizeof nm, "%s.match", argv[5]); FILE *mm = fopen(nm, "w");
        fprintf(mm, "# gadgetK base %s K %d seed %s HDEG %d ; hop-less points:", argv[1], K, argv[3], HDEG);
        for (int k = 0; k < K; k++) fprintf(mm, " %d", Xs[k]);
        fprintf(mm, " ; then 'p s1(p) s2(p)' per point\n");
        for (int p = 0; p < P; p++) fprintf(mm, "%d %d %d\n", p, sig[1][p], sig[2][p]);
        fclose(mm);
        printf("wrote %s\n", argv[5]);
    }
    return 0;
}
