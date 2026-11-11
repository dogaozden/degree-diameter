/* thmd.c: Theorem D graph (POLISHED.md sections 6.1-6.5, Corollary 6.8) for an odd PRIME q, m = 2.
   Input: hex/hex_q{q}.bin written by hexgen2 (points 0..N-1, lines N..2N-1, incidence = line point lists).
   Construction, in the paper's coordinates (X0..X6 = the 7 coordinates of hexgen2):
     v = line through e1 and e6; c = least c>=1 with -c a non-square; Pi = {X0 + c X4 = 0};
     A2 = {v}; A1 = {v} u points(v) u S (S = lines of H(q) inside Pi); A0 = A1 u points(Pi) u L_v u W,
     L_v = lines != v meeting v; W = {l in S_z\{v}, z != 0 : nu(l cap Pi) = F(z)} (exact whisker set, Thm 6.5),
     nu(X) = (X2X3 - X4X5)/(cX2^2 + X5^2), F(z) = G(a,b)/(a^2+c b^2) at z=(a,b), G(a,b) = (c0 a + c1 b)(a^2+c b^2) - b^3,
     (c0,c1) = first pair with c0 != 0 such that G has no zero on F^2 minus 0 (Lemma 6.4).
   Level: lambda(v)=2, lambda = 1 on points(v) and S\{v}, lambda = 0 on A0 \ A1, lambda = -1 elsewhere.
   Doubling with m = 2 (Definition 1.1): an element of level k has 2^(k+1) versions, labelled by words of length k+1 over {0,1};
   versions x^w, y^u are adjacent iff x I y and w, u are comparable (one a prefix of the other).
   Output: the doubled bipartite graph (CSR), degree histogram, BFS sample check, optional edge list for apsp.
   Usage: thmd hex/hex_q{q}.bin NRAND SEED [edges_out.txt] */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

static int q;
static inline int md(int64_t x) { x %= q; if (x < 0) x += q; return (int)x; }

int main(int argc, char **argv) {
    if (argc < 4) { fprintf(stderr, "usage: thmd hex.bin NRAND SEED [edges_out]\n"); return 1; }
    FILE *f = fopen(argv[1], "rb"); if (!f) { perror("open"); return 1; }
    int32_t hdr[3]; if (fread(hdr, 4, 3, f) != 3) return 1;
    q = hdr[0]; int64_t N = hdr[1], L = hdr[2]; int Q1 = q + 1;
    if (N != L) return 1;
    int32_t *lines = malloc(sizeof(int32_t) * N * Q1);
    uint8_t *coord = malloc(N * 7);
    if (fread(lines, 4, N * Q1, f) != (size_t)(N * Q1) || fread(coord, 1, N * 7, f) != (size_t)(N * 7)) { fprintf(stderr, "short\n"); return 1; }
    fclose(f);
    int isprime = 1; for (int d = 2; d * d <= q; d++) if (q % d == 0) isprime = 0;
    if (!isprime) { fprintf(stderr, "this code is for prime q only\n"); return 1; }
    #define X(p, j) ((int)coord[(p) * 7 + (j)])

    /* point -> lines */
    int32_t *pl = malloc(sizeof(int32_t) * N * Q1); int *pc = calloc(N, sizeof(int));
    for (int64_t l = 0; l < N; l++) for (int s = 0; s < Q1; s++) { int64_t p = lines[l * Q1 + s]; pl[p * Q1 + pc[p]++] = (int32_t)l; }

    /* points e1 = the unit vector of X1 and e6 = the unit vector of X6 (paper indices are 0-based: v = <e_1, e_6>,
       and p_16 is not in Tits' equations); the line v through both */
    int64_t e1 = -1, e6 = -1;
    for (int64_t p = 0; p < N; p++) {
        int nz = 0; for (int j = 0; j < 7; j++) nz += X(p, j) != 0;
        if (nz == 1 && X(p, 1) == 1) e1 = p;
        if (nz == 1 && X(p, 6) == 1) e6 = p;
    }
    int64_t v = -1;
    for (int k = 0; k < Q1 && e1 >= 0; k++) {
        int64_t l = pl[e1 * Q1 + k]; int has = 0;
        for (int s = 0; s < Q1; s++) if (lines[l * Q1 + s] == e6) has = 1;
        if (has) v = l;
    }
    if (v < 0) { fprintf(stderr, "v not found\n"); return 1; }
    printf("q=%d N=%lld e1=%lld e6=%lld v(line)=%lld\n", q, (long long)N, (long long)e1, (long long)e6, (long long)v);

    /* squares, c with -c non-square */
    int *sq = calloc(q, sizeof(int)); for (int x = 1; x < q; x++) sq[x * x % q] = 1;
    int c = 1; while (!((md(-c) != 0) && !sq[md(-c)])) c++;
    /* (c0, c1) */
    int c0 = -1, c1 = -1;
    for (int a0 = 1; a0 < q && c0 < 0; a0++) for (int a1 = 0; a1 < q && c0 < 0; a1++) {
        int ok = 1;
        for (int a = 0; a < q && ok; a++) for (int b = 0; b < q && ok; b++) {
            if (a == 0 && b == 0) continue;
            int G = md((int64_t)md((int64_t)a0 * a + (int64_t)a1 * b) * md((int64_t)a * a + (int64_t)c * b * b) - (int64_t)b * b * b);
            if (G == 0) ok = 0;
        }
        if (ok) { c0 = a0; c1 = a1; }
    }
    if (c0 < 0) { fprintf(stderr, "no (c0,c1)\n"); return 1; }
    printf("c=%d (-c nonsquare), c0=%d c1=%d\n", c, c0, c1);

    #define LAM(p) md((int64_t)X(p, 0) + (int64_t)c * X(p, 4))
    int *lev = malloc(sizeof(int) * 2 * N);
    for (int64_t e = 0; e < 2 * N; e++) lev[e] = -1;
    int64_t nS = 0, nPi = 0, nLv = 0;
    char *inS = calloc(N, 1);
    for (int s = 0; s < Q1; s++) { int64_t p = lines[v * Q1 + s]; lev[p] = 1; }
    for (int64_t l = 0; l < N; l++) {
        int inside = 1; for (int s = 0; s < Q1 && inside; s++) if (LAM(lines[l * Q1 + s]) != 0) inside = 0;
        if (inside) { inS[l] = 1; nS++; }
    }
    for (int64_t p = 0; p < N; p++) if (LAM(p) == 0) { nPi++; if (lev[p] < 0) lev[p] = 0; }
    lev[N + v] = 2;
    for (int64_t l = 0; l < N; l++) if (inS[l] && l != v) lev[N + l] = 1;
    /* L_v: lines != v through a point of v */
    for (int s = 0; s < Q1; s++) { int64_t p = lines[v * Q1 + s];
        for (int k = 0; k < Q1; k++) { int64_t l = pl[p * Q1 + k]; if (l != v && lev[N + l] < 0) { lev[N + l] = 0; nLv++; } } }
    /* W: lines l != v, not in S, lying in some Pi_z with z != 0, with the nu condition */
    int64_t nW = 0, nNoZ = 0, nAmbig = 0, nZeroLine = 0;
    if (Q1 > 64) { fprintf(stderr, "q too big for this code\n"); return 1; }
    for (int64_t l = 0; l < N; l++) {
        if (l == v || inS[l] || lev[N + l] == 0) continue;
        int a2[64], b2[64], bb[64];
        for (int s = 0; s < Q1; s++) { int64_t p = lines[l * Q1 + s]; a2[s] = X(p, 2); b2[s] = X(p, 5); bb[s] = md(-(int64_t)LAM(p)); }
        /* row s: alpha * X2 + beta * X5 = -(X0 + c X4) for each point of l */
        int alpha = -1, beta = -1, found = 0;
        int dj = -1, dk = -1;
        for (int j = 0; j < Q1 && dj < 0; j++) for (int k = j + 1; k < Q1; k++) {
            if (md((int64_t)a2[j] * b2[k] - (int64_t)b2[j] * a2[k])) { dj = j; dk = k; break; }
        }
        if (dj >= 0) {
            int D = md((int64_t)a2[dj] * b2[dk] - (int64_t)b2[dj] * a2[dk]);
            int Dinv = 1; for (int t = 1; t < q; t++) if (md((int64_t)D * t) == 1) Dinv = t;
            alpha = md(((int64_t)bb[dj] * b2[dk] - (int64_t)b2[dj] * bb[dk]) * Dinv);
            beta = md(((int64_t)a2[dj] * bb[dk] - (int64_t)bb[dj] * a2[dk]) * Dinv);
            int ok = 1; for (int s = 0; s < Q1; s++) if (md((int64_t)alpha * a2[s] + (int64_t)beta * b2[s]) != bb[s]) ok = 0;
            if (ok) found = 1;
        }
        if (!found) { /* brute force over z (lines with all points in a rank-1 configuration) */
            int cnt = 0, ta = -1, tb = -1;
            for (int za = 0; za < q; za++) for (int zb = 0; zb < q; zb++) {
                int ok = 1; for (int s = 0; s < Q1 && ok; s++) if (md((int64_t)za * a2[s] + (int64_t)zb * b2[s]) != bb[s]) ok = 0;
                if (ok) { cnt++; ta = za; tb = zb; }
            }
            if (cnt == 1) { alpha = ta; beta = tb; found = 1; }
            else if (cnt > 1) nAmbig++;
        }
        if (!found) { nNoZ++; continue; }
        if (alpha == 0 && beta == 0) { nZeroLine++; continue; }   /* a line of Pi: would be in S (not expected here) */
        /* the unique point X of l on Pi (X0 + c X4 = 0) */
        int64_t Xp = -1, cntX = 0;
        for (int s = 0; s < Q1; s++) { int64_t p = lines[l * Q1 + s]; if (LAM(p) == 0) { Xp = p; cntX++; } }
        if (cntX != 1) { fprintf(stderr, "line %lld meets Pi in %lld points\n", (long long)l, (long long)cntX); return 1; }
        int x2 = X(Xp, 2), x3 = X(Xp, 3), x4 = X(Xp, 4), x5 = X(Xp, 5);
        int num = md((int64_t)x2 * x3 - (int64_t)x4 * x5);
        int den = md((int64_t)c * x2 * x2 + (int64_t)x5 * x5);
        if (den == 0) { fprintf(stderr, "den 0\n"); return 1; }
        int A = md((int64_t)alpha * alpha + (int64_t)c * beta * beta);
        int G = md((int64_t)md((int64_t)c0 * alpha + (int64_t)c1 * beta) * A - (int64_t)beta * beta * beta);
        /* nu = G / A  <=>  num * A == G * den */
        if (md((int64_t)num * A) == md((int64_t)G * den)) { lev[N + l] = 0; nW++; }
    }
    printf("|S|=%lld (q^3+1=%lld)  |points(Pi)|=%lld ((q+1)(q^3+1)=%lld)  |L_v|=%lld (q^2+q=%lld)\n",
           (long long)nS, (long long)((int64_t)q * q * q + 1), (long long)nPi, (long long)((int64_t)Q1 * ((int64_t)q * q * q + 1)),
           (long long)nLv, (long long)(q * q + q));
    printf("|W|=%lld (q^2(q^2-1)=%lld)  lines-with-no-z=%lld ambiguous=%lld zero-z=%lld\n",
           (long long)nW, (long long)((int64_t)q * q * (q * q - 1)), (long long)nNoZ, (long long)nAmbig, (long long)nZeroLine);
    int64_t cntlev[4] = {0, 0, 0, 0};
    for (int64_t e = 0; e < 2 * N; e++) if (lev[e] >= -1) cntlev[lev[e] + 1]++;
    printf("levels: 2:%lld 1:%lld 0:%lld -1:%lld\n", (long long)(1), (long long)cntlev[2], (long long)cntlev[1], (long long)cntlev[0]);

    /* versions: element e of level k has 2^(k+1) versions */
    int64_t *base = malloc(sizeof(int64_t) * 2 * N);
    int64_t nv = 0;
    for (int64_t e = 0; e < 2 * N; e++) { base[e] = nv; nv += (int64_t)1 << (lev[e] + 1); }
    printf("doubled graph: n=%lld vertices\n", (long long)nv);
    /* degrees: two passes over incidences; comparable version pairs are the edges */
    int64_t *deg = calloc(nv, sizeof(int64_t));
    for (int64_t p = 0; p < N; p++) for (int k = 0; k < Q1; k++) {
        int64_t l = pl[p * Q1 + k]; int a = lev[p] + 1, b = lev[N + l] + 1;
        if (a <= b) { for (int64_t s = 0; s < ((int64_t)1 << a); s++) for (int64_t r = 0; r < ((int64_t)1 << (b - a)); r++) { deg[base[p] + s]++; deg[base[N + l] + ((s << (b - a)) | r)]++; } }
        else { for (int64_t t = 0; t < ((int64_t)1 << b); t++) for (int64_t r = 0; r < ((int64_t)1 << (a - b)); r++) { deg[base[p] + ((t << (a - b)) | r)]++; deg[base[N + l] + t]++; } }
    }
    int64_t *off = malloc(sizeof(int64_t) * (nv + 1)); off[0] = 0;
    for (int64_t u = 0; u < nv; u++) off[u + 1] = off[u] + deg[u];
    int32_t *adj = malloc(sizeof(int32_t) * off[nv]);
    int64_t *fp = malloc(sizeof(int64_t) * nv); for (int64_t u = 0; u < nv; u++) fp[u] = off[u];
    for (int64_t p = 0; p < N; p++) for (int k = 0; k < Q1; k++) {
        int64_t l = pl[p * Q1 + k]; int a = lev[p] + 1, b = lev[N + l] + 1;
        if (a <= b) { for (int64_t s = 0; s < ((int64_t)1 << a); s++) for (int64_t r = 0; r < ((int64_t)1 << (b - a)); r++) {
                int64_t x = base[p] + s, y = base[N + l] + ((s << (b - a)) | r); adj[fp[x]++] = (int32_t)y; adj[fp[y]++] = (int32_t)x; } }
        else { for (int64_t t = 0; t < ((int64_t)1 << b); t++) for (int64_t r = 0; r < ((int64_t)1 << (a - b)); r++) {
                int64_t x = base[p] + ((t << (a - b)) | r), y = base[N + l] + t; adj[fp[x]++] = (int32_t)y; adj[fp[y]++] = (int32_t)x; } }
    }
    int64_t mind = 1 << 30, maxd = 0, hist[64]; memset(hist, 0, sizeof hist);
    for (int64_t u = 0; u < nv; u++) { if (deg[u] < mind) mind = deg[u]; if (deg[u] > maxd) maxd = deg[u]; if (deg[u] < 64) hist[deg[u]]++; }
    printf("degrees: min %lld max %lld (q+m = %d); histogram:", (long long)mind, (long long)maxd, q + 2);
    for (int d = 0; d < 64; d++) if (hist[d]) printf(" %d:%lld", d, (long long)hist[d]);
    printf("\nedges=%lld\n", (long long)(off[nv] / 2));
    if (argc >= 5) {
        FILE *g = fopen(argv[4], "w"); fprintf(g, "%lld\n", (long long)nv);
        for (int64_t u = 0; u < nv; u++) for (int64_t i = off[u]; i < off[u + 1]; i++) if ((int64_t)adj[i] > u) fprintf(g, "%lld %d\n", (long long)u, adj[i]);
        fclose(g); printf("wrote edge list %s\n", argv[4]);
    }
    /* BFS sample: random versions, the versions of the points of v, and the versions of the lines through p0 */
    int64_t nrand = atoll(argv[2]); srand(atoi(argv[3]));
    int32_t *dist = malloc(sizeof(int32_t) * nv), *queue = malloc(sizeof(int32_t) * nv);
    int64_t maxecc = 0, nbfs = 0, nsrc = nrand + 2 * (int64_t)Q1;
    int64_t p0 = lines[v * Q1 + 0];
    for (int64_t it = 0; it < nsrc; it++) {
        int64_t src;
        if (it < nrand) src = (((int64_t)rand() << 31) | (int64_t)rand()) % nv;
        else if (it - nrand < Q1) src = base[lines[v * Q1 + (it - nrand)]];
        else src = base[N + pl[p0 * Q1 + (it - nrand - Q1)]];
        for (int64_t u = 0; u < nv; u++) dist[u] = -1;
        int64_t qh = 0, qt = 0; queue[qt++] = (int32_t)src; dist[src] = 0; int ecc = 0;
        while (qh < qt) { int32_t x = queue[qh++]; int d = dist[x]; if (d > ecc) ecc = d;
            for (int64_t i = off[x]; i < off[x + 1]; i++) { int32_t y = adj[i]; if (dist[y] < 0) { dist[y] = d + 1; queue[qt++] = y; } } }
        if (qt != nv) { printf("source %lld: not connected (%lld of %lld)\n", (long long)src, (long long)qt, (long long)nv); return 1; }
        if (ecc > maxecc) maxecc = ecc;
        nbfs++;
    }
    printf("BFS sources=%lld (random %lld + local %d): max eccentricity %lld\n", (long long)nbfs, (long long)nrand, 2 * Q1, (long long)maxecc);
    printf("RESULT %s q=%d m=2 n=%lld maxdeg=%lld maxecc_sampled=%lld\n", (maxecc <= 6 && maxd == q + 2) ? "VALID-SAMPLED" : "CHECK", q, (long long)nv, (long long)maxd, (long long)maxecc);
    return 0;
}
