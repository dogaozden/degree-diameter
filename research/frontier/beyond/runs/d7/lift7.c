/* hexgen2.c: the split Cayley hexagon H(q) for any prime power q <= 32 (including q even).
   Same model as research/p4/d6/hexgen.c: points of X0X4 + X1X5 + X2X6 = X3^2 in PG(6,q); the lines through x are
   the lines through x in the plane pi_x = {y : Tits' six equations, B(x,y) = 0} (B the polar form; in
   characteristic 2 its X3 term vanishes and pi_x is still a plane through x).
   Field GF(p^e): polynomials over GF(p) mod a fixed irreducible, element a0 + a1 p + ... .
   Checks: |lines| = |points| = (q^6-1)/(q-1), q+1 points per line, q+1 lines per point.
   Output: hex/hex_q{q}.bin = int32 q, N, L, then L*(q+1) int32 point ids, then N*7 uint8 coordinates.
   Usage: hexgen2 q */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

int q, p, e;
int ADD[32][32], MUL[32][32], NEG[32], INV[32];

static int poly_for(int q, int *c) { /* monic irreducible of degree e: coefficients c[0..e-1] of x^e = -(c0 + c1 x + ...) */
    /* x^e + c_{e-1} x^{e-1} + ... + c0 */
    memset(c, 0, sizeof(int) * 8);
    switch (q) {
        case 4: c[0] = 1; c[1] = 1; return 2;          /* x^2+x+1 */
        case 8: c[0] = 1; c[1] = 1; return 3;          /* x^3+x+1 */
        case 9: c[0] = 1; return 2;                    /* x^2+1 */
        case 16: c[0] = 1; c[1] = 1; return 4;         /* x^4+x+1 */
        case 25: c[0] = 2; return 2;                   /* x^2+2 */
        case 27: c[0] = 1; c[1] = 2; return 3;         /* x^3+2x+1 */
        case 32: c[0] = 1; c[2] = 1; return 5;         /* x^5+x^2+1 */
    }
    return 1;
}

void field(void) {
    int c[8]; e = poly_for(q, c);
    for (int x = 0; x < q; x++) for (int y = 0; y < q; y++) {
        int a[8] = {0}, b[8] = {0}, r[16] = {0};
        int t = x; for (int i = 0; i < e; i++) { a[i] = t % p; t /= p; }
        t = y; for (int i = 0; i < e; i++) { b[i] = t % p; t /= p; }
        int s = 0, pw = 1;
        for (int i = 0; i < e; i++) { s += ((a[i] + b[i]) % p) * pw; pw *= p; }
        ADD[x][y] = s;
        for (int i = 0; i < e; i++) for (int j = 0; j < e; j++) r[i + j] = (r[i + j] + a[i] * b[j]) % p;
        for (int k = 2 * e - 2; k >= e; k--) {          /* reduce x^k = x^{k-e} * x^e = -x^{k-e}(c0 + ...) */
            int f = r[k]; if (!f) continue; r[k] = 0;
            for (int i = 0; i < e; i++) r[k - e + i] = ((r[k - e + i] - f * c[i]) % p + p) % p;
        }
        s = 0; pw = 1; for (int i = 0; i < e; i++) { s += r[i] * pw; pw *= p; }
        MUL[x][y] = s;
    }
    for (int x = 0; x < q; x++) { NEG[x] = -1; INV[x] = -1;
        for (int y = 0; y < q; y++) { if (ADD[x][y] == 0) NEG[x] = y; if (MUL[x][y] == 1) INV[x] = y; } }
    for (int x = 1; x < q; x++) if (INV[x] < 0) { fprintf(stderr, "not a field\n"); exit(1); }
}
static inline int ad(int a, int b) { return ADD[a][b]; }
static inline int mu(int a, int b) { return MUL[a][b]; }
static inline int sb(int a, int b) { return ADD[a][NEG[b]]; }

int64_t code(const int *v) { int64_t c = 0; for (int i = 6; i >= 0; i--) c = c * q + v[i]; return c; }
void normalize(int *v) { for (int i = 0; i < 7; i++) if (v[i]) { int s = INV[v[i]]; for (int j = 0; j < 7; j++) v[j] = mu(s, v[j]); return; } }

int64_t *codes; int N;
int lookup(int *v) {
    normalize(v); int64_t c = code(v); int lo = 0, hi = N - 1;
    while (lo <= hi) { int m = (lo + hi) / 2; if (codes[m] == c) return m; if (codes[m] < c) lo = m + 1; else hi = m - 1; }
    fprintf(stderr, "point not found\n"); exit(1);
}
int Qf(const int *v) { return sb(ad(ad(mu(v[0], v[4]), mu(v[1], v[5])), mu(v[2], v[6])), mu(v[3], v[3])); }

int nullspace(int M[][7], int k, int B[][7]) {
    int piv[7], r = 0, isp[7] = {0};
    for (int c = 0; c < 7 && r < k; c++) {
        int s = -1; for (int i = r; i < k; i++) if (M[i][c]) { s = i; break; }
        if (s < 0) continue;
        for (int j = 0; j < 7; j++) { int t = M[r][j]; M[r][j] = M[s][j]; M[s][j] = t; }
        int iv = INV[M[r][c]]; for (int j = 0; j < 7; j++) M[r][j] = mu(iv, M[r][j]);
        for (int i = 0; i < k; i++) if (i != r && M[i][c]) { int f = M[i][c]; for (int j = 0; j < 7; j++) M[i][j] = sb(M[i][j], mu(f, M[r][j])); }
        piv[r] = c; isp[c] = 1; r++;
    }
    int d = 0;
    for (int fcol = 0; fcol < 7; fcol++) if (!isp[fcol]) {
        for (int j = 0; j < 7; j++) B[d][j] = 0;
        B[d][fcol] = 1;
        for (int i = 0; i < r; i++) B[d][piv[i]] = NEG[M[i][fcol]];
        d++;
    }
    return d;
}


/* ---- card c09: Theorem A level graph of H(q) (D7_HEXAGON.md Sec. 2) ----
   Field, plane model and point enumeration: copied from research/squads/beyond/r1/c08/hexgen2.c (lines 1-87).
   Lift: M = 2r+1 levels; vertex (e,k), e in [0,2N) (points e=p<N, lines e=N+l), id = e*M+k.
   Edges: (p,k)-(l,k) for each incidence of H(q); (p,k)-(sigma_i(p),k+i) for i=1..r, sigma_i a point->line bijection.
   r = 0 gives M = 1, i.e. the incidence graph of H(q) itself.
   Modes:
     lift7 q r seed edges OUTFILE     apsp input (n, then edges), for small instances
     lift7 q r seed bfs K             structure check + K random sources (<=64) bit-parallel BFS, exact max ecc of the sample */
#include <time.h>
#include <unistd.h>

static void die(const char *s) { fprintf(stderr, "%s\n", s); exit(1); }

int32_t *LP, *PL; int LL;   /* LP[l*(q+1)+j]: points on line l; PL[p*(q+1)+j]: lines through point p */
uint8_t *coord;
int M, R; int32_t **SIG, **SINV;
int64_t nV;

static void build_hex(void) {
    int64_t total = 1; for (int i = 0; i < 7; i++) total *= q;
    int64_t want = 0, pw = 1; for (int i = 0; i < 6; i++) { want += pw; pw *= q; }
    codes = malloc(sizeof(int64_t) * want); N = 0;
    int v[7];
    for (int64_t c = 0; c < total; c++) {
        int64_t t = c; for (int i = 0; i < 7; i++) { v[i] = t % q; t /= q; }
        int f = -1; for (int i = 0; i < 7; i++) if (v[i]) { f = v[i]; break; }
        if (f != 1) continue;
        if (Qf(v)) continue;
        if (N >= want) die("too many points");
        codes[N++] = c;
    }
    if (N != want) die("wrong point count");
    int Q1 = q + 1;
    LP = malloc(sizeof(int32_t) * (int64_t)N * Q1); int L = 0;
    int *cnt = calloc(N, sizeof(int));
    coord = malloc((size_t)N * 7);
    for (int i = 0; i < N; i++) { int64_t t = codes[i]; for (int j = 0; j < 7; j++) { coord[(size_t)i * 7 + j] = t % q; t /= q; } }
    int two = ad(1, 1);
    for (int i = 0; i < N; i++) {
        int x[7]; for (int j = 0; j < 7; j++) x[j] = coord[(size_t)i * 7 + j];
        int Mx[7][7]; memset(Mx, 0, sizeof Mx);
        Mx[0][4] = x[0]; Mx[0][0] = x[4]; Mx[0][5] = x[1]; Mx[0][1] = x[5]; Mx[0][6] = x[2]; Mx[0][2] = x[6]; Mx[0][3] = NEG[mu(two, x[3])];
        int eq[6][4] = {{1,2,3,4},{5,4,3,2},{2,0,3,5},{6,5,3,0},{0,1,3,6},{4,6,3,1}};
        for (int r = 0; r < 6; r++) {
            int a = eq[r][0], b = eq[r][1], c = eq[r][2], d = eq[r][3];
            int *Rr = Mx[r + 1];
            Rr[b] = ad(Rr[b], x[a]); Rr[a] = sb(Rr[a], x[b]);
            Rr[d] = sb(Rr[d], x[c]); Rr[c] = ad(Rr[c], x[d]);
        }
        int B[7][7]; int dim = nullspace(Mx, 7, B);
        if (dim != 3) die("plane dimension");
        int b[2][7], nb = 0;
        for (int k = 0; k < 3 && nb < 2; k++) {
            int T[3][7]; int rows = 0;
            for (int j = 0; j < 7; j++) T[0][j] = x[j]; rows = 1;
            for (int s = 0; s < nb; s++) { for (int j = 0; j < 7; j++) T[rows][j] = b[s][j]; rows++; }
            for (int j = 0; j < 7; j++) T[rows][j] = B[k][j]; rows++;
            int Z[7][7]; int dz = nullspace(T, rows, Z);
            if (7 - dz == rows) { for (int j = 0; j < 7; j++) b[nb][j] = B[k][j]; nb++; }
        }
        if (nb != 2) die("basis");
        for (int t = 0; t <= q; t++) {
            int d[7];
            for (int j = 0; j < 7; j++) d[j] = (t == q) ? b[1][j] : ad(b[0][j], mu(t, b[1][j]));
            int ids[40], n = 0, mn = 1 << 30;
            int w[7]; for (int j = 0; j < 7; j++) w[j] = d[j];
            if (Qf(w)) die("plane point off quadric");
            ids[n++] = lookup(w);
            for (int lam = 0; lam < q; lam++) { for (int j = 0; j < 7; j++) w[j] = ad(x[j], mu(lam, d[j])); ids[n++] = lookup(w); }
            for (int s = 0; s < n; s++) if (ids[s] < mn) mn = ids[s];
            if (mn != i) continue;
            for (int s = 1; s < n; s++) { int k2 = ids[s], u = s - 1; while (u >= 0 && ids[u] > k2) { ids[u + 1] = ids[u]; u--; } ids[u + 1] = k2; }
            for (int s = 0; s < n; s++) { if (s && ids[s] == ids[s - 1]) die("dup point on line"); LP[(int64_t)L * Q1 + s] = ids[s]; cnt[ids[s]]++; }
            L++;
            if (L > N) die("too many lines");
        }
    }
    for (int i = 0; i < N; i++) if (cnt[i] != Q1) die("point not on q+1 lines");
    if (L != N) die("line count");
    PL = malloc(sizeof(int32_t) * (int64_t)N * Q1);
    int *fill = calloc(N, sizeof(int));
    for (int l = 0; l < L; l++) for (int s = 0; s < Q1; s++) { int p = LP[(int64_t)l * Q1 + s]; PL[(int64_t)p * Q1 + fill[p]++] = l; }
    LL = L;
    fprintf(stderr, "H(%d): %d points, %d lines, every point on %d lines, every line has %d points\n", q, N, L, Q1, Q1);
}

static uint64_t rs;
static uint64_t rnd(void) { uint64_t z = (rs += 0x9E3779B97F4A7C15ULL); z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ULL; z = (z ^ (z >> 27)) * 0x94D049BB133111EBULL; return z ^ (z >> 31); }

static void make_lift(int r, uint64_t seed) {
    R = r; M = 2 * r + 1; nV = (int64_t)2 * N * M; rs = seed;
    SIG = malloc(sizeof(int32_t *) * (r + 1)); SINV = malloc(sizeof(int32_t *) * (r + 1));
    for (int i = 0; i < r; i++) {
        int32_t *perm = malloc(sizeof(int32_t) * N);
        for (int j = 0; j < N; j++) perm[j] = j;
        for (int j = N - 1; j > 0; j--) { int jj = (int)(rnd() % (uint64_t)(j + 1)); int32_t t = perm[j]; perm[j] = perm[jj]; perm[jj] = t; }
        SIG[i] = malloc(sizeof(int32_t) * N); SINV[i] = malloc(sizeof(int32_t) * N);
        for (int p = 0; p < N; p++) { SIG[i][p] = perm[p]; SINV[i][perm[p]] = p; }
        free(perm);
    }
}

/* neighbours of vertex v = e*M + k; returns degree (q+1+r) */
static inline int nbrs(int64_t v, int64_t *out) {
    int64_t e = v / M; int k = (int)(v - e * M);
    int Q1 = q + 1, d = 0;
    if (e < N) {
        int64_t p = e;
        for (int j = 0; j < Q1; j++) out[d++] = (N + (int64_t)PL[p * Q1 + j]) * M + k;
        for (int i = 1; i <= R; i++) out[d++] = (N + (int64_t)SIG[i - 1][p]) * M + (k + i) % M;
    } else {
        int64_t l = e - N;
        for (int j = 0; j < Q1; j++) out[d++] = (int64_t)LP[l * Q1 + j] * M + k;
        for (int i = 1; i <= R; i++) out[d++] = (int64_t)SINV[i - 1][l] * M + ((k - i) % M + M) % M;
    }
    return d;
}

static int structure_check(int64_t sym_sample) {
    int Dl = q + 1 + R; int64_t nb[64]; int bad = 0;
    for (int64_t v = 0; v < nV; v++) {
        int d = nbrs(v, nb);
        if (d != Dl) bad++;
        int ptside = (v / M) < N;
        for (int a = 0; a < d; a++) {
            if (((nb[a] / M) < N) == ptside) bad++;           /* bipartite sides */
            for (int b2 = a + 1; b2 < d; b2++) if (nb[a] == nb[b2]) bad++;   /* simple */
        }
        if (bad) { fprintf(stderr, "structure failure at vertex %lld\n", (long long)v); return 0; }
    }
    /* symmetry: sampled */
    uint64_t s0 = rs; int64_t tot = sym_sample < nV ? sym_sample : nV;
    for (int64_t t = 0; t < tot; t++) {
        int64_t v = (sym_sample >= nV) ? t : (int64_t)(rnd() % (uint64_t)nV);
        int d = nbrs(v, nb); int64_t nb2[64];
        for (int a = 0; a < d; a++) {
            int d2 = nbrs(nb[a], nb2); int found = 0;
            for (int b2 = 0; b2 < d2; b2++) if (nb2[b2] == v) found = 1;
            if (!found) { fprintf(stderr, "asymmetric edge at %lld\n", (long long)v); return 0; }
        }
    }
    rs = s0;
    return 1;
}

/* bit-parallel BFS from ns <= 64 sources; pull-based; returns max eccentricity over the sources (or -1) */
static int multi_bfs(const int64_t *srcs, int ns, int maxlev) {
    uint64_t *vis = calloc(nV, 8), *fr = calloc(nV, 8), *nx = calloc(nV, 8);
    uint64_t full = ns == 64 ? ~0ULL : ((1ULL << ns) - 1);
    for (int s = 0; s < ns; s++) { vis[srcs[s]] |= 1ULL << s; fr[srcs[s]] |= 1ULL << s; }
    int lev = 0, ecc = -1; int64_t nb[64];
    for (;;) {
        int64_t unfinished = 0;
        for (int64_t v = 0; v < nV; v++) if (vis[v] != full) unfinished++;
        fprintf(stderr, "  level %d done: %lld (vertex,source-set) incomplete\n", lev, (long long)unfinished);
        if (unfinished == 0) { ecc = lev; break; }
        if (lev >= maxlev) break;
        for (int64_t v = 0; v < nV; v++) {
            int d = nbrs(v, nb); uint64_t acc = 0;
            for (int a = 0; a < d; a++) acc |= fr[nb[a]];
            acc &= ~vis[v]; nx[v] = acc; vis[v] |= acc;
        }
        uint64_t *t = fr; fr = nx; nx = t; lev++;
    }
    free(vis); free(fr); free(nx);
    return ecc;
}

int main(int argc, char **argv) {
    if (argc < 5) { fprintf(stderr, "usage: lift7 q r seed edges OUT | lift7 q r seed bfs K\n"); return 1; }
    q = atoi(argv[1]); int r = atoi(argv[2]); uint64_t seed = strtoull(argv[3], 0, 10);
    for (p = 2; q % p; p++) {}
    field();
    { int pe = 1; for (int i = 0; i < e; i++) pe *= p; if (pe != q) die("unsupported q"); }
    clock_t t0 = clock();
    char cfn[64]; sprintf(cfn, "hex_q%d.bin", q);
    FILE *cf = fopen(cfn, "rb");
    if (cf) {   /* cached incidence: N, L, then LP (line -> points); rebuild PL */
        int32_t hd[2]; if (fread(hd, 4, 2, cf) != 2) die("cache header");
        N = hd[0]; LL = hd[1]; int Q1 = q + 1;
        LP = malloc(sizeof(int32_t) * (int64_t)N * Q1);
        if (fread(LP, 4, (size_t)N * Q1, cf) != (size_t)N * Q1) die("cache body");
        fclose(cf);
        PL = malloc(sizeof(int32_t) * (int64_t)N * Q1); int *fill = calloc(N, sizeof(int));
        for (int l = 0; l < LL; l++) for (int s = 0; s < Q1; s++) { int p = LP[(int64_t)l * Q1 + s]; PL[(int64_t)p * Q1 + fill[p]++] = l; }
        fprintf(stderr, "H(%d) loaded from %s: %d points, %d lines\n", q, cfn, N, LL);
    } else {
        build_hex();
        cf = fopen(cfn, "wb"); int32_t hd[2] = {N, LL};
        fwrite(hd, 4, 2, cf); fwrite(LP, 4, (size_t)N * (q + 1), cf); fclose(cf);
    }
    make_lift(r, seed);
    int Dl = q + 1 + r;
    fprintf(stderr, "lift: r=%d M=%d n=%lld target degree %d (built in %.1f s)\n", r, M, (long long)nV, Dl, (double)(clock() - t0) / CLOCKS_PER_SEC);
    if (!strcmp(argv[4], "edges")) {
        if (argc < 6) die("need OUT");
        FILE *f = fopen(argv[5], "w"); if (!f) die("open");
        fprintf(f, "%lld\n", (long long)nV);
        int64_t nb[64]; long long ne = 0;
        for (int64_t v = 0; v < nV; v++) {
            if ((v / M) >= N) continue;                 /* emit each edge once, from its point end */
            int d = nbrs(v, nb);
            for (int a = 0; a < d; a++) { fprintf(f, "%lld %lld\n", (long long)v, (long long)nb[a]); ne++; }
        }
        fclose(f);
        fprintf(stderr, "wrote %s: n=%lld edges=%lld\n", argv[5], (long long)nV, ne);
        return 0;
    }
    if (!strcmp(argv[4], "bfs")) {
        int K = argc > 5 ? atoi(argv[5]) : 40; if (K > 64) K = 64;
        int ok = structure_check(nV <= 400000 ? nV : 300000);
        fprintf(stderr, "structure (degree %d, simple, bipartite, symmetric): %s\n", Dl, ok ? "ok" : "FAILED");
        if (!ok) return 1;
        int64_t srcs[64];
        for (int s = 0; s < K; s++) srcs[s] = (int64_t)(rnd() % (uint64_t)nV);
        int ecc = multi_bfs(srcs, K, 12);
        printf("RESULT q=%d r=%d n=%lld degree=%d sources=%d max_ecc=%d time=%.1fs\n", q, r, (long long)nV, Dl, K, ecc,
               (double)(clock() - t0) / CLOCKS_PER_SEC);
        return ecc >= 0 && ecc <= 7 ? 0 : 1;
    }
    die("unknown mode");
    return 1;
}
