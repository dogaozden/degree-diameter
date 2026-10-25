/* nlift.c: exact diameter-8 test for lifts of a bipartite base graph by an ARBITRARY finite group (card c8, r2_d14D8).

   Base graph: sides A (nA vertices, points) and B (nB, lines), edges (a, b, v) with v a group element index.
   Lift: vertices (a, x), (b, x), x in G; base edge (a,b,v) gives (a, x) ~ (b, x*v) (right multiplication).
   Left multiplication by G is an automorphism of the lift acting regularly on each fibre, so every vertex is
   equivalent to (a, e) for an A-vertex a: sources (a, e) suffice (a in A).
   Walk A->B along (a,b,v): x -> x*v.  Walk B->A along (a,b,v): y -> y*v^{-1}.
   For even D: diameter <= D iff from every (a, e) every (b, g) is reached by a walk of length exactly D-1
   (same argument as lifteval.c; bipartite padding). Tested here for D = 8 (walks of length 7) by default.

   Group file: "m" then m*m integers, table[x*m+y] = x*y, identity = index 0.
   Base file : "nA nB" then lines "a b v".
   Usage: nlift GROUPFILE BASEFILE D [srcspec] [verbose]
     srcspec: all (default) | r:K:seed | i:a1,a2,... | s:start:step
   Output: "COST total sources n bad b worst_src s worst w m M E ..." ; exit code 0 iff COST 0.
   Reach sets are bitsets over G (W = ceil(m/64) words). Right multiplication by v is applied through byte tables. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

typedef uint64_t u64;
static int m, W, NCH, nA, nB, nE;
static int *mul, *inv_;
static u64 *tbl;   /* tbl[((v*NCH + j)*256 + byte)*W + w] = image of the byte-chunk j of a set under x -> x*v */
static int *Aoff, *Aadj, *Avol, *Boff, *Badj, *Bvol;
static u64 rs = 0x9E3779B97F4A7C15ULL;
static u64 rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }

static inline void apply_or(int v, const u64 *src, u64 *dst) {
    for (int j = 0; j < NCH; j++) {
        unsigned byte = (unsigned)((src[j >> 3] >> (8 * (j & 7))) & 0xFF);
        if (!byte) continue;
        const u64 *t = tbl + (((size_t)v * NCH + j) * 256 + byte) * W;
        for (int w = 0; w < W; w++) dst[w] |= t[w];
    }
}

static int nonzero(const u64 *x) { for (int w = 0; w < W; w++) if (x[w]) return 1; return 0; }

static long long run_source(int src, u64 *RA, u64 *RB, int L) {
    memset(RA, 0, sizeof(u64) * (size_t)nA * W);
    memset(RB, 0, sizeof(u64) * (size_t)nB * W);
    RA[(size_t)src * W] = 1;               /* identity element is index 0 */
    for (int t = 0; t < L; t++) {
        if (t % 2 == 0) {                  /* A -> B */
            memset(RB, 0, sizeof(u64) * (size_t)nB * W);
            for (int a = 0; a < nA; a++) {
                const u64 *x = RA + (size_t)a * W; if (!nonzero(x)) continue;
                for (int k = Aoff[a]; k < Aoff[a + 1]; k++) apply_or(Avol[k], x, RB + (size_t)Aadj[k] * W);
            }
        } else {                           /* B -> A (Bvol holds the inverse voltage) */
            memset(RA, 0, sizeof(u64) * (size_t)nA * W);
            for (int b = 0; b < nB; b++) {
                const u64 *y = RB + (size_t)b * W; if (!nonzero(y)) continue;
                for (int k = Boff[b]; k < Boff[b + 1]; k++) apply_or(Bvol[k], y, RA + (size_t)Badj[k] * W);
            }
        }
    }
    /* L is odd (D = 8 -> L = 7): the walk ends on side B */
    long long unc = 0;
    for (int b = 0; b < nB; b++) {
        int cnt = 0; const u64 *y = RB + (size_t)b * W;
        for (int w = 0; w < W; w++) cnt += __builtin_popcountll(y[w]);
        unc += m - cnt;
    }
    return unc;
}

int main(int argc, char **argv) {
    if (argc < 4) { fprintf(stderr, "usage: nlift GROUPFILE BASEFILE D [srcspec] [verbose]\n"); return 2; }
    int D = atoi(argv[3]);
    const char *spec = argc > 4 ? argv[4] : "all";
    int verbose = argc > 5 ? atoi(argv[5]) : 0;
    if (D % 2 != 0) { fprintf(stderr, "only even D implemented\n"); return 2; }
    FILE *g = fopen(argv[1], "r"); if (!g) { perror("group"); return 2; }
    if (fscanf(g, "%d", &m) != 1 || m < 1 || m > 1024) { fprintf(stderr, "bad group header\n"); return 2; }
    mul = malloc(sizeof(int) * (size_t)m * m); inv_ = malloc(sizeof(int) * m);
    for (int i = 0; i < m * m; i++) if (fscanf(g, "%d", &mul[i]) != 1) { fprintf(stderr, "bad group table\n"); return 2; }
    fclose(g);
    for (int x = 0; x < m; x++) {
        if (mul[x] != x || mul[x * m] != x) { fprintf(stderr, "index 0 must be the identity\n"); return 2; }
        inv_[x] = -1;
        for (int y = 0; y < m; y++) if (mul[x * m + y] == 0) inv_[x] = y;
        if (inv_[x] < 0) { fprintf(stderr, "no inverse for %d: not a group table\n", x); return 2; }
    }
    W = (m + 63) / 64; NCH = (m + 7) / 8;
    tbl = calloc((size_t)m * NCH * 256 * W, sizeof(u64));
    for (int v = 0; v < m; v++)
        for (int j = 0; j < NCH; j++)
            for (int b = 0; b < 256; b++) {
                u64 *t = tbl + (((size_t)v * NCH + j) * 256 + b) * W;
                for (int bit = 0; bit < 8; bit++) if ((b >> bit) & 1) {
                    int x = 8 * j + bit; if (x >= m) continue;
                    int y = mul[x * m + v];
                    t[y >> 6] |= 1ULL << (y & 63);
                }
            }
    FILE *f = fopen(argv[2], "r"); if (!f) { perror("base"); return 2; }
    if (fscanf(f, "%d %d", &nA, &nB) != 2) { fprintf(stderr, "bad base header\n"); return 2; }
    int cap = 1 << 16, n = 0;
    int *ea = malloc(sizeof(int) * cap), *eb = malloc(sizeof(int) * cap), *ev = malloc(sizeof(int) * cap);
    int a, b, v;
    while (fscanf(f, "%d %d %d", &a, &b, &v) == 3) {
        if (a < 0 || a >= nA || b < 0 || b >= nB || v < 0 || v >= m) { fprintf(stderr, "bad edge %d %d %d\n", a, b, v); return 2; }
        if (n == cap) { cap *= 2; ea = realloc(ea, sizeof(int) * cap); eb = realloc(eb, sizeof(int) * cap); ev = realloc(ev, sizeof(int) * cap); }
        ea[n] = a; eb[n] = b; ev[n] = v; n++;
    }
    fclose(f); nE = n;
    Aoff = calloc(nA + 1, sizeof(int)); Boff = calloc(nB + 1, sizeof(int));
    for (int e = 0; e < nE; e++) { Aoff[ea[e] + 1]++; Boff[eb[e] + 1]++; }
    for (int i = 0; i < nA; i++) Aoff[i + 1] += Aoff[i];
    for (int i = 0; i < nB; i++) Boff[i + 1] += Boff[i];
    Aadj = malloc(sizeof(int) * nE); Avol = malloc(sizeof(int) * nE); Badj = malloc(sizeof(int) * nE); Bvol = malloc(sizeof(int) * nE);
    int *pa = malloc(sizeof(int) * nA), *pb = malloc(sizeof(int) * nB);
    memcpy(pa, Aoff, sizeof(int) * nA); memcpy(pb, Boff, sizeof(int) * nB);
    for (int e = 0; e < nE; e++) {
        Aadj[pa[ea[e]]] = eb[e]; Avol[pa[ea[e]]++] = ev[e];
        Badj[pb[eb[e]]] = ea[e]; Bvol[pb[eb[e]]++] = inv_[ev[e]];
    }
    /* sources */
    int nsrc = 0; int *src = malloc(sizeof(int) * (nA + 8));
    if (!strcmp(spec, "all")) { for (int i = 0; i < nA; i++) src[nsrc++] = i; }
    else if (spec[0] == 'r') { int K = 0; unsigned long long seed = 1; sscanf(spec, "r:%d:%llu", &K, &seed);
        rs = 0x9E3779B97F4A7C15ULL + (seed + 1) * 0xD1B54A32D192ED03ULL; if (!rs) rs = 1; for (int i = 0; i < 20; i++) rnd();
        for (int i = 0; i < K; i++) src[nsrc++] = (int)(rnd() % (u64)nA); }
    else if (spec[0] == 's') { int st = 0, sp = 1; sscanf(spec, "s:%d:%d", &st, &sp); for (int i = st; i < nA; i += sp) src[nsrc++] = i; }
    else if (spec[0] == 'i') { const char *p = spec + 2; while (*p) { src[nsrc++] = atoi(p); while (*p && *p != ',') p++; if (*p) p++; } }
    else { fprintf(stderr, "bad srcspec\n"); return 2; }
    u64 *RA = malloc(sizeof(u64) * (size_t)nA * W), *RB = malloc(sizeof(u64) * (size_t)nB * W);
    long long total = 0, worstc = -1; int worst = -1, bad = 0;
    for (int s = 0; s < nsrc; s++) {
        long long unc = run_source(src[s], RA, RB, D - 1);
        if (verbose && unc) fprintf(stderr, "src %d uncovered %lld\n", src[s], unc);
        if (unc) bad++;
        total += unc; if (unc > worstc) { worstc = unc; worst = src[s]; }
    }
    printf("COST %lld sources %d bad %d worst_src %d worst %lld m %d E %d lift_vertices %lld\n", total, nsrc, bad, worst,
           worstc, m, nE, (long long)(nA + nB) * m);
    return total ? 1 : 0;
}
