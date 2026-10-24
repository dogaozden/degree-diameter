/* liftevalw.c: like lifteval.c, but masks of W = ceil(m/64) words, so m <= 1024 (cell-14-8 job, 2026-10-24).

   Base graph: sides A (nA) and B (nB), edges (a, b, v), v in Z_m. Lift: (a, g) ~ (b, g + v).
   Even D: diameter <= D iff from every (a, 0) all (b, g) are reached by walks of length exactly D - 1.
   Input (text): "nA nB m" then "a b v" lines.
   Usage: liftevalw FILE D [srcspec] [verbose]   srcspec: all | r:K:seed | s:start:step | i:a1,a2,...
   Output: "COST total sources n bad b worst_src s worst w maxdeg d lift_vertices V"; exit 0 iff cost 0. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

typedef uint64_t u64;
static int nA, nB, m, nE, W;
static int *Aoff, *Aadj, *Avol, *Boff, *Badj, *Bvol;
static u64 LASTMASK;

/* out |= ((x << v) | (x >> (m - v))) restricted to m bits; x has no bits >= m */
static inline void orrot(u64 *restrict out, const u64 *restrict x, int v) {
    if (W == 1) { u64 y = x[0]; if (v) y = ((y << v) | (y >> (m - v))) & LASTMASK; out[0] |= y; return; }
    if (v == 0) { for (int i = 0; i < W; i++) out[i] |= x[i]; return; }
    int ws = v >> 6, bs = v & 63;
    for (int i = W - 1; i >= ws; i--) {
        int s = i - ws;
        u64 val = x[s] << bs;
        if (bs && s >= 1) val |= x[s - 1] >> (64 - bs);
        if (i == W - 1) val &= LASTMASK;
        out[i] |= val;
    }
    int r = m - v, wr = r >> 6, br = r & 63;
    for (int i = 0; i + wr < W; i++) {
        int s = i + wr;
        u64 val = x[s] >> br;
        if (br && s + 1 < W) val |= x[s + 1] << (64 - br);
        out[i] |= val;
    }
}

static u64 rs = 0x9E3779B97F4A7C15ULL;
static u64 rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }

static void walk(int side, int src, int L, u64 *bA, u64 *bB) {
    memset(bA, 0, sizeof(u64) * nA * W); memset(bB, 0, sizeof(u64) * nB * W);
    if (side == 0) bA[(size_t)src * W] = 1; else bB[(size_t)src * W] = 1;
    int cur = side;
    for (int step = 0; step < L; step++) {
        if (cur == 0) {
            memset(bB, 0, sizeof(u64) * nB * W);
            for (int a = 0; a < nA; a++) {
                const u64 *x = bA + (size_t)a * W; int nz = 0; for (int i = 0; i < W; i++) nz |= x[i] != 0; if (!nz) continue;
                for (int k = Aoff[a]; k < Aoff[a + 1]; k++) orrot(bB + (size_t)Aadj[k] * W, x, Avol[k]);
            }
            cur = 1;
        } else {
            memset(bA, 0, sizeof(u64) * nA * W);
            for (int b = 0; b < nB; b++) {
                const u64 *x = bB + (size_t)b * W; int nz = 0; for (int i = 0; i < W; i++) nz |= x[i] != 0; if (!nz) continue;
                for (int k = Boff[b]; k < Boff[b + 1]; k++) orrot(bA + (size_t)Badj[k] * W, x, (m - Bvol[k]) % m);
            }
            cur = 0;
        }
    }
}

static long long uncovered(const u64 *buf, int n) {
    long long u = 0;
    for (int i = 0; i < n; i++) { int c = 0; for (int w = 0; w < W; w++) c += __builtin_popcountll(buf[(size_t)i * W + w]); u += m - c; }
    return u;
}

int main(int argc, char **argv) {
    if (argc < 3) { fprintf(stderr, "usage: liftevalw FILE D [srcspec] [verbose]\n"); return 2; }
    FILE *f = fopen(argv[1], "r"); if (!f) { perror("open"); return 2; }
    int D = atoi(argv[2]);
    const char *spec = argc > 3 ? argv[3] : "all";
    int verbose = argc > 4 ? atoi(argv[4]) : 0;
    if (fscanf(f, "%d %d %d", &nA, &nB, &m) != 3 || m < 1 || m > 1024) { fprintf(stderr, "bad header\n"); return 2; }
    W = (m + 63) / 64;
    LASTMASK = (m % 64 == 0) ? ~0ULL : ((1ULL << (m % 64)) - 1);
    int cap = 1 << 20; int *ea = malloc(sizeof(int) * cap), *eb = malloc(sizeof(int) * cap), *ev = malloc(sizeof(int) * cap);
    nE = 0; int a, b, v;
    while (fscanf(f, "%d %d %d", &a, &b, &v) == 3) {
        if (a < 0 || a >= nA || b < 0 || b >= nB) { fprintf(stderr, "bad edge %d %d\n", a, b); return 2; }
        if (nE == cap) { cap *= 2; ea = realloc(ea, sizeof(int) * cap); eb = realloc(eb, sizeof(int) * cap); ev = realloc(ev, sizeof(int) * cap); }
        ea[nE] = a; eb[nE] = b; ev[nE] = ((v % m) + m) % m; nE++;
    }
    fclose(f);
    Aoff = calloc(nA + 1, sizeof(int)); Boff = calloc(nB + 1, sizeof(int));
    for (int e = 0; e < nE; e++) { Aoff[ea[e] + 1]++; Boff[eb[e] + 1]++; }
    int maxdA = 0, maxdB = 0;
    for (int i = 0; i < nA; i++) { if (Aoff[i + 1] > maxdA) maxdA = Aoff[i + 1]; Aoff[i + 1] += Aoff[i]; }
    for (int i = 0; i < nB; i++) { if (Boff[i + 1] > maxdB) maxdB = Boff[i + 1]; Boff[i + 1] += Boff[i]; }
    Aadj = malloc(sizeof(int) * nE); Avol = malloc(sizeof(int) * nE); Badj = malloc(sizeof(int) * nE); Bvol = malloc(sizeof(int) * nE);
    int *pa = malloc(sizeof(int) * nA), *pb = malloc(sizeof(int) * nB);
    memcpy(pa, Aoff, sizeof(int) * nA); memcpy(pb, Boff, sizeof(int) * nB);
    for (int e = 0; e < nE; e++) { Aadj[pa[ea[e]]] = eb[e]; Avol[pa[ea[e]]++] = ev[e]; Badj[pb[eb[e]]] = ea[e]; Bvol[pb[eb[e]]++] = ev[e]; }
    long multi = 0;
    for (int i = 0; i < nA; i++) for (int k = Aoff[i]; k < Aoff[i + 1]; k++) for (int k2 = Aoff[i]; k2 < k; k2++)
        if (Aadj[k] == Aadj[k2] && Avol[k] == Avol[k2]) multi++;
    fprintf(stderr, "base: nA %d nB %d m %d (W %d) edges %d maxdeg A %d B %d; lift %lld vertices; multi-edges %ld\n",
            nA, nB, m, W, nE, maxdA, maxdB, (long long)(nA + nB) * m, multi);
    int nsrc = 0; int *src = malloc(sizeof(int) * (nA + 8));
    if (!strcmp(spec, "all")) { for (int i = 0; i < nA; i++) src[nsrc++] = i; }
    else if (spec[0] == 'r') { int K = 0; unsigned long long seed = 1; sscanf(spec, "r:%d:%llu", &K, &seed);
        rs = 0x9E3779B97F4A7C15ULL + (seed + 1) * 0xD1B54A32D192ED03ULL; if (!rs) rs = 1; for (int i = 0; i < 20; i++) rnd();
        for (int i = 0; i < K; i++) src[nsrc++] = (int)(rnd() % (u64)nA); }
    else if (spec[0] == 's') { int st = 0, sp = 1; sscanf(spec, "s:%d:%d", &st, &sp); for (int i = st; i < nA; i += sp) src[nsrc++] = i; }
    else if (spec[0] == 'i') { const char *p = spec + 2; while (*p) { src[nsrc++] = atoi(p); while (*p && *p != ',') p++; if (*p) p++; } }
    u64 *bA = malloc(sizeof(u64) * nA * W), *bB = malloc(sizeof(u64) * nB * W);
    long long total = 0, worstc = -1; int worst = -1, bad = 0;
    for (int s = 0; s < nsrc; s++) {
        long long unc;
        if (D % 2 == 0) { walk(0, src[s], D - 1, bA, bB); unc = uncovered(bB, nB); }
        else { walk(0, src[s], D - 1, bA, bB); unc = uncovered(bA, nA); walk(0, src[s], D, bA, bB); unc += uncovered(bB, nB); }
        if (verbose && unc) fprintf(stderr, "src %d uncovered %lld\n", src[s], unc);
        if (unc) bad++;
        total += unc; if (unc > worstc) { worstc = unc; worst = src[s]; }
    }
    printf("COST %lld sources %d bad %d worst_src %d worst %lld maxdeg %d lift_vertices %lld\n", total, nsrc, bad, worst, worstc,
           maxdA > maxdB ? maxdA : maxdB, (long long)(nA + nB) * m);
    return total ? 1 : 0;
}
