/* perfcodes.c: spreads / ovoids of the split Cayley hexagon H(q), and partitions into them.
   polylev job (Opus), 2026-10-28.

   A spread of H(q) is a set of q^3+1 pairwise opposite lines (distance 6 in the incidence graph); equivalently a set of
   lines meeting every line 2-ball B2(l) = {l} u {lines meeting l} exactly once (a perfect code). An ovoid is the same
   for points, with B2(p) = the q^2+q+1 points of the plane pi_p.

   Mode "enum": enumerate perfect codes by exact-cover search (branch on the first element not yet covered; it must be
   covered by one of the q^2+q+1 members of its 2-ball). Writes one code per line (element ids) to OUT, up to MAX codes.
   Mode "part": read codes from FILE and search for k = q^2+q+1 of them partitioning the elements (exact cover).
   Usage: perfcodes HEXBIN lines|points enum OUT [MAX] [SEED]
          perfcodes HEXBIN lines|points part CODES OUT [SEED] [MAXNODES] */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

static int q, N, Q1, K, *LP, *PL;
static int n;                 /* number of elements of the chosen type */
static int *ball, bsz;        /* ball[x*bsz + j]: the 2-ball of element x (including x) */

static void build_balls(int lines) {
    bsz = q * q + q + 1; n = N; ball = malloc(sizeof(int) * (size_t)n * bsz);
    int *mark = calloc(n, sizeof(int)), stamp = 0;
    for (int x = 0; x < n; x++) {
        stamp++; int c = 0; ball[(size_t)x * bsz + c++] = x; mark[x] = stamp;
        for (int a = 0; a < Q1; a++) {
            int m = lines ? LP[x * Q1 + a] : PL[x * Q1 + a];          /* neighbour of the other type */
            for (int b = 0; b < Q1; b++) {
                int y = lines ? PL[m * Q1 + b] : LP[m * Q1 + b];
                if (mark[y] != stamp) { mark[y] = stamp; ball[(size_t)x * bsz + c++] = y; }
            }
        }
        if (c != bsz) { fprintf(stderr, "ball size %d at %d\n", c, x); exit(1); }
    }
    free(mark);
}

/* ---------------- enumeration of perfect codes ---------------- */
static int *cov, *code, clen, ncodes, maxcodes; static FILE *fo; static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int *perm;
static void enum_rec(void) {
    if (ncodes >= maxcodes) return;
    int x = -1;
    for (int i = 0; i < n; i++) if (!cov[perm[i]]) { x = perm[i]; break; }
    if (x < 0) {
        for (int i = 0; i < clen; i++) fprintf(fo, "%d%c", code[i], i + 1 < clen ? ' ' : '\n');
        ncodes++; return;
    }
    /* candidates: c in B2(x) with B2(c) entirely uncovered */
    int st = rnd() % bsz;
    for (int jj = 0; jj < bsz; jj++) {
        int c = ball[(size_t)x * bsz + (st + jj) % bsz], ok = 1;
        for (int j = 0; j < bsz && ok; j++) if (cov[ball[(size_t)c * bsz + j]]) ok = 0;
        if (!ok) continue;
        for (int j = 0; j < bsz; j++) cov[ball[(size_t)c * bsz + j]] = 1;
        code[clen++] = c;
        enum_rec();
        clen--;
        for (int j = 0; j < bsz; j++) cov[ball[(size_t)c * bsz + j]] = 0;
        if (ncodes >= maxcodes) return;
    }
}

/* ---------------- partition into codes ---------------- */
static int nc, csz, *codes, **byelt, *nby, *used, *chosen, nch; static long nodes, maxnodes;
static int part_rec(void) {
    if (++nodes > maxnodes) return 0;
    if (nch == K) return 1;
    /* element with fewest available codes */
    int best = -1, bestc = 1 << 30;
    for (int x = 0; x < n; x++) {
        if (used[x]) continue;
        int c = 0;
        for (int i = 0; i < nby[x]; i++) {
            int s = byelt[x][i], ok = 1;
            for (int j = 0; j < csz && ok; j++) if (used[codes[(size_t)s * csz + j]]) ok = 0;
            if (ok) c++;
        }
        if (c < bestc) { bestc = c; best = x; if (c == 0) return 0; }
    }
    int x = best;
    for (int i = 0; i < nby[x]; i++) {
        int s = byelt[x][i], ok = 1;
        for (int j = 0; j < csz && ok; j++) if (used[codes[(size_t)s * csz + j]]) ok = 0;
        if (!ok) continue;
        for (int j = 0; j < csz; j++) used[codes[(size_t)s * csz + j]] = 1;
        chosen[nch++] = s;
        if (part_rec()) return 1;
        nch--;
        for (int j = 0; j < csz; j++) used[codes[(size_t)s * csz + j]] = 0;
        if (nodes > maxnodes) return 0;
    }
    return 0;
}

int main(int argc, char **argv) {
    if (argc < 5) { fprintf(stderr, "usage\n"); return 1; }
    FILE *f = fopen(argv[1], "rb"); int32_t h[3]; if (!f || fread(h, 4, 3, f) != 3) return 1;
    q = h[0]; N = h[1]; Q1 = q + 1; K = q * q + q + 1;
    LP = malloc(sizeof(int) * (size_t)N * Q1); if (fread(LP, 4, (size_t)N * Q1, f) != (size_t)N * Q1) return 1; fclose(f);
    PL = malloc(sizeof(int) * (size_t)N * Q1); int *cnt = calloc(N, sizeof(int));
    for (int l = 0; l < N; l++) for (int a = 0; a < Q1; a++) { int p = LP[l * Q1 + a]; PL[p * Q1 + cnt[p]++] = l; }
    int lines = strcmp(argv[2], "lines") == 0;
    build_balls(lines);
    csz = q * q * q + 1;
    if (strcmp(argv[3], "enum") == 0) {
        fo = fopen(argv[4], "w"); maxcodes = argc > 5 ? atoi(argv[5]) : 1000000;
        if (argc > 6) { rs ^= (uint64_t)atoll(argv[6]) * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 10; i++) rnd(); }
        cov = calloc(n, sizeof(int)); code = malloc(sizeof(int) * n); perm = malloc(sizeof(int) * n);
        for (int i = 0; i < n; i++) perm[i] = i;
        enum_rec(); fclose(fo);
        printf("q=%d %s: %d perfect codes written (cap %d)\n", q, argv[2], ncodes, maxcodes);
        return 0;
    }
    /* part */
    FILE *fc = fopen(argv[4], "r"); int cap = 1024; codes = malloc(sizeof(int) * (size_t)cap * csz); nc = 0; int v;
    while (fscanf(fc, "%d", &v) == 1) {
        if (nc == cap) { cap *= 2; codes = realloc(codes, sizeof(int) * (size_t)cap * csz); }
        codes[(size_t)nc * csz] = v; for (int j = 1; j < csz; j++) if (fscanf(fc, "%d", &codes[(size_t)nc * csz + j]) != 1) return 1;
        nc++;
    }
    fclose(fc);
    nby = calloc(n, sizeof(int)); byelt = malloc(sizeof(int *) * n);
    for (int s = 0; s < nc; s++) for (int j = 0; j < csz; j++) nby[codes[(size_t)s * csz + j]]++;
    for (int x = 0; x < n; x++) { byelt[x] = malloc(sizeof(int) * (nby[x] + 1)); nby[x] = 0; }
    for (int s = 0; s < nc; s++) for (int j = 0; j < csz; j++) { int x = codes[(size_t)s * csz + j]; byelt[x][nby[x]++] = s; }
    used = calloc(n, sizeof(int)); chosen = malloc(sizeof(int) * K);
    maxnodes = argc > 7 ? atol(argv[7]) : 100000000L;
    int ok = part_rec();
    printf("q=%d %s: %d codes read; partition %s (nodes %ld)\n", q, argv[2], nc, ok ? "FOUND" : "not found", nodes);
    if (ok) {
        FILE *fp = fopen(argv[5], "w"); int *cls = malloc(sizeof(int) * n);
        for (int i = 0; i < K; i++) for (int j = 0; j < csz; j++) cls[codes[(size_t)chosen[i] * csz + j]] = i;
        for (int x = 0; x < n; x++) fprintf(fp, "%d\n", cls[x]);
        fclose(fp);
    }
    return 0;
}
