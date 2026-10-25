/* mis_tabu.c: k-fixed tabu search for pairwise-opposite sets in H(7) (squad r4, card c5).
   points: conflict(x,y) iff B(x,y)=0 mod 7 (x!=y), B = polar form of X0X4+X1X5+X2X6-X3^2.
   lines : conflict(L,M) iff the 2x2 pairing det(B(x_i,y_j)) = 0 mod 7 on the first two points (L!=M).
   Usage: mis_tabu MODE(points|lines) K0 KMAX ITERS SEED OUTPREFIX [INITFILE]
   Writes OUTPREFIX_<k>.txt (whitespace ids) for every k reached. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>
#define Q 7
static int q, N, Lc, *LP;      /* LP: line -> points (q+1 each) */
static int *coords_dummy;
static unsigned char *C;       /* N*7 coords */
static uint64_t *bits; static int W;
static int *nb; static int *deg;
static uint64_t rs;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline int adj(int a, int b) { return (bits[(size_t)a * W + (b >> 6)] >> (b & 63)) & 1; }
static int bform(const unsigned char *x, const unsigned char *y) {
    int s = x[0]*y[4] + x[4]*y[0] + x[1]*y[5] + x[5]*y[1] + x[2]*y[6] + x[6]*y[2] - 2*x[3]*y[3];
    s %= Q; if (s < 0) s += Q; return s;
}
int main(int argc, char **argv) {
    if (argc < 7) { fprintf(stderr, "usage: mis_tabu points|lines K0 KMAX ITERS SEED OUTPREFIX [INITFILE]\n"); return 2; }
    int isline = !strcmp(argv[1], "lines");
    int K0 = atoi(argv[2]), KMAX = atoi(argv[3]); long ITERS = atol(argv[4]);
    rs = 88172645463325252ULL ^ (uint64_t)atol(argv[5]) * 2654435761ULL; if (!rs) rs = 1;
    const char *outp = argv[6];
    FILE *f = fopen("/home/user/degree-diameter/research/d10D7/hex/hex_q7.bin", "rb");
    int32_t hdr[3]; if (!f || fread(hdr, 4, 3, f) != 3) { fprintf(stderr, "read fail\n"); return 2; }
    q = hdr[0]; N = hdr[1]; int L = hdr[2];
    LP = malloc(sizeof(int) * (size_t)L * (q + 1));
    if (fread(LP, 4, (size_t)L * (q + 1), f) != (size_t)L * (q + 1)) return 2;
    C = malloc((size_t)N * 7); if (fread(C, 1, (size_t)N * 7, f) != (size_t)N * 7) return 2; fclose(f);
    W = (N + 63) / 64;
    bits = calloc((size_t)N * W, 8); nb = malloc(sizeof(int) * (size_t)N * 2900); deg = calloc(N, sizeof(int));
    /* build conflict graph */
    for (int a = 0; a < N; a++) for (int b = a + 1; b < N; b++) {
        int conf;
        if (!isline) conf = (bform(C + 7 * a, C + 7 * b) == 0);
        else {
            /* lines a,b: first two points of each */
            const unsigned char *x1 = C + 7 * LP[a * (q + 1) + 0], *x2 = C + 7 * LP[a * (q + 1) + 1];
            const unsigned char *y1 = C + 7 * LP[b * (q + 1) + 0], *y2 = C + 7 * LP[b * (q + 1) + 1];
            int det = (bform(x1, y1) * bform(x2, y2) - bform(x1, y2) * bform(x2, y1)) % Q; if (det < 0) det += Q;
            conf = (det == 0);
        }
        if (conf) {
            bits[(size_t)a * W + (b >> 6)] |= 1ULL << (b & 63); bits[(size_t)b * W + (a >> 6)] |= 1ULL << (a & 63);
            nb[(size_t)a * 2900 + deg[a]++] = b; nb[(size_t)b * 2900 + deg[b]++] = a;
        }
    }
    fprintf(stderr, "graph built: N=%d deg0=%d\n", N, deg[0]);
    /* state */
    int *S = malloc(sizeof(int) * N), *pos = malloc(sizeof(int) * N), n = 0;
    int *cnt = calloc(N, sizeof(int)); long *tabu = calloc(N, sizeof(long));
    char *inS = calloc(N, 1);
    /* init: greedy random maximal independent set */
    for (int i = 0; i < N; i++) pos[i] = -1;
    if (argc > 7) {
        FILE *g = fopen(argv[7], "r"); int x;
        while (g && fscanf(g, "%d", &x) == 1) { if (!inS[x]) { inS[x] = 1; pos[x] = n; S[n++] = x; for (int j = 0; j < deg[x]; j++) cnt[nb[(size_t)x * 2900 + j]]++; } }
        if (g) fclose(g);
        fprintf(stderr, "init from file: %d\n", n);
    }
    while (n < K0) { /* add min-cnt vertex */
        int best = -1, bc = 1 << 30, ties = 0;
        for (int v = 0; v < N; v++) if (!inS[v]) { if (cnt[v] < bc) { bc = cnt[v]; best = v; ties = 1; } else if (cnt[v] == bc && (rnd() % (++ties)) == 0) best = v; }
        inS[best] = 1; pos[best] = n; S[n++] = best; for (int j = 0; j < deg[best]; j++) cnt[nb[(size_t)best * 2900 + j]]++;
    }
    int bestk = 0;
    for (int k = n; k <= KMAX; k++) {
        /* ensure size k */
        while (n < k) {
            int best = -1, bc = 1 << 30, ties = 0;
            for (int v = 0; v < N; v++) if (!inS[v]) { if (cnt[v] < bc) { bc = cnt[v]; best = v; ties = 1; } else if (cnt[v] == bc && (rnd() % (++ties)) == 0) best = v; }
            inS[best] = 1; pos[best] = n; S[n++] = best; for (int j = 0; j < deg[best]; j++) cnt[nb[(size_t)best * 2900 + j]]++;
        }
        long f = 0; for (int i = 0; i < n; i++) f += cnt[S[i]]; f /= 2;
        long bestf = f; int found = (f == 0);
        for (long it = 1; it <= ITERS && !found; it++) {
            /* u in S: max cnt among non-tabu (random ties) */
            int u = -1, uc = -1, ties = 0;
            for (int i = 0; i < n; i++) { int v = S[i]; if (tabu[v] > it && f > 0) { /* allow aspiration below */ }
                if (tabu[v] > it) continue;
                if (cnt[v] > uc) { uc = cnt[v]; u = v; ties = 1; } else if (cnt[v] == uc && (rnd() % (++ties)) == 0) u = v; }
            if (u < 0) { u = S[rnd() % n]; uc = cnt[u]; }
            /* v not in S: min cnt - adj(u,v), non-tabu */
            int v = -1, vc = 1 << 30; ties = 0;
            for (int w = 0; w < N; w++) { if (inS[w] || w == u) continue; if (tabu[w] > it) continue;
                int c = cnt[w] - adj(u, w);
                if (c < vc) { vc = c; v = w; ties = 1; } else if (c == vc && (rnd() % (++ties)) == 0) v = w; }
            if (v < 0) continue;
            /* apply swap u out, v in */
            int pu = pos[u];
            inS[u] = 0; pos[u] = -1; S[pu] = v; pos[v] = pu; inS[v] = 1;
            for (int j = 0; j < deg[u]; j++) cnt[nb[(size_t)u * 2900 + j]]--;
            for (int j = 0; j < deg[v]; j++) cnt[nb[(size_t)v * 2900 + j]]++;
            f += (long)vc - uc;
            tabu[u] = it + 7 + (long)(rnd() % 10);     /* u may not return soon */
            tabu[v] = it + 2 + (long)(rnd() % 4);      /* v may not leave soon */
            if (f < bestf) bestf = f;
            if (f == 0) found = 1;
        }
        if (!found) { fprintf(stderr, "k=%d FAILED (best conflicts %ld)\n", k, bestf); break; }
        bestk = k;
        char fn[512]; snprintf(fn, sizeof fn, "%s_%d.txt", outp, k);
        FILE *o = fopen(fn, "w"); for (int i = 0; i < n; i++) fprintf(o, "%d\n", S[i]); fclose(o);
        fprintf(stderr, "k=%d found -> %s\n", k, fn);
        if (k == KMAX) break;
    }
    printf("bestk %d\n", bestk);
    return 0;
}
