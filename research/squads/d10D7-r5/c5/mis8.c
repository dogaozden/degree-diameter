/* c5: k-fixed tabu for pairwise-opposite (B != 0) point sets of H(8), restricted to a candidate id list.
   Usage: mis8 HEXBIN IDLIST K0 KMAX ITERS SEED OUTPREFIX [INITFILE]
   Writes OUTPREFIX_<k>.txt (hex point ids) for each k reached. Adapted from research/squads/d10D7-r4/c5/mis_tabu.c. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
static uint8_t MT[8][8];
static uint64_t rs;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int hm(int a, int b) { int r = 0; for (int i = 0; i < 3; i++) if ((b >> i) & 1) r ^= a << i;
    for (int i = 4; i >= 3; i--) if ((r >> i) & 1) r ^= 0xB << (i - 3); return r; }
int main(int argc, char **argv) {
    if (argc < 8) { fprintf(stderr, "usage: mis8 HEXBIN IDLIST K0 KMAX ITERS SEED OUTPREFIX [INIT]\n"); return 2; }
    for (int a = 0; a < 8; a++) for (int b = 0; b < 8; b++) MT[a][b] = hm(a, b);
    FILE *f = fopen(argv[1], "rb"); int32_t hdr[3]; if (!f || fread(hdr, 4, 3, f) != 3) return 2;
    int q = hdr[0], N = hdr[1], L = hdr[2]; (void)q;
    fseek(f, 12L + 4L * L * (q + 1), SEEK_SET);
    uint8_t *C = malloc((size_t)N * 7); if (fread(C, 1, (size_t)N * 7, f) != (size_t)N * 7) return 2; fclose(f);
    int *id = malloc(sizeof(int) * 20000), n = 0; f = fopen(argv[2], "r"); int x;
    while (fscanf(f, "%d", &x) == 1) id[n++] = x; fclose(f);
    int K0 = atoi(argv[3]), KMAX = atoi(argv[4]); long ITERS = atol(argv[5]);
    rs = 88172645463325252ULL ^ (uint64_t)atol(argv[6]) * 2654435761ULL; if (!rs) rs = 1;
    const char *outp = argv[7];
    int W = (n + 63) / 64; uint64_t *bits = calloc((size_t)n * W, 8);
    int *deg = calloc(n, sizeof(int)); int *nb = malloc(sizeof(int) * (size_t)n * n / 4 + 1000); /* upper bound on degree handled below */
    int MAXD = n; int *nbl = malloc(sizeof(int) * (size_t)n * MAXD); (void)nb;
    for (int a = 0; a < n; a++) for (int b = a + 1; b < n; b++) {
        const uint8_t *X = C + 7 * id[a], *Y = C + 7 * id[b];
        int B = MT[X[0]][Y[4]] ^ MT[X[4]][Y[0]] ^ MT[X[1]][Y[5]] ^ MT[X[5]][Y[1]] ^ MT[X[2]][Y[6]] ^ MT[X[6]][Y[2]];
        if (B == 0) {
            bits[(size_t)a * W + (b >> 6)] |= 1ULL << (b & 63); bits[(size_t)b * W + (a >> 6)] |= 1ULL << (a & 63);
            nbl[(size_t)a * MAXD + deg[a]++] = b; nbl[(size_t)b * MAXD + deg[b]++] = a;
        }
    }
    fprintf(stderr, "candidates %d, conflict degree of 0: %d\n", n, deg[0]);
    #define ADJ(a, b) ((bits[(size_t)(a) * W + ((b) >> 6)] >> ((b) & 63)) & 1)
    int *S = malloc(sizeof(int) * n), *pos = malloc(sizeof(int) * n), m = 0;
    int *cnt = calloc(n, sizeof(int)); long *tabu = calloc(n, sizeof(long)); char *inS = calloc(n, 1);
    for (int i = 0; i < n; i++) pos[i] = -1;
    if (argc > 8) { FILE *g = fopen(argv[8], "r"); int y;
        /* init file holds hex ids; map to candidate indices */
        while (g && fscanf(g, "%d", &y) == 1) { for (int a = 0; a < n; a++) if (id[a] == y && !inS[a]) { inS[a] = 1; pos[a] = m; S[m++] = a; for (int j = 0; j < deg[a]; j++) cnt[nbl[(size_t)a * MAXD + j]]++; break; } }
        if (g) fclose(g); fprintf(stderr, "init %d\n", m); }
    while (m < K0) { int best = -1, bc = 1 << 30, ties = 0;
        for (int v = 0; v < n; v++) if (!inS[v]) { if (cnt[v] < bc) { bc = cnt[v]; best = v; ties = 1; } else if (cnt[v] == bc && (rnd() % (++ties)) == 0) best = v; }
        inS[best] = 1; pos[best] = m; S[m++] = best; for (int j = 0; j < deg[best]; j++) cnt[nbl[(size_t)best * MAXD + j]]++; }
    int bestk = 0;
    for (int k = m; k <= KMAX; k++) {
        while (m < k) { int best = -1, bc = 1 << 30, ties = 0;
            for (int v = 0; v < n; v++) if (!inS[v]) { if (cnt[v] < bc) { bc = cnt[v]; best = v; ties = 1; } else if (cnt[v] == bc && (rnd() % (++ties)) == 0) best = v; }
            inS[best] = 1; pos[best] = m; S[m++] = best; for (int j = 0; j < deg[best]; j++) cnt[nbl[(size_t)best * MAXD + j]]++; }
        long fc = 0; for (int i = 0; i < m; i++) fc += cnt[S[i]]; fc /= 2; long bestf = fc; int found = (fc == 0);
        for (long it = 1; it <= ITERS && !found; it++) {
            int u = -1, uc = -1, ties = 0;
            for (int i = 0; i < m; i++) { int v = S[i]; if (tabu[v] > it) continue;
                if (cnt[v] > uc) { uc = cnt[v]; u = v; ties = 1; } else if (cnt[v] == uc && (rnd() % (++ties)) == 0) u = v; }
            if (u < 0) { u = S[rnd() % m]; uc = cnt[u]; }
            int v = -1, vc = 1 << 30; ties = 0;
            for (int w = 0; w < n; w++) { if (inS[w] || w == u) continue; if (tabu[w] > it) continue;
                int c = cnt[w] - (int)ADJ(u, w);
                if (c < vc) { vc = c; v = w; ties = 1; } else if (c == vc && (rnd() % (++ties)) == 0) v = w; }
            if (v < 0) continue;
            int pu = pos[u]; inS[u] = 0; pos[u] = -1; S[pu] = v; pos[v] = pu; inS[v] = 1;
            for (int j = 0; j < deg[u]; j++) cnt[nbl[(size_t)u * MAXD + j]]--;
            for (int j = 0; j < deg[v]; j++) cnt[nbl[(size_t)v * MAXD + j]]++;
            fc += (long)vc - uc;
            tabu[u] = it + 7 + (long)(rnd() % 10); tabu[v] = it + 2 + (long)(rnd() % 4);
            if (fc < bestf) bestf = fc; if (fc == 0) found = 1;
        }
        if (!found) { fprintf(stderr, "k=%d FAILED best conflicts %ld\n", k, bestf); break; }
        bestk = k; char fn[512]; snprintf(fn, sizeof fn, "%s_%d.txt", outp, k);
        FILE *o = fopen(fn, "w"); for (int i = 0; i < m; i++) fprintf(o, "%d\n", id[S[i]]); fclose(o);
        fprintf(stderr, "k=%d found -> %s\n", k, fn);
    }
    printf("bestk %d\n", bestk);
    return 0;
}
