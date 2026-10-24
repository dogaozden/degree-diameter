/* linestar_check.c: scorer for "line-star" sets of H(q) (relaxed surgery, job cell-13-7).
   Input: one star per line, "m s1 s2 ... sk" (line indices of the hexgen file): the lines s_j meet the middle line m
   in k distinct points (s_j != m), 1 <= k <= q.  Valid iff: every s_j meets m, at distinct points; no line is used
   twice; at most q^2 stars; lines of different stars are pairwise opposite (distance 6 in the incidence graph);
   lines of one star are at distance 4 with middle m (automatic).  Score = total number of lines.
   usage: linestar_check HEXFILE FILE */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
int q, N, Q1; int32_t *lp, *pl;
static void ball(int id, int maxd, uint8_t *dist, int32_t *queue) {
    memset(dist, 255, 2 * (size_t)N); int h = 0, t = 0; dist[id] = 0; queue[t++] = id;
    while (h < t) { int x = queue[h++]; if (dist[x] >= maxd) continue;
        const int32_t *nb = (x < N) ? &pl[(size_t)x * Q1] : &lp[(size_t)(x - N) * Q1]; int off = (x < N) ? N : 0;
        for (int k = 0; k < Q1; k++) { int y = nb[k] + off; if (dist[y] == 255) { dist[y] = dist[x] + 1; queue[t++] = y; } } }
}
static int meet(int a, int b) { for (int i = 0; i < Q1; i++) for (int j = 0; j < Q1; j++) if (lp[(size_t)a * Q1 + i] == lp[(size_t)b * Q1 + j]) return lp[(size_t)a * Q1 + i]; return -1; }
int main(int argc, char **argv) {
    if (argc < 3) { fprintf(stderr, "usage: linestar_check HEXFILE FILE\n"); return 2; }
    FILE *f = fopen(argv[1], "rb"); int32_t hdr[3]; if (!f || fread(hdr, 4, 3, f) != 3) return 2; q = hdr[0]; N = hdr[1]; Q1 = q + 1;
    lp = malloc(4L * N * Q1); if (fread(lp, 4, (size_t)N * Q1, f) != (size_t)N * Q1) return 2; fclose(f);
    pl = malloc(4L * N * Q1); int *c = calloc(N, sizeof(int));
    for (int l = 0; l < N; l++) for (int k = 0; k < Q1; k++) { int p = lp[(size_t)l * Q1 + k]; pl[(size_t)p * Q1 + c[p]++] = l; }
    FILE *g = fopen(argv[2], "r"); if (!g) { printf("RESULT INVALID cannot read file\n"); return 1; }
    int *S = malloc(sizeof(int) * N), *star = malloc(sizeof(int) * N), *mid = malloc(sizeof(int) * N); int ns = 0, nst = 0, maxk = 0;
    char buf[4096];
    while (fgets(buf, sizeof buf, g)) {
        if (buf[0] == '#') continue;
        int vals[64], nv = 0; char *p = buf; int v, used;
        while (nv < 64 && sscanf(p, "%d%n", &v, &used) == 1) { vals[nv++] = v; p += used; }
        if (nv == 0) continue;
        if (nv < 2) { printf("RESULT INVALID star without lines\n"); return 1; }
        int m = vals[0], k = nv - 1; if (k > q) { printf("RESULT INVALID star larger than q\n"); return 1; }
        if (m < 0 || m >= N) { printf("RESULT INVALID bad index\n"); return 1; }
        int seen[64], nseen = 0;
        for (int j = 1; j < nv; j++) { int s = vals[j]; if (s < 0 || s >= N || s == m) { printf("RESULT INVALID bad line %d\n", s); return 1; }
            int x = meet(s, m); if (x < 0) { printf("RESULT INVALID line %d does not meet middle %d\n", s, m); return 1; }
            for (int t = 0; t < nseen; t++) if (seen[t] == x) { printf("RESULT INVALID two lines of star %d meet the middle in the same point\n", nst); return 1; }
            seen[nseen++] = x; S[ns] = s; star[ns] = nst; mid[ns] = m; ns++; }
        if (k > maxk) maxk = k; nst++;
    }
    if (nst > q * q) { printf("RESULT INVALID more than q^2 stars\n"); return 1; }
    uint8_t *in = calloc(N, 1); for (int i = 0; i < ns; i++) { if (in[S[i]]) { printf("RESULT INVALID line %d used twice\n", S[i]); return 1; } in[S[i]] = 1; }
    int *who = malloc(sizeof(int) * N); for (int i = 0; i < N; i++) who[i] = -1; for (int i = 0; i < ns; i++) who[S[i]] = i;
    uint8_t *dist = malloc(2L * N); int32_t *queue = malloc(8L * N); long bad = 0;
    for (int i = 0; i < ns; i++) { ball(N + S[i], 4, dist, queue);
        for (int l = 0; l < N; l++) if (dist[N + l] <= 4 && who[l] >= 0 && who[l] != i) {
            int j = who[l];
            if (star[j] != star[i]) bad++;
            else if (dist[N + l] != 4) bad++;
        } }
    if (bad) { printf("%ld close pairs across stars\nRESULT INVALID linestars\n", bad / 2); return 1; }
    printf("RESULT VALID linestars %d stars %d maxk %d\n", ns, nst, maxk);
    return 0;
}
