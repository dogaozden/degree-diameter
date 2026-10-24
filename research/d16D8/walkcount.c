/* walkcount.c: non-backtracking walk counts in the lift of H(q) + t matchings by a cyclic skeleton Z_s
   (jump k moves the skeleton by a_k, flags by 0).  For each source vertex (x,0), count NB walks of length <= D
   (same side) / <= D-1 (other side) to every lift vertex (y, g); report the histogram of these counts (capped).
   A further Z_k-lift on top can cover at most "count" values of Z_k at that target, so the minimum count bounds k.
   Usage: walkcount HEX DESIGN s a_1 .. a_t D nsrc seed     (DESIGN: hexlift2 format; only the matchings are used) */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
static int q, q1, N, V, t, S;
static int *lp, *pl, *Mk;
static uint64_t rs = 88172645463325252ULL;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
int main(int argc, char **argv) {
    FILE *fh = fopen(argv[1], "rb"); int32_t h[3]; if (fread(h, 4, 3, fh) != 3) return 1;
    q = h[0]; N = h[1]; q1 = q + 1; V = 2 * N;
    int32_t *tmp = malloc(4 * (size_t)N * q1); if (fread(tmp, 4, (size_t)N * q1, fh) != (size_t)N * q1) return 1; fclose(fh);
    lp = malloc(sizeof(int) * (size_t)N * q1); pl = malloc(sizeof(int) * (size_t)N * q1); int *cnt = calloc(N, sizeof(int));
    for (size_t i = 0; i < (size_t)N * q1; i++) lp[i] = tmp[i];
    for (int l = 0; l < N; l++) for (int j = 0; j < q1; j++) { int p = lp[(size_t)l * q1 + j]; pl[(size_t)p * q1 + cnt[p]++] = l; }
    FILE *fd = fopen(argv[2], "r"); char line[256]; if (!fgets(line, sizeof line, fd)) return 1;
    int a0, a1, a2, a3; int nh = sscanf(line, "%d %d %d %d", &a0, &a1, &a2, &a3); t = nh == 4 ? a3 : a2;
    Mk = malloc(sizeof(int) * (size_t)t * N);
    for (int p = 0; p < N; p++) {
        int x, y; for (int k = 0; k < t; k++) { if (fscanf(fd, "%d %d", &x, &y) != 2) return 1; Mk[(size_t)k * N + p] = x; }
        for (int j = 0; j < q1; j++) if (fscanf(fd, "%d", &x) != 1) return 1;
    }
    fclose(fd);
    S = atoi(argv[3]); int ai = 4; int *ak = malloc(sizeof(int) * t); for (int k = 0; k < t; k++) ak[k] = atoi(argv[ai++]);
    int D = atoi(argv[ai++]); int nsrc = atoi(argv[ai++]); rs ^= (uint64_t)atoll(argv[ai++]) * 0x9E3779B97F4A7C15ULL;
    int deg = q1 + t; size_t LV = (size_t)V * S;
    /* adjacency of the skeleton lift: vertex id = x*S + g */
    int *nb = malloc(sizeof(int) * LV * deg); int *fill = calloc(LV, sizeof(int));
    for (int p = 0; p < N; p++) for (int g = 0; g < S; g++) {
        size_t u = (size_t)p * S + g;
        for (int j = 0; j < q1; j++) { size_t w = (size_t)(N + pl[(size_t)p * q1 + j]) * S + g; nb[u * deg + fill[u]++] = (int)w; nb[w * deg + fill[w]++] = (int)u; }
        for (int k = 0; k < t; k++) { size_t w = (size_t)(N + Mk[(size_t)k * N + p]) * S + (g + ak[k]) % S; nb[u * deg + fill[u]++] = (int)w; nb[w * deg + fill[w]++] = (int)u; }
    }
    for (size_t u = 0; u < LV; u++) if (fill[u] != deg) { fprintf(stderr, "degree error\n"); return 1; }
    uint32_t *a_prev = calloc(LV, 4), *a_cur = calloc(LV, 4), *a_nxt = calloc(LV, 4), *tot = calloc(LV, 4);
    long hist[2][1026] = {{0}};   /* [same/other side][min(count,65)] */
    for (int si = 0; si < nsrc; si++) {
        int x = (int)(rnd() % V); size_t src = (size_t)x * S;
        memset(a_prev, 0, LV * 4); memset(a_cur, 0, LV * 4); memset(tot, 0, LV * 4);
        a_prev[src] = 1; tot[src] = 1;  /* length 0 */
        for (int j = 0; j < deg; j++) { a_cur[nb[src * deg + j]] += 1; }
        for (size_t u = 0; u < LV; u++) tot[u] += a_cur[u];
        for (int l = 2; l <= D; l++) {
            uint32_t c = (l == 2) ? deg : deg - 1;
            for (size_t u = 0; u < LV; u++) {
                uint64_t s = 0; const int *n = nb + u * deg; for (int j = 0; j < deg; j++) s += a_cur[n[j]];
                int64_t v = (int64_t)s - (int64_t)c * a_prev[u]; if (v < 0) v = 0; if (v > 2000000000) v = 2000000000;
                a_nxt[u] = (uint32_t)v;
            }
            for (size_t u = 0; u < LV; u++) { uint64_t z = (uint64_t)tot[u] + a_nxt[u]; tot[u] = z > 4000000000ULL ? 4000000000U : (uint32_t)z; }
            uint32_t *tp = a_prev; a_prev = a_cur; a_cur = a_nxt; a_nxt = tp;
        }
        for (size_t u = 0; u < LV; u++) {
            int y = (int)(u / S); int same = (y < N) == (x < N);
            uint32_t c = tot[u]; hist[same ? 0 : 1][c > 1025 ? 1025 : c]++;
        }
    }
    printf("q=%d skeleton Z%d shifts", q, S); for (int k = 0; k < t; k++) printf(" %d", ak[k]); printf(" D=%d sources=%d\n", D, nsrc);
    for (int side = 0; side < 2; side++) {
        printf("%s side: count histogram (count: number of targets), counts >= 65 lumped\n", side ? "other" : "same");
        long cum = 0;
        for (int c = 0; c <= 1025; c++) if (hist[side][c]) { cum += hist[side][c]; printf("  %d%s: %ld (cum %ld)\n", c, c == 1025 ? "+" : "", hist[side][c], cum); }
    }
    return 0;
}
