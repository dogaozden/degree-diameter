/* nbwx.c: in the C-copy compound X (H(q) copies + r random bijections with shifts s_j, as in x2s.c, no symmetry),
 * for sampled sources v, the base distance d(v,w) and the number of reduced walks v -> w of length exactly d, and of
 * length <= D with the parity of d. Prints the minimum and the smallest values seen per distance.
 * Usage: nbwx HEX.bin C r s_1..s_r D nsrc seed */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
int main(int argc, char **argv) {
    int ai = 1; const char *hexp = argv[ai++]; int C = atoi(argv[ai++]), R = atoi(argv[ai++]), S[8];
    for (int j = 0; j < R; j++) S[j] = atoi(argv[ai++]);
    int D = atoi(argv[ai++]), nsrc = atoi(argv[ai++]); rs ^= atoll(argv[ai++]) * 0x9E3779B97F4A7C15ULL;
    FILE *f = fopen(hexp, "rb"); int q, N, Lc;
    if (fread(&q, 4, 1, f) != 1 || fread(&N, 4, 1, f) != 1 || fread(&Lc, 4, 1, f) != 1) return 2;
    int *lp = malloc(sizeof(int) * N * (q + 1)); if (fread(lp, 4, (size_t)N * (q + 1), f) != (size_t)N * (q + 1)) return 2; fclose(f);
    int DEG = q + 1 + R, NV = C * 2 * N; int *nb = malloc(sizeof(int) * (size_t)NV * DEG), *dg = calloc(NV, sizeof(int));
#define ADD(a, b) do { int a_ = (a), b_ = (b); nb[(size_t)a_ * DEG + dg[a_]++] = b_; nb[(size_t)b_ * DEG + dg[b_]++] = a_; } while (0)
    int *sig = malloc(sizeof(int) * N * R);
    for (int j = 0; j < R; j++) { int *p = sig + j * N; for (int i = 0; i < N; i++) p[i] = i; for (int i = N - 1; i > 0; i--) { int z = rnd() % (i + 1), t = p[i]; p[i] = p[z]; p[z] = t; } }
    for (int c = 0; c < C; c++) {
        for (int l = 0; l < N; l++) for (int i = 0; i <= q; i++) ADD(c * 2 * N + lp[l * (q + 1) + i], c * 2 * N + N + l);
        for (int j = 0; j < R; j++) for (int p = 0; p < N; p++) ADD(c * 2 * N + p, ((c + S[j]) % C) * 2 * N + N + sig[j * N + p]);
    }
    int *rev = malloc(sizeof(int) * (size_t)NV * DEG);
    for (int x = 0; x < NV; x++) for (int j = 0; j < DEG; j++) { int y = nb[(size_t)x * DEG + j], kth = 0; for (int t = 0; t < j; t++) if (nb[(size_t)x * DEG + t] == y) kth++;
        int jj; for (jj = 0; jj < DEG; jj++) if (nb[(size_t)y * DEG + jj] == x && kth-- == 0) break; rev[(size_t)x * DEG + j] = jj; }
    int64_t *cur = malloc(8 * (size_t)NV * DEG), *nxt = malloc(8 * (size_t)NV * DEG), *Wd = malloc(8 * NV), *Wle = malloc(8 * NV);
    int *dist = malloc(sizeof(int) * NV);
    int64_t mnd[16], mnle[16]; long cntd[16]; for (int i = 0; i < 16; i++) { mnd[i] = mnle[i] = INT64_MAX; cntd[i] = 0; }
    static long hd[16][64], hl[16][256];
    for (int s = 0; s < nsrc; s++) {
        int v0 = s == 0 ? 0 : (s == 1 ? N : (int)(rnd() % (2 * N))); /* copy-0 sources */
        for (int x = 0; x < NV; x++) { dist[x] = -1; Wd[x] = 0; Wle[x] = 0; }
        dist[v0] = 0; Wd[v0] = 1;
        memset(cur, 0, 8 * (size_t)NV * DEG);
        for (int j = 0; j < DEG; j++) cur[(size_t)v0 * DEG + j] = 1;
        for (int len = 1; len <= D; len++) {
            memset(nxt, 0, 8 * (size_t)NV * DEG);
            for (int x = 0; x < NV; x++) for (int j = 0; j < DEG; j++) { int64_t c = cur[(size_t)x * DEG + j]; if (!c) continue;
                int y = nb[(size_t)x * DEG + j];
                if (dist[y] < 0) dist[y] = len;
                if (dist[y] == len) Wd[y] += c;
                if ((len - dist[y]) % 2 == 0) Wle[y] += c;
                if (len < D) { int r = rev[(size_t)x * DEG + j]; for (int k = 0; k < DEG; k++) if (k != r) nxt[(size_t)y * DEG + k] += c; } }
            int64_t *t = cur; cur = nxt; nxt = t;
        }
        for (int w = 0; w < NV; w++) { if (w == v0) continue; int d = dist[w]; if (d < 0) { printf("unreached within D\n"); continue; }
            cntd[d]++; if (Wd[w] < mnd[d]) mnd[d] = Wd[w]; if (Wle[w] < mnle[d]) mnle[d] = Wle[w];
            hd[d][Wd[w] < 63 ? Wd[w] : 63]++; hl[d][Wle[w] < 255 ? Wle[w] : 255]++; }
    }
    printf("q=%d C=%d r=%d D=%d sources=%d\n", q, C, R, D, nsrc);
    for (int d = 1; d <= D; d++) if (cntd[d]) {
        printf("dist %d: %ld pairs; geodesics min %lld", d, cntd[d], (long long)mnd[d]);
        int shown = 0; for (int b = 0; b < 64 && shown < 4; b++) if (hd[d][b]) { printf(" [%d:%.3f%%]", b, 100.0 * hd[d][b] / cntd[d]); shown++; }
        printf("; walks<=D min %lld", (long long)mnle[d]); shown = 0;
        for (int b = 0; b < 256 && shown < 3; b++) if (hl[d][b]) { printf(" [%d:%.3f%%]", b, 100.0 * hl[d][b] / cntd[d]); shown++; }
        printf("\n");
    }
    return 0;
}
