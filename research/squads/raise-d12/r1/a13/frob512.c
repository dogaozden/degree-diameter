/* a13b: Haar graphs H(G,S) on G = F_512^+ x| C_73 (Frobenius, kernel F_512, C_73 = <zeta^7> in F_512^*),
 * alpha(v,j) = (v^8, 8j mod 73): order-3 automorphism, Fix = F_8 x {0} (8 elements).
 * S = {e, x, alpha x, alpha^2 x}, exhaustive over x. Same BFS and hole counts as a13.c (U1 = B-holes from (e,A)).
 * Usage: frob512 start count [random_trials seed]   (mode random if trials > 0)
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#define NF 512
#define K 73
#define N (NF * K)
static int expt[2 * NF], logt[NF];
static int pw7[K];
static uint8_t *dist; static int *q;
static int S[4], Sinv[4];
static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }

static int fmul(int a, int b) { if (!a || !b) return 0; return expt[logt[a] + logt[b]]; }
static inline int gmul(int g1, int g2) {
    int v1 = g1 / K, j1 = g1 % K, v2 = g2 / K, j2 = g2 % K;
    int v = v1 ^ fmul(pw7[j1], v2);
    int j = (j1 + j2) % K;
    return v * K + j;
}
static int ginv(int g) {
    int v = g / K, j = g % K;
    int jinv = (K - j) % K;
    int vi = fmul(pw7[jinv], v);
    return vi * K + jinv;
}
static inline int galpha(int g) {
    int v = g / K, j = g % K;
    int v8 = 0;
    if (v) { int l = logt[v]; v8 = expt[(8 * l) % 511]; }
    return v8 * K + (8 * j) % K;
}

static int holes(int src) {
    memset(dist, 255, 2 * N);
    int head = 0, tail = 0;
    q[tail++] = src; dist[src] = 0;
    while (head < tail) {
        int v = q[head++]; int d = dist[v];
        if (d >= 11) continue;
        if (v < N) {
            for (int i = 0; i < 4; i++) { int w = N + gmul(S[i], v); if (dist[w] == 255) { dist[w] = d + 1; q[tail++] = w; } }
        } else {
            int y = v - N;
            for (int i = 0; i < 4; i++) { int w = gmul(Sinv[i], y); if (dist[w] == 255) { dist[w] = d + 1; q[tail++] = w; } }
        }
    }
    int lo = (src < N) ? N : 0, hi = (src < N) ? 2 * N : N, cnt = 0;
    for (int v = lo; v < hi; v++) if (dist[v] == 255) cnt++;
    return cnt;
}
static void setS(int x) {
    S[0] = 0; S[1] = x; S[2] = galpha(x); S[3] = galpha(S[2]);
    for (int i = 0; i < 4; i++) Sinv[i] = ginv(S[i]);
}

int main(int argc, char **argv) {
    long start = atol(argv[1]), count = atol(argv[2]);
    long trials = argc > 3 ? atol(argv[3]) : 0;
    if (argc > 4) rs ^= (uint64_t)atol(argv[4]) * 2654435761ULL;
    int poly = (1 << 9) | (1 << 4) | 1;
    int e = 1;
    for (int i = 0; i < 511; i++) { expt[i] = e; expt[i + 511] = e; e <<= 1; if (e & 512) e ^= poly; }
    for (int i = 0; i < 511; i++) logt[expt[i]] = i;
    int primitive = 1; for (int i = 1; i < 511; i++) if (expt[i] == 1) { primitive = 0; break; }
    if (!primitive || expt[511] != 1) { fprintf(stderr, "x not primitive\n"); return 1; }
    for (int j = 0; j < K; j++) pw7[j] = expt[(7 * j) % 511];
    dist = malloc(2 * N); q = malloc(sizeof(int) * 2 * N);
    {
        int bad = 0, fix = 0;
        for (int t = 0; t < 20000; t++) {
            int g = rnd() % N, h = rnd() % N, k = rnd() % N;
            if (gmul(gmul(g, h), k) != gmul(g, gmul(h, k))) bad++;
            if (gmul(g, ginv(g)) != 0) bad++;
            if (galpha(gmul(g, h)) != gmul(galpha(g), galpha(h))) bad++;
        }
        for (int g = 1; g < N; g++) { if (galpha(g) == g) fix++; if (galpha(galpha(galpha(g))) != g) bad++; }
        fprintf(stderr, "N=%d 2N=%d sanity bad=%d fixed_nonidentity=%d\n", N, 2 * N, bad, fix);
        if (bad) return 2;
    }
    if (trials == 0) {
        long hist[64] = {0}, tested = 0, hits = 0; int bestU = 1 << 30; long bestx = -1;
        long end = start + count; if (end > N) end = N;
        for (long x = (start < 1 ? 1 : start); x < end; x++) {
            setS((int)x); int U1 = holes(0); tested++;
            if (U1 < 64) hist[U1]++;
            if (U1 < bestU) { bestU = U1; bestx = x; }
            if (U1 == 0) { int U2 = holes(N); printf("U1=0 x=%ld S=%d %d %d %d U2=%d\n", x, S[0], S[1], S[2], S[3], U2); fflush(stdout); if (!U2) hits++; }
        }
        printf("tested=%ld best_U1=%d at x=%ld hits=%ld\nhist:", tested, bestU, bestx, hits);
        for (int i = 0; i < 64; i++) if (hist[i]) printf(" %d:%ld", i, hist[i]);
        printf("\n");
    } else {
        long hist[256] = {0}; int bestU = 1 << 30;
        for (long t = 0; t < trials; t++) {
            int a[3];
            for (int i = 0; i < 3; i++) { int ok; do { a[i] = 1 + rnd() % (N - 1); ok = 1; for (int j = 0; j < i; j++) if (a[j] == a[i]) ok = 0; } while (!ok); }
            S[0] = 0; S[1] = a[0]; S[2] = a[1]; S[3] = a[2];
            for (int i = 0; i < 4; i++) Sinv[i] = ginv(S[i]);
            int U1 = holes(0); if (U1 < 256) hist[U1]++; if (U1 < bestU) bestU = U1;
        }
        printf("random trials=%ld best_U1=%d hist:", trials, bestU);
        for (int i = 0; i < 256; i++) if (hist[i]) printf(" %d:%ld", i, hist[i]);
        printf("\n");
    }
    return 0;
}
