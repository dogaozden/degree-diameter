/* cover_sample: build the (2j+1)-fold polygon cover of a generalized polygon (polygons.py / gh_fast.py format) with
 * random perfect matchings sigma_t over Z_M (voltage 0 on polygon edges, T[t] on sigma_t) and BFS from sampled
 * sources. Z_M acts by translation, so sources in copy 0 suffice; all 2P base vertices are sources if SAMPLES <= 0.
 * Prints the max eccentricity seen and the number of (source, target) pairs beyond D.  (job cell-12-7)
 * usage: cover_sample BASE D M seed SAMPLES T1 .. Tj */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

static uint64_t rs;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }

int main(int argc, char **argv) {
    if (argc < 7) { fprintf(stderr, "usage: cover_sample BASE D M seed SAMPLES T1..Tj\n"); return 1; }
    FILE *f = fopen(argv[1], "r");
    int D = atoi(argv[2]), M = atoi(argv[3]); rs = 0x9E3779B97F4A7C15ULL ^ (uint64_t)atoll(argv[4]) * 2654435761ULL;
    long samples = atol(argv[5]); int j = argc - 6; int *T = malloc(j * sizeof(int));
    for (int t = 0; t < j; t++) T[t] = ((atoi(argv[6 + t]) % M) + M) % M;
    int P; if (fscanf(f, "%d", &P) != 1) return 2;
    /* read lines: count points per line from the first line */
    char buf[4096]; fgets(buf, sizeof buf, f);
    int Q1 = 0, cap = 0; int *lines = NULL;
    for (int k = 0; k < P; k++) {
        if (!fgets(buf, sizeof buf, f)) { fprintf(stderr, "short file\n"); return 2; }
        int vals[64], c = 0; char *s = buf, *e;
        for (;;) { long v = strtol(s, &e, 10); if (e == s) break; vals[c++] = (int)v; s = e; }
        if (k == 0) { Q1 = c; lines = malloc((size_t)P * Q1 * sizeof(int)); cap = Q1; }
        if (c != cap) { fprintf(stderr, "line %d has %d points\n", k, c); return 2; }
        memcpy(lines + (size_t)k * Q1, vals, Q1 * sizeof(int));
    }
    int *thru = malloc((size_t)P * Q1 * sizeof(int)), *tc = calloc(P, sizeof(int));
    for (int k = 0; k < P; k++) for (int i = 0; i < Q1; i++) { int p = lines[(size_t)k * Q1 + i]; thru[(size_t)p * Q1 + tc[p]++] = k; }
    for (int p = 0; p < P; p++) if (tc[p] != Q1) { fprintf(stderr, "point %d on %d lines\n", p, tc[p]); return 2; }
    int *sig = malloc((size_t)j * P * sizeof(int)), *sinv = malloc((size_t)j * P * sizeof(int));
    for (int t = 0; t < j; t++) {
        int *s = sig + (size_t)t * P;
        for (int i = 0; i < P; i++) s[i] = i;
        for (int i = P - 1; i > 0; i--) { int r = rnd() % (i + 1); int x = s[i]; s[i] = s[r]; s[r] = x; }
        for (int i = 0; i < P; i++) sinv[(size_t)t * P + s[i]] = i;
    }
    long NV = 2L * P * M;      /* vertex (x, c) = x*M + c, x < P point, x >= P line P + k */
    int8_t *dist = malloc(NV); int *q = malloc(NV * sizeof(int));
    int maxecc = 0; long beyond = 0, nsrc = 0;
    long total = 2L * P; if (samples <= 0 || samples > total) samples = total;
    for (long si = 0; si < samples; si++) {
        long s = (samples == total) ? si : (long)(rnd() % total);
        memset(dist, -1, NV);
        int qh = 0, qt = 0; long v0 = s * M; dist[v0] = 0; q[qt++] = (int)v0; long reached = 1; int ecc = 0;
        while (qh < qt) {
            int u = q[qh++]; int du = dist[u]; if (du > ecc) ecc = du;
            int x = u / M, c = u % M;
            if (x < P) {
                for (int k = 0; k < Q1; k++) { int w = (P + thru[(size_t)x * Q1 + k]) * M + c; if (dist[w] < 0) { dist[w] = du + 1; q[qt++] = w; reached++; } }
                for (int t = 0; t < j; t++) { int cc = (c + T[t]) % M; int w = (P + sig[(size_t)t * P + x]) * M + cc; if (dist[w] < 0) { dist[w] = du + 1; q[qt++] = w; reached++; } }
            } else {
                int k = x - P;
                for (int i = 0; i < Q1; i++) { int w = lines[(size_t)k * Q1 + i] * M + c; if (dist[w] < 0) { dist[w] = du + 1; q[qt++] = w; reached++; } }
                for (int t = 0; t < j; t++) { int cc = (c - T[t] + M) % M; int w = sinv[(size_t)t * P + k] * M + cc; if (dist[w] < 0) { dist[w] = du + 1; q[qt++] = w; reached++; } }
            }
        }
        if (reached != NV) { printf("source %ld: only %ld of %ld reached\n", s, reached, NV); }
        long far = 0; for (long v = 0; v < NV; v++) if (dist[v] > D) far++;
        beyond += far; if (ecc > maxecc) maxecc = ecc; nsrc++;
    }
    printf("RESULT base %s P %d deg %d M %d j %d vertices %ld sources %ld maxecc %d pairs_beyond_D %ld\n",
           argv[1], P, Q1 + j, M, j, NV, nsrc, maxecc, beyond);
    return 0;
}
