/* a13: Haar graphs H(G,S), G = Heis(F_p) x A (nilpotent, class 2), D = 12.
 * alpha(a,b,c) = (w a, w b, w^2 c) on Heis(F_p), alpha_A on abelian A (fpf). Scan S = {e, x, ax, a^2x} exhaustively.
 * U1 = #B-vertices not within 11 of (e,A); U2 = #A-vertices not within 11 of (e,B) (computed only if U1 == 0).
 * Usage: a13 A P mode start count seed
 *   A in {z103, f4sq, z4sq}; mode 0 = orbit scan over x in [start,start+count); mode 1 = random S (count trials).
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

static int P, NA, N, OM;
static int addA[128][128], negA[128], alphaA[128];
static uint8_t *dist;
static int *q;
static int S[4], Sinv[4];

static int hmul(int h1, int h2) {
    int a1 = h1 / (P * P), b1 = (h1 / P) % P, c1 = h1 % P;
    int a2 = h2 / (P * P), b2 = (h2 / P) % P, c2 = h2 % P;
    int a = (a1 + a2) % P, b = (b1 + b2) % P, c = (c1 + c2 + a1 * b2) % P;
    return a * P * P + b * P + c;
}
static int hinv(int h) {
    int a = h / (P * P), b = (h / P) % P, c = h % P;
    int na = (P - a) % P, nb = (P - b) % P, nc = ((-c + a * b) % P + P) % P;
    return na * P * P + nb * P + nc;
}
static int halpha(int h) {
    int a = h / (P * P), b = (h / P) % P, c = h % P;
    int a2 = OM * a % P, b2 = OM * b % P, c2 = (OM * OM % P) * c % P;
    return a2 * P * P + b2 * P + c2;
}
static inline int gmul(int g1, int g2) {
    return hmul(g1 / NA, g2 / NA) * NA + addA[g1 % NA][g2 % NA];
}
static inline int ginv(int g) { return hinv(g / NA) * NA + negA[g % NA]; }
static inline int galpha(int g) { return halpha(g / NA) * NA + alphaA[g % NA]; }

/* BFS from src (0..N-1 = A-side, N..2N-1 = B-side), depth <= 11; return # opposite-side nodes not reached. */
static int holes(int src) {
    memset(dist, 255, 2 * N);
    int head = 0, tail = 0;
    q[tail++] = src; dist[src] = 0;
    while (head < tail) {
        int v = q[head++]; int d = dist[v];
        if (d >= 11) continue;
        if (v < N) {
            for (int i = 0; i < 4; i++) {
                int w = N + gmul(S[i], v);
                if (dist[w] == 255) { dist[w] = d + 1; q[tail++] = w; }
            }
        } else {
            int y = v - N;
            for (int i = 0; i < 4; i++) {
                int w = gmul(Sinv[i], y);
                if (dist[w] == 255) { dist[w] = d + 1; q[tail++] = w; }
            }
        }
    }
    if (getenv("LAYERS")) {
        long L[13] = {0};
        for (int v = 0; v < 2 * N; v++) if (dist[v] != 255) L[dist[v]]++;
        for (int d = 0; d <= 11; d++) fprintf(stderr, "%ld ", L[d]);
        fprintf(stderr, "\n");
    }
    if (getenv("COMP")) {
        long ra = 0, rb = 0;
        for (int v = 0; v < 2 * N; v++) if (dist[v] != 255) { if (v < N) ra++; else rb++; }
        fprintf(stderr, "reached A=%ld B=%ld\n", ra, rb);
    }
    int lo = (src < N) ? N : 0, hi = (src < N) ? 2 * N : N, cnt = 0;
    for (int v = lo; v < hi; v++) if (dist[v] == 255) cnt++;
    return cnt;
}

static uint64_t rs;
static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }

static void setS(int x, int y, int z, int w) { S[0] = 0; S[1] = x; S[2] = y; S[3] = z; (void)w; }
static void invS(void) { for (int i = 0; i < 4; i++) Sinv[i] = ginv(S[i]); }

static int save_solution(const char *fn, int U1, int U2) {
    FILE *f = fopen(fn, "w");
    if (!f) return 0;
    fprintf(f, "# a13 Haar H(G,S), G = Heis(F_%d) x A (A code %d), N=%d, 2N=%d, S=%d %d %d %d, U1=%d U2=%d\n",
            P, NA, N, 2 * N, S[0], S[1], S[2], S[3], U1, U2);
    fclose(f);
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 7) { fprintf(stderr, "usage: a13 A P mode start count seed\n"); return 1; }
    const char *Aname = argv[1];
    P = atoi(argv[2]);
    int mode = atoi(argv[3]);
    long start = atol(argv[4]), count = atol(argv[5]);
    rs = 88172645463325252ULL ^ (uint64_t)atol(argv[6]) * 2654435761ULL;
    /* abelian factor */
    if (!strcmp(Aname, "z103")) {
        NA = 103;
        for (int a = 0; a < NA; a++) for (int b = 0; b < NA; b++) addA[a][b] = (a + b) % NA;
        for (int g = 2; g < NA; g++) { /* cube root of unity */
            long w = 1; for (int k = 0; k < (NA - 1) / 3; k++) w = w * g % NA;
            if (w != 1) { OM = 0; alphaA[0] = 0; for (int a = 0; a < NA; a++) alphaA[a] = (int)(w * a % NA); break; }
        }
    } else if (!strcmp(Aname, "f4sq")) {
        NA = 16;
        for (int a = 0; a < NA; a++) for (int b = 0; b < NA; b++) addA[a][b] = a ^ b;
        for (int a = 0; a < NA; a++) {
            int c0 = a & 1, c1 = (a >> 1) & 1, d0 = (a >> 2) & 1, d1 = (a >> 3) & 1;
            int e0 = c1, e1 = c0 ^ c1, f0 = d1, f1 = d0 ^ d1;
            alphaA[a] = e0 | (e1 << 1) | (f0 << 2) | (f1 << 3);
        }
    } else if (!strcmp(Aname, "z4sq")) {
        NA = 16;
        for (int a = 0; a < NA; a++) for (int b = 0; b < NA; b++)
            addA[a][b] = ((a % 4 + b % 4) % 4) + 4 * (((a / 4) + (b / 4)) % 4);
        for (int a = 0; a < NA; a++) {
            int x = a % 4, y = a / 4;
            int x2 = (4 - y) % 4, y2 = ((x - y) % 4 + 4) % 4;
            alphaA[a] = x2 + 4 * y2;
        }
    } else { fprintf(stderr, "bad A\n"); return 1; }
    for (int a = 0; a < NA; a++) for (int b = 0; b < NA; b++) if (addA[a][b] == 0) negA[a] = b;
    /* cube root of unity mod P */
    OM = 0;
    for (int g = 2; g < P && !OM; g++) {
        long w = 1; for (int k = 0; k < (P - 1) / 3; k++) w = w * g % P;
        if (w != 1) OM = (int)w;
    }
    N = P * P * P * NA;
    dist = malloc(2 * N); q = malloc(sizeof(int) * 2 * N);
    if (!dist || !q) { fprintf(stderr, "oom\n"); return 1; }

    /* sanity: alpha automorphism of order 3, fpf; group associativity on random triples */
    {
        int bad = 0, fix = 0;
        for (int t = 0; t < 20000; t++) {
            int g = rnd() % N, h = rnd() % N;
            if (galpha(gmul(g, h)) != gmul(galpha(g), galpha(h))) bad++;
            int k = rnd() % N;
            if (gmul(gmul(g, h), k) != gmul(g, gmul(h, k))) bad++;
            if (gmul(g, ginv(g)) != 0) bad++;
        }
        for (int g = 1; g < N; g++) { if (galpha(g) == g) fix++; if (galpha(galpha(galpha(g))) != g) bad++; }
        fprintf(stderr, "N=%d 2N=%d OM=%d sanity bad=%d fixed_nonidentity=%d\n", N, 2 * N, OM, bad, fix);
        if (bad) return 2;
    }

    if (mode == 0) {
        long hist[64] = {0}; long hit = 0, tested = 0; int bestU = 1 << 30; long bestx = -1;
        long end = start + count; if (end > N) end = N;
        for (long x = (start < 1 ? 1 : start); x < end; x++) {
            int a1 = (int)x, a2 = galpha(a1), a3 = galpha(a2);
            setS(a1, a2, a3, 0);
            invS();
            int U1 = holes(0);  /* src = (e,A) */
            tested++;
            if (U1 < 64) hist[U1]++;
            if (U1 < bestU) { bestU = U1; bestx = x; }
            if (U1 == 0) {
                int U2 = holes(N);
                printf("U1=0 x=%ld S=%d %d %d %d U2=%d\n", x, S[0], S[1], S[2], S[3], U2);
                fflush(stdout);
                if (U2 == 0) {
                    char fn[256]; sprintf(fn, "sol_%s_p%d_x%ld.txt", Aname, P, x);
                    save_solution(fn, 0, 0);
                    hit++;
                }
            }
        }
        printf("tested=%ld best_U1=%d at x=%ld hits=%ld\nhist:", tested, bestU, bestx, hit);
        for (int i = 0; i < 64; i++) if (hist[i]) printf(" %d:%ld", i, hist[i]);
        printf("\n");
    } else {
        /* random 4-sets containing e, no orbit structure */
        long hist[256] = {0}; int bestU = 1 << 30; long trials = count;
        for (long t = 0; t < trials; t++) {
            int a[3];
            for (int i = 0; i < 3; i++) {
                int ok;
                do { a[i] = 1 + rnd() % (N - 1); ok = 1;
                     for (int j = 0; j < i; j++) if (a[j] == a[i]) ok = 0;
                } while (!ok);
            }
            setS(a[0], a[1], a[2], 0); invS();
            int U1 = holes(0);
            if (U1 < 256) hist[U1]++;
            if (U1 < bestU) bestU = U1;
        }
        long sum = 0, n = 0;
        printf("random trials=%ld best_U1=%d hist:", trials, bestU);
        for (int i = 0; i < 256; i++) if (hist[i]) { printf(" %d:%ld", i, hist[i]); sum += (long)i * hist[i]; n += hist[i]; }
        printf("\n");
    }
    return 0;
}
