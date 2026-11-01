/* Independent checker for Haar graphs on Z_m x|_r Z_k (x Z_1), from haar_gen3 solution files.
   Element x = a*k + j means (a,j); (a,j)(b,l) = (a + r^j b mod m, j+l mod k).
   Haar graph: A_g ~ B_{s g} for s in S (2N vertices). Right mult by G is an automorphism, so
   eccentricities of A_e and B_e give the diameter; we also BFS from random sources as a sanity check. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
static long long M, K, R_[100000], RR;
static inline long mul(long x, long y) {
    long a = x / K, j = x % K, b = y / K, l = y % K;
    long c = (a + R_[j] * b) % M;
    return c * K + (j + l) % K;
}
static long N;
static long S[64], SI[64];
static int d;
static uint8_t *dist;
static long *queue;
static int bfs(long src, int *reached) {
    /* vertices 0..N-1: A side, N..2N-1: B side */
    long n2 = 2 * N;
    memset(dist, 255, n2);
    long qh = 0, qt = 0; queue[qt++] = src; dist[src] = 0;
    int ecc = 0;
    while (qh < qt) {
        long v = queue[qh++];
        int dv = dist[v];
        if (v < N) { /* A_g -> B_{s g} */
            long g = v;
            for (int i = 0; i < d; i++) {
                long w = N + mul(S[i], g);
                if (dist[w] == 255) { dist[w] = dv + 1; if (dv + 1 > ecc) ecc = dv + 1; queue[qt++] = w; }
            }
        } else { /* B_h -> A_{s^-1 h} */
            long h = v - N;
            for (int i = 0; i < d; i++) {
                long w = mul(SI[i], h);
                if (dist[w] == 255) { dist[w] = dv + 1; if (dv + 1 > ecc) ecc = dv + 1; queue[qt++] = w; }
            }
        }
    }
    *reached = (int)qt;
    return ecc;
}
int main(int argc, char **argv) {
    if (argc < 3) { fprintf(stderr, "usage: check_meta SOL NSAMPLES\n"); return 2; }
    FILE *f = fopen(argv[1], "r"); if (!f) { perror("open"); return 2; }
    int nsamp = atoi(argv[2]);
    char line[4096];
    if (!fgets(line, sizeof line, f)) return 2;
    int D0, dd; char tag[16]; long long m, k, r, n, NN;
    if (sscanf(line, "%d %d %15s %lld %lld %lld n %lld N %lld", &dd, &D0, tag, &m, &k, &r, &n, &NN) != 8) { fprintf(stderr, "bad header\n"); return 2; }
    if (strcmp(tag, "meta") || n != 1) { fprintf(stderr, "only meta x Z_1 handled\n"); return 2; }
    M = m; K = k; N = M * K; if (N != NN) { fprintf(stderr, "N mismatch %ld vs %lld\n", N, NN); return 2; }
    R_[0] = 1 % M; for (long j = 1; j < K; j++) R_[j] = (R_[j - 1] * r) % M;
    if ((R_[K - 1] * r) % M != 1 % M) { fprintf(stderr, "r^k != 1\n"); return 2; }
    d = dd; if (d > 64) return 2;
    for (int i = 0; i < d; i++) {
        long x; if (!fgets(line, sizeof line, f)) { fprintf(stderr, "short file\n"); return 2; }
        if (sscanf(line, "%ld", &x) != 1 || x < 0 || x >= N) { fprintf(stderr, "bad element\n"); return 2; }
        S[i] = x;
    }
    fclose(f);
    /* distinct */
    for (int i = 0; i < d; i++) for (int j = i + 1; j < d; j++) if (S[i] == S[j]) { printf("duplicate generator\n"); return 1; }
    /* inverses */
    for (int i = 0; i < d; i++) {
        int found = 0;
        for (long y = 0; y < N; y++) if (mul(S[i], y) == 0) { SI[i] = y; found = 1; break; }
        if (!found) { printf("no inverse\n"); return 1; }
    }
    dist = malloc(2 * N); queue = malloc(sizeof(long) * 2 * N);
    if (!dist || !queue) return 2;
    int reached; int worst = 0; int ok = 1;
    int e1 = bfs(0, &reached); /* A_e */
    printf("N=%ld Delta=%d  ecc(A_e)=%d reached=%d/%ld\n", N, d, e1, reached, 2 * N);
    if (reached != 2 * N) ok = 0;
    if (e1 > worst) worst = e1;
    int e2 = bfs(N, &reached); /* B_e */
    printf("ecc(B_e)=%d reached=%d\n", e2, reached);
    if (reached != 2 * N) ok = 0;
    if (e2 > worst) worst = e2;
    srand(12345);
    for (int t = 0; t < nsamp; t++) {
        long s = ((long)rand() * RAND_MAX + rand()) % (2 * N);
        int ec = bfs(s, &reached);
        if (reached != 2 * N) ok = 0;
        if (ec > worst) worst = ec;
    }
    printf("max ecc over sampled sources = %d (sources: A_e, B_e, %d random)\n", worst, nsamp);
    printf("VERDICT: %s diameter=%d  vertices=%ld\n", (ok && worst <= D0) ? "OK" : "FAIL", worst, 2 * N);
    return (ok && worst <= D0) ? 0 : 1;
}
