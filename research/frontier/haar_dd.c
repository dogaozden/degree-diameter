/* haar_dd: annealing search for Haar (bi-Cayley) graphs of diameter D over metacyclic groups.
 *
 * Group G = Z_m x|_r Z_k (r^k = 1 mod m), element (a,j) <-> index a*k + j,
 *   (a,j)(b,l) = (a + r^j b mod m, j + l mod k).        (k = 1 gives the cyclic group Z_m.)
 * Haar graph H(G,S): vertices (g,A), (g,B); edges (g,A) ~ (s g, B), s in S, |S| = d.
 * Right multiplication by G is transitive on each side, so diam = max(ecc(e,A), ecc(e,B)).
 * Cost:
 *   D even: #B-side elements not within D-1 of (e,A)   (A-side from (e,B) is the inverse set; the
 *           same-side condition, distance <= D, is checked at the end);
 *   D odd : #A-side elements not within D-1 of (e,A)  +  #B-side elements not within D-1 of (e,B).
 * Moves: replace one s_i (i >= 1; s_0 = e WLOG) by the best of K random elements; Metropolis on the best.
 *
 * Usage: haar_dd d D m k r seed seconds [K] [outfile]
 * On cost 0 (and full diameter check passing) writes outfile: "d D m k r" then d lines "a j".
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <time.h>
#include <signal.h>

#define MAXD 32
static int d, D, m, k;
static long long r;
static int N;
static int64_t *R;          /* R[j] = r^j mod m */
static int S[MAXD], bestS[MAXD];
static int *fa, *fb;        /* frontier buffers */
static uint32_t *markA, *markB, stampv = 0;

static unsigned long long rs;
static inline unsigned long long rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }

static int *RA;             /* RA[j*m + b] = r^j b mod m */
static int *EA, *EJ;        /* EA[x] = x / k, EJ[x] = x % k */
static inline int mul(int x, int y) {
    int a = EA[x], j = EJ[x], b = EA[y], l = EJ[y];
    int c = a + RA[j * m + b]; if (c >= m) c -= m;
    int t = j + l; if (t >= k) t -= k;
    return c * k + t;
}
static inline int inv(int x) {
    int a = x / k, j = x % k;
    int jj = (k - j) % k;
    int b = (int)((m - (R[jj] * a) % m) % m);
    return b * k + jj;
}
static int Sinv[MAXD];

/* BFS from (e,side0) for `depth` steps; returns number of elements reached on side `target`
 * (target 0 = same side as start, 1 = other side). Left-multiply by s going A->B, by s^-1 going B->A
 * (start side B: the roles swap). */
static int reach(int startB, int depth, int target) {
    stampv += 1;
    if (stampv == 0) { memset(markA, 0, sizeof(uint32_t) * N); memset(markB, 0, sizeof(uint32_t) * N); stampv = 1; }
    uint32_t *mk[2] = { markA, markB };
    int cnt[2] = { 0, 0 };
    int nf = 1; fa[0] = 0;
    int side = startB;            /* side of the frontier: 0 = A, 1 = B */
    mk[side][0] = stampv; cnt[side == startB ? 0 : 1]++;
    for (int step = 0; step < depth; step++) {
        int ns = side ^ 1, nn = 0;
        uint32_t *M = mk[ns];
        const int *T = (side == 0) ? S : Sinv;   /* A->B: g -> s g ; B->A: h -> s^-1 h */
        for (int f = 0; f < nf; f++) {
            int g = fa[f];
            for (int i = 0; i < d; i++) {
                int h = mul(T[i], g);
                if (M[h] != stampv) { M[h] = stampv; fb[nn++] = h; }
            }
        }
        cnt[ns == startB ? 0 : 1] += nn;
        int *tmp = fa; fa = fb; fb = tmp; nf = nn; side = ns;
    }
    return cnt[target];
}

static int cost(void) {
    for (int i = 0; i < d; i++) Sinv[i] = inv(S[i]);
    if (D % 2 == 0) return N - reach(0, D - 1, 1);
    return (N - reach(0, D - 1, 0)) + (N - reach(1, D - 1, 0));
}
static int full_check(void) {
    for (int i = 0; i < d; i++) Sinv[i] = inv(S[i]);
    return reach(0, D, 0) == N && reach(0, D, 1) == N && reach(1, D, 0) == N && reach(1, D, 1) == N;
}
static int used(int x, int skip) {
    for (int i = 0; i < d; i++) if (i != skip && S[i] == x) return 1;
    return 0;
}

static volatile int stop_flag = 0;
static void on_term(int s) { (void)s; stop_flag = 1; }

int main(int argc, char **argv) {
    if (argc < 8) { fprintf(stderr, "usage: haar_dd d D m k r seed seconds [K] [outfile]\n"); return 2; }
    d = atoi(argv[1]); D = atoi(argv[2]); m = atoi(argv[3]); k = atoi(argv[4]); r = atoll(argv[5]);
    rs = 0x9E3779B97F4A7C15ULL ^ ((unsigned long long)atoll(argv[6]) + 1) * 2654435761ULL;
    double secs = atof(argv[7]);
    int K = argc > 8 ? atoi(argv[8]) : 8;
    const char *out = argc > 9 ? argv[9] : NULL;
    signal(SIGTERM, on_term);
    N = m * k;
    R = malloc(sizeof(int64_t) * k);
    R[0] = 1 % m;
    for (int j = 1; j < k; j++) R[j] = (R[j - 1] * (r % m)) % m;
    if ((R[k - 1] * (r % m)) % m != 1 % m) { fprintf(stderr, "r^k != 1 mod m\n"); return 2; }
    RA = malloc(sizeof(int) * (size_t)N); EA = malloc(sizeof(int) * N); EJ = malloc(sizeof(int) * N);
    for (int j = 0; j < k; j++) for (int b = 0; b < m; b++) RA[j * m + b] = (int)((R[j] * b) % m);
    for (int x = 0; x < N; x++) { EA[x] = x / k; EJ[x] = x % k; }
    fa = malloc(sizeof(int) * N); fb = malloc(sizeof(int) * N);
    markA = calloc(N, sizeof(uint32_t)); markB = calloc(N, sizeof(uint32_t));
    /* sanity: associativity on random triples, inverse */
    for (int t = 0; t < 1000; t++) {
        int x = rnd() % N, y = rnd() % N, z = rnd() % N;
        if (mul(mul(x, y), z) != mul(x, mul(y, z)) || mul(x, inv(x)) != 0) { fprintf(stderr, "group error\n"); return 2; }
    }
    S[0] = 0;
    for (int i = 1; i < d; i++) { int x; do x = rnd() % N; while (used(x, i) || x == 0); S[i] = x; }
    int c = cost(), best = c;
    memcpy(bestS, S, sizeof S);
    double t0 = now(), T = 1.5, lastimp = t0, lastprint = t0;
    long long evals = 1, steps = 0;
    fprintf(stderr, "start N=%d cost=%d\n", N, c);
    while (!stop_flag && now() - t0 < secs && best > 0) {
        int i = 1 + rnd() % (d - 1);
        int old = S[i], bx = -1, bc = 1 << 30;
        for (int t = 0; t < K; t++) {
            int x; do x = rnd() % N; while (x == 0 || used(x, i));
            S[i] = x;
            int cc = cost(); evals++;
            if (cc < bc) { bc = cc; bx = x; }
        }
        if (bc <= c || exp((c - bc) / T) > (rnd() % 1000000) / 1e6) { S[i] = bx; c = bc; }
        else S[i] = old;
        steps++;
        if (c < best) { best = c; memcpy(bestS, S, sizeof S); lastimp = now(); }
        /* temperature: slow cooling, reheat after long stagnation */
        T *= 0.9995; if (T < 0.15) T = 0.15;
        if (now() - lastimp > 120) { T = 1.5; memcpy(S, bestS, sizeof S); c = best; lastimp = now(); }
        if (now() - lastprint > 30) {
            fprintf(stderr, "t=%.0f steps=%lld evals=%lld cost=%d best=%d T=%.2f\n", now() - t0, steps, evals, c, best, T);
            lastprint = now();
        }
    }
    memcpy(S, bestS, sizeof S);
    printf("RESULT d=%d D=%d m=%d k=%d r=%lld N=%d best=%d evals=%lld time=%.1f\n", d, D, m, k, r, N, best, evals, now() - t0);
    if (best == 0) {
        int ok = full_check();
        printf("full diameter check: %s\n", ok ? "OK" : "FAIL");
        if (ok && out) {
            FILE *f = fopen(out, "w");
            fprintf(f, "%d %d %d %d %lld\n", d, D, m, k, r);
            for (int i = 0; i < d; i++) fprintf(f, "%d %d\n", S[i] / k, S[i] % k);
            fclose(f);
            printf("wrote %s\n", out);
        }
    }
    return best == 0 ? 0 : 1;
}
