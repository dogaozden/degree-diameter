/* Search for diameter-5 Haar (bi-Cayley) graphs over metacyclic groups G = Z_m x|_lam Z_k.
 *
 * Group: pairs (a, j), a in Z_m, j in Z_k, (a,j)(b,l) = (a + lam^j b, j + l), lam^k = 1 mod m.
 * Graph: vertices G x {A, B}, (g, A) ~ (s g, B) for s in S, |S| = d. d-regular, bipartite.
 * G acts regularly on each side by right multiplication, so the diameter is <= 5 iff
 *   (S^-1 S)^2 = G   (every A vertex within 4 of (e,A))  and
 *   (S S^-1)^2 = G   (every B vertex within 4 of (e,B)).
 * (Odd distances then follow: S (S^-1 S)^2 = G covers B from (e,A), etc.)
 * Cost = number of elements missed by each of the two products. Simulated annealing on S.
 *
 * Usage: haar_search d m k lam seed seconds [outfile]
 * Prints best cost; on cost 0 writes S (as "a j" lines) to outfile.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <time.h>

static int m, k, lam, d, N;
static int *pw, *ipw;        /* lam^j, lam^-j mod m */
static int *stamp, cur = 1;
static int T[4096];

static inline int mul(int g, int h) {
    int a = g / k, j = g % k, b = h / k, l = h % k;
    return ((a + (long)pw[j] * b) % m) * k + (j + l) % k;
}
static inline int inv(int g) {
    int a = g / k, j = g % k;
    int jj = (k - j) % k;
    int aa = (int)((m - ((long)ipw[j] * a) % m) % m);
    return aa * k + jj;
}

static unsigned long long rs;
static inline unsigned long long rnd(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs;
}
static double now(void) {
    struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec;
}

/* misses of (X^-1 Y)^2 where for side A: X = Y = S; side B uses S^-1 */
static int misses(const int *S, int side) {
    int nt = 0;
    cur++;
    for (int i = 0; i < d; i++)
        for (int j = 0; j < d; j++) {
            int t = side == 0 ? mul(inv(S[i]), S[j]) : mul(S[i], inv(S[j]));
            if (stamp[t] != cur) { stamp[t] = cur; T[nt++] = t; }
        }
    cur++;
    int cov = 0;
    for (int i = 0; i < nt; i++)
        for (int j = 0; j < nt; j++) {
            int t = mul(T[i], T[j]);
            if (stamp[t] != cur) { stamp[t] = cur; cov++; }
        }
    return N - cov;
}
static int cost(const int *S) { return misses(S, 0) + misses(S, 1); }

int main(int argc, char **argv) {
    if (argc < 7) { fprintf(stderr, "usage: d m k lam seed seconds [out]\n"); return 1; }
    d = atoi(argv[1]); m = atoi(argv[2]); k = atoi(argv[3]); lam = atoi(argv[4]);
    rs = 0x9E3779B97F4A7C15ULL ^ (unsigned long long)atoll(argv[5]) * 2654435761ULL;
    double secs = atof(argv[6]);
    const char *out = argc > 7 ? argv[7] : NULL;
    N = m * k;
    pw = malloc(sizeof(int) * k); ipw = malloc(sizeof(int) * k);
    pw[0] = 1 % m;
    for (int j = 1; j < k; j++) pw[j] = (int)((long)pw[j - 1] * lam % m);
    if ((long)pw[k - 1] * lam % m != 1 % m) { fprintf(stderr, "lam^k != 1\n"); return 1; }
    for (int j = 0; j < k; j++) ipw[j] = pw[(k - j) % k];
    stamp = calloc(N, sizeof(int));
    int S[64], best[64], bestc = 1 << 30;
    double t0 = now();
    int restarts = 0;
    while (now() - t0 < secs && bestc > 0) {
        restarts++;
        /* random start: distinct elements, S[0] = identity */
        S[0] = 0;
        for (int i = 1; i < d; i++) {
            int ok;
            do { S[i] = rnd() % N; ok = S[i] != 0; for (int j = 1; j < i; j++) if (S[j] == S[i]) ok = 0; } while (!ok);
        }
        int c = cost(S);
        double T0 = 2.0, temp = T0;
        long it = 0, since = 0;
        int runbest = c;
        while (c > 0 && now() - t0 < secs) {
            it++;
            int i = 1 + rnd() % (d - 1);
            int old = S[i], nw;
            int ok;
            do {
                nw = rnd() % N; ok = 1;
                for (int j = 0; j < d; j++) if (S[j] == nw) ok = 0;
            } while (!ok);
            S[i] = nw;
            int c2 = cost(S);
            if (c2 <= c || exp((c - c2) / temp) * 4294967296.0 > (double)(rnd() & 0xffffffffULL)) {
                c = c2;
                if (c < runbest) { runbest = c; since = 0; } else since++;
            } else {
                S[i] = old; since++;
            }
            temp = T0 * exp(-(double)(since % 20000) / 4000.0) + 0.05;
            if (c < bestc) { bestc = c; memcpy(best, S, sizeof(int) * d); }
            if (since > 60000) break;
        }
    }
    printf("d=%d m=%d k=%d lam=%d N=%d n=%d best=%d restarts=%d time=%.1f\n",
           d, m, k, lam, N, 2 * N, bestc, restarts, now() - t0);
    if (bestc == 0 && out) {
        FILE *f = fopen(out, "w");
        fprintf(f, "%d %d %d %d\n", d, m, k, lam);
        for (int i = 0; i < d; i++) fprintf(f, "%d %d\n", best[i] / k, best[i] % k);
        fclose(f);
    }
    return 0;
}
