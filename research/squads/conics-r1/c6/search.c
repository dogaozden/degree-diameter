/* Card c6, squad conics-r1.
 * Simulated annealing for a self-polar extension of PG(2,q) by KN=6 new points h_i
 * and their polar lines K_i = theta(h_i), theta = conic polarity of x z = y^2.
 *
 * Unknowns: X[i][L] (h_i on old line L), symmetric Y[i][j] (h_i on K_j = h_j on K_i).
 * Derived: K_i contains old point p iff X[i][ell(p)] = 1, where ell(p) = polar line of p.
 * Cost = (# point pairs with no common line, over the full extended structure)
 *        + lam * (total degree excess over q+2, points and lines).
 * usage: search q iters restarts seed lam T0 T1
 * Prints best cost per restart to stderr; on cost 0 prints one JSON line to stdout and exits.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>

#ifndef KN
#define KN 6
#endif
#define MAXN 64

static int q, N, n;
static int tri[MAXN][3];          /* normalized triples: used both as points and as lines */
static int ell[MAXN];             /* old point p -> index of its polar line */
static int ptOfPole[MAXN];        /* old line L -> index of the old point whose polar is L */
static uint64_t oldmask[MAXN];    /* old point p -> bitmask of old lines through p */
static char X[KN][MAXN];
static char Y[KN][KN];
static uint64_t rs = 88172645463325252ULL;

static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline double urand(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int md(int a) { a %= q; if (a < 0) a += q; return a; }

static int inverse(int a) {
    int r = 1, e = q - 2, b = md(a);
    while (e) { if (e & 1) r = r * b % q; b = b * b % q; e >>= 1; }
    return r;
}

/* index of the normalized triple equal to v (mod q, up to scalar) */
static int find(const int *v) {
    int a[3], i, k, s = 0;
    for (i = 0; i < 3; i++) a[i] = md(v[i]);
    for (i = 0; i < 3; i++) if (a[i]) { s = inverse(a[i]); break; }
    for (k = 0; k < 3; k++) a[k] = a[k] * s % q;
    for (i = 0; i < N; i++)
        if (tri[i][0] == a[0] && tri[i][1] == a[1] && tri[i][2] == a[2]) return i;
    fprintf(stderr, "find failed\n");
    exit(2);
}

static void setup(void) {
    int a, b, c, idx = 0, p, L, i;
    N = q * q + q + 1;
    n = N + KN;
    for (a = 0; a < q; a++)
        for (b = 0; b < q; b++)
            for (c = 0; c < q; c++) {
                int v[3] = {a, b, c}, f = 0;
                for (i = 0; i < 3; i++) if (v[i]) { f = v[i]; break; }
                if (f != 1) continue;
                tri[idx][0] = a; tri[idx][1] = b; tri[idx][2] = c; idx++;
            }
    if (idx != N) { fprintf(stderr, "bad count\n"); exit(2); }
    for (p = 0; p < N; p++) {
        int pole[3] = {tri[p][2], md(-2 * tri[p][1]), tri[p][0]};
        ell[p] = find(pole);
        ptOfPole[ell[p]] = p;
    }
    for (p = 0; p < N; p++) {
        oldmask[p] = 0;
        for (L = 0; L < N; L++) {
            int d = md(tri[p][0] * tri[L][0] + tri[p][1] * tri[L][1] + tri[p][2] * tri[L][2]);
            if (d == 0) oldmask[p] |= 1ULL << L;
        }
    }
    /* sanity: old flags are preserved by theta (self-polarity of the old plane) */
    for (p = 0; p < N; p++)
        for (L = 0; L < N; L++) {
            int f1 = (oldmask[p] >> L) & 1;
            int f2 = (oldmask[ptOfPole[L]] >> ell[p]) & 1;
            if (f1 != f2) { fprintf(stderr, "polarity not self-polar\n"); exit(2); }
        }
}

/* returns nc + lam*ex; nc = point pairs without a common line; ex = degree excess */
static int cost(int lam, int *nc_out, int *ex_out) {
    uint64_t mask[MAXN];
    int p, i, j, L, v, u, nc = 0, ex = 0;
    for (p = 0; p < N; p++) {
        uint64_t m = oldmask[p];
        int Lp = ell[p];
        for (i = 0; i < KN; i++) if (X[i][Lp]) m |= 1ULL << (N + i);
        mask[p] = m;
    }
    for (i = 0; i < KN; i++) {
        uint64_t m = 0;
        int s = 0, t = 0;
        for (L = 0; L < N; L++) if (X[i][L]) { m |= 1ULL << L; s++; }
        for (j = 0; j < KN; j++) if (Y[i][j]) { m |= 1ULL << (N + j); t++; }
        mask[N + i] = m;
        if (s + t > q + 2) ex += s + t - (q + 2);
    }
    for (i = 0; i < KN; i++) {
        u = N + i;
        for (v = 0; v < N; v++) if ((mask[u] & mask[v]) == 0) nc++;
        for (j = i + 1; j < KN; j++) if ((mask[u] & mask[N + j]) == 0) nc++;
    }
    for (p = 0; p < N; p++) {
        int d = __builtin_popcountll(mask[p]);
        if (d > q + 2) ex += d - (q + 2);
    }
    for (L = 0; L < N; L++) {
        int c = 0;
        for (i = 0; i < KN; i++) c += X[i][L];
        if (c > 1) ex += c - 1;   /* old line gets q+1 points plus c new ones */
    }
    *nc_out = nc;
    *ex_out = ex;
    return nc + lam * ex;
}

static void init_state(void) {
    char used[MAXN];
    int i, j, k, s, L;
    memset(X, 0, sizeof X);
    memset(Y, 0, sizeof Y);
    memset(used, 0, sizeof used);
    for (i = 0; i < KN; i++) {
        s = 2 + (int)(rnd() % (uint64_t)(q - 1));
        for (k = 0; k < s; k++) {
            do { L = (int)(rnd() % (uint64_t)N); } while (used[L]);
            used[L] = 1;
            X[i][L] = 1;
        }
    }
    for (i = 0; i < KN; i++)
        for (j = i; j < KN; j++) {
            Y[i][j] = Y[j][i] = (urand() < 0.3);
        }
}

static void print_json(void) {
    int i, j, L;
    printf("{\"card\": \"c6\", \"q\": %d, \"cost\": 0, \"new_points\": %d, \"lines_on_h\": [", q, KN);
    for (i = 0; i < KN; i++) {
        printf("%s[", i ? ", " : "");
        int first = 1;
        for (L = 0; L < N; L++) if (X[i][L]) {
            printf("%s[%d, %d, %d]", first ? "" : ", ", tri[L][0], tri[L][1], tri[L][2]);
            first = 0;
        }
        printf("]");
    }
    printf("], \"Y\": [");
    for (i = 0; i < KN; i++) {
        printf("%s[", i ? ", " : "");
        for (j = 0; j < KN; j++) printf("%s%d", j ? ", " : "", Y[i][j]);
        printf("]");
    }
    printf("]}\n");
}

int main(int argc, char **argv) {
    if (argc < 8) {
        fprintf(stderr, "usage: search q iters restarts seed lam T0 T1\n");
        return 1;
    }
    q = atoi(argv[1]);
    long iters = atol(argv[2]);
    int restarts = atoi(argv[3]);
    uint64_t seed = strtoull(argv[4], 0, 10);
    int lam = atoi(argv[5]);
    double T0 = atof(argv[6]), T1 = atof(argv[7]);
    int r, bestc = 1 << 30;
    rs ^= (seed + 1) * 0x9E3779B97F4A7C15ULL;
    for (r = 0; r < 20; r++) rnd();
    setup();
    for (r = 0; r < restarts; r++) {
        int nc, ex, cur, rbest;
        long it;
        init_state();
        cur = cost(lam, &nc, &ex);
        rbest = cur;
        for (it = 0; it < iters; it++) {
            double T = T0 * pow(T1 / T0, (double)it / (double)iters);
            int a, b, nn, d;
            int type = (urand() < 0.8) ? 0 : 1;
            if (type == 0) {
                a = (int)(rnd() % KN); b = (int)(rnd() % N);
                X[a][b] ^= 1;
            } else {
                a = (int)(rnd() % KN); b = (int)(rnd() % KN);
                Y[a][b] ^= 1;
                if (a != b) Y[b][a] ^= 1;
            }
            nn = cost(lam, &nc, &ex);
            d = nn - cur;
            if (d <= 0 || urand() < exp(-d / T)) {
                cur = nn;
            } else {
                if (type == 0) X[a][b] ^= 1;
                else { Y[a][b] ^= 1; if (a != b) Y[b][a] ^= 1; }
            }
            if (cur < rbest) rbest = cur;
            if (cur < bestc) bestc = cur;
            if (cur == 0) {
                cost(lam, &nc, &ex);
                fprintf(stderr, "restart %d: cost 0 at iter %ld (nc=%d ex=%d)\n", r, it, nc, ex);
                print_json();
                return 0;
            }
        }
        fprintf(stderr, "restart %d: best %d (last cur %d)\n", r, rbest, cur);
    }
    fprintf(stderr, "q=%d best cost over all restarts: %d\n", q, bestc);
    printf("{\"card\": \"c6\", \"q\": %d, \"cost\": null, \"best_cost\": %d}\n", q, bestc);
    return 0;
}
