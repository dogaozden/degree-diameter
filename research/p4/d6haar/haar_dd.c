/* Annealing search for Haar graphs of diameter <= D, for any D >= 3 (copied in spirit from research/d5/haar_search3.c).
 *
 * Haar graph H(G, S): vertices G x {A, B}, edges (g, A) ~ (s g, B) for s in S, |S| = d. Right multiplication is an
 * automorphism that is transitive on each side, so only distances from (e, A) and (e, B) matter. With T = S^-1 S and
 * U = S S^-1 (both closed under inverses, both contain e):
 *   D = 2k   : diameter <= D  iff  S T^(k-1) = G               (one condition; it implies T^k = G = U^k)
 *   D = 2k+1 : diameter <= D  iff  T^k = G and U^k = G         (the odd condition S T^k = G follows)
 * Cost = number of elements of G missed by these sets (summed over the two sides when D is odd).
 *
 * Group: G = G0 x Z_c, G0 read from a multiplication table (groups.py format: N0, then N0 rows; identity = 0).
 * Element index x = g * c + z. Every product set is computed with dedup (stamp array), so one evaluation costs about
 * sum_j |X_j| |T| multiplications, where X_j are the partial products (e.g. D = 7: |T| + |T^2| |T| per side).
 *
 * Usage: haar_dd D d table c seed seconds [outfile|-] [K]
 *        haar_dd check D d table c seed        (cost vs. brute-force BFS on the graph, random S)
 *        haar_dd eval D d table c x1 .. xd     (cost and BFS diameter of a given S)
 * On cost 0 writes: "D d N c table" then d lines "x" (x = element index in G0 x Z_c).
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <time.h>

#define MAXD 24

static int D, d, N, N0, C;
static uint16_t *MT0;   /* MT0[g*N0 + h] */
static int *IT0;
static int *bg, *bz;    /* x -> (g, z) */
static int *stamp, cur = 1;
static int *bufA, *bufB;
static int S[MAXD], best[MAXD];
static long long evals;

static inline int mul(int x, int y) {
    int z = bz[x] + bz[y];
    if (z >= C) z -= C;
    return MT0[bg[x] * N0 + bg[y]] * C + z;
}
static inline int inv(int x) {
    int z = bz[x] ? C - bz[x] : 0;
    return IT0[bg[x]] * C + z;
}

static unsigned long long rs;
static inline unsigned long long rnd(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs;
}
static double now(void) {
    struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec;
}

/* out = distinct elements of X * Y (|X| = nx, |Y| = ny); returns the count */
static int prodset(const int *X, int nx, const int *Y, int ny, int *out) {
    int n = 0;
    cur++;
    for (int i = 0; i < nx; i++)
        for (int j = 0; j < ny; j++) {
            int t = mul(X[i], Y[j]);
            if (stamp[t] != cur) { stamp[t] = cur; out[n++] = t; }
        }
    return n;
}

/* T = S^-1 S (side 0) or S S^-1 (side 1), deduplicated */
static int pairset(const int *X, int side, int *out) {
    int n = 0;
    cur++;
    for (int i = 0; i < d; i++)
        for (int j = 0; j < d; j++) {
            int t = side == 0 ? mul(inv(X[i]), X[j]) : mul(X[i], inv(X[j]));
            if (stamp[t] != cur) { stamp[t] = cur; out[n++] = t; }
        }
    return n;
}

/* number of elements of T^k (k >= 1) */
static int power_size(const int *T, int nt, int k) {
    int n = nt;
    int *A = bufA, *B = bufB;
    memcpy(A, T, sizeof(int) * nt);
    for (int j = 1; j < k; j++) {
        n = prodset(A, n, T, nt, B);
        int *t = A; A = B; B = t;
        if (n == N) break;
    }
    return n;
}

static int cost(const int *X) {
    static int T[MAXD * MAXD];
    if (D % 2 == 0) {
        int k = D / 2;
        int nt = pairset(X, 0, T);
        if (k == 1) return N - d;
        /* S T^(k-1): compute T^(k-1) into bufA, then S * that */
        int n = nt;
        int *A = bufA, *B = bufB;
        memcpy(A, T, sizeof(int) * nt);
        for (int j = 1; j < k - 1; j++) {
            n = prodset(A, n, T, nt, B);
            int *t = A; A = B; B = t;
        }
        n = prodset(X, d, A, n, B);
        return N - n;
    } else {
        int k = D / 2, c = 0;
        for (int side = 0; side < 2; side++) {
            int nt = pairset(X, side, T);
            c += N - power_size(T, nt, k);
        }
        return c;
    }
}

/* brute-force: BFS on the Haar graph, return max eccentricity (or 1e9 if disconnected) */
static int bfs_diam(const int *X) {
    int n = 2 * N, diam = 0;
    int *dist = malloc(sizeof(int) * n), *q = malloc(sizeof(int) * n);
    int Xi[MAXD];
    for (int i = 0; i < d; i++) Xi[i] = inv(X[i]);
    for (int src = 0; src < 2; src++) {   /* (e, A) and (e, B) suffice */
        for (int v = 0; v < n; v++) dist[v] = -1;
        int s0 = src * N, h = 0, t = 0;
        dist[s0] = 0; q[t++] = s0;
        while (h < t) {
            int v = q[h++];
            int g = v % N, side = v / N;
            for (int i = 0; i < d; i++) {
                int w = side == 0 ? N + mul(X[i], g) : mul(Xi[i], g);
                if (dist[w] < 0) { dist[w] = dist[v] + 1; q[t++] = w; }
            }
        }
        for (int v = 0; v < n; v++) { if (dist[v] < 0) { diam = 1000000000; break; } if (dist[v] > diam) diam = dist[v]; }
    }
    free(dist); free(q);
    return diam;
}

static inline int used(int x, int n) {
    for (int j = 0; j < n; j++) if (S[j] == x) return 1;
    return 0;
}

static void random_start(void) {
    S[0] = 0;
    for (int i = 1; i < d; i++) {
        int x;
        do { x = rnd() % N; } while (used(x, i));
        S[i] = x;
    }
}

static void load_table(const char *path) {
    FILE *f = fopen(path, "r");
    if (!f) { fprintf(stderr, "cannot open table %s\n", path); exit(1); }
    if (fscanf(f, "%d", &N0) != 1 || N0 < 1 || N0 > 65535) { fprintf(stderr, "bad table size\n"); exit(1); }
    MT0 = malloc(sizeof(uint16_t) * (size_t)N0 * N0);
    for (long i = 0; i < (long)N0 * N0; i++) {
        int v;
        if (fscanf(f, "%d", &v) != 1 || v < 0 || v >= N0) { fprintf(stderr, "bad entry %ld\n", i); exit(1); }
        MT0[i] = (uint16_t)v;
    }
    fclose(f);
    for (int h = 0; h < N0; h++)
        if (MT0[h] != h || MT0[(long)h * N0] != h) { fprintf(stderr, "element 0 is not the identity\n"); exit(1); }
    IT0 = malloc(sizeof(int) * N0);
    for (int g = 0; g < N0; g++) {
        IT0[g] = -1;
        for (int h = 0; h < N0; h++) if (MT0[(long)g * N0 + h] == 0) IT0[g] = h;
        if (IT0[g] < 0) { fprintf(stderr, "no inverse for %d\n", g); exit(1); }
    }
}

int main(int argc, char **argv) {
    if (argc > 6 && strcmp(argv[1], "eval") == 0) {   /* eval D d table c x1 .. xd : cost and BFS diameter */
        D = atoi(argv[2]); d = atoi(argv[3]); C = atoi(argv[5]);
        load_table(argv[4]);
        N = N0 * C;
        bg = malloc(sizeof(int) * N); bz = malloc(sizeof(int) * N);
        for (int x = 0; x < N; x++) { bg[x] = x / C; bz[x] = x % C; }
        stamp = calloc(N, sizeof(int));
        bufA = malloc(sizeof(int) * N); bufB = malloc(sizeof(int) * N);
        for (int i = 0; i < d; i++) S[i] = atoi(argv[6 + i]);
        printf("cost=%d bfs_diameter=%d N=%d\n", cost(S), bfs_diam(S), N);
        return 0;
    }
    int check = argc > 1 && strcmp(argv[1], "check") == 0;
    int a = check ? 2 : 1;
    if (argc < a + (check ? 5 : 6)) {
        fprintf(stderr, "usage: haar_dd D d table c seed seconds [outfile|-] [K]\n"
                        "       haar_dd check D d table c seed\n");
        return 1;
    }
    D = atoi(argv[a]); d = atoi(argv[a + 1]);
    const char *table = argv[a + 2];
    C = atoi(argv[a + 3]);
    rs = 0x9E3779B97F4A7C15ULL ^ (unsigned long long)atoll(argv[a + 4]) * 2654435761ULL;
    double secs = check ? 0 : atof(argv[a + 5]);
    const char *out = (!check && argc > a + 6 && strcmp(argv[a + 6], "-")) ? argv[a + 6] : NULL;
    int K = (!check && argc > a + 7) ? atoi(argv[a + 7]) : 20;
    if (d > MAXD || d < 2 || K < 1 || D < 3 || C < 1) { fprintf(stderr, "bad parameters\n"); return 1; }
    load_table(table);
    N = N0 * C;
    bg = malloc(sizeof(int) * N); bz = malloc(sizeof(int) * N);
    for (int x = 0; x < N; x++) { bg[x] = x / C; bz[x] = x % C; }
    stamp = calloc(N, sizeof(int));
    bufA = malloc(sizeof(int) * N); bufB = malloc(sizeof(int) * N);

    if (check) {
        int ok = 1, zeros = 0;
        for (int trial = 0; trial < 200; trial++) {
            random_start();
            int c = cost(S), dm = bfs_diam(S);
            if ((c == 0) != (dm <= D)) { ok = 0; printf("mismatch trial %d: cost %d diam %d\n", trial, c, dm); }
            zeros += c == 0;
        }
        printf("check %s (D=%d d=%d N=%d, %d of 200 random S had cost 0)\n", ok ? "OK" : "FAILED", D, d, N, zeros);
        return ok ? 0 : 1;
    }

    int bestc = 1 << 30, restarts = 0;
    long long steps = 0;
    double t0 = now(), lastp = t0;
    while (now() - t0 < secs && bestc > 0) {
        restarts++;
        random_start();
        int c = cost(S);
        double T0 = 2.0, temp = T0;
        long since = 0;
        int runbest = c;
        while (c > 0 && now() - t0 < secs) {
            steps++;
            int bi = -1, bx = 0, bc = 1 << 30;
            for (int t = 0; t < K; t++) {
                int i = 1 + rnd() % (d - 1);
                int nw, old = S[i];
                do { nw = rnd() % N; } while (used(nw, d));
                S[i] = nw;
                int c2 = cost(S);
                S[i] = old;
                evals++;
                if (c2 < bc) { bc = c2; bi = i; bx = nw; }
            }
            if (bc <= c || exp((c - bc) / temp) * 4294967296.0 > (double)(rnd() & 0xffffffffULL)) {
                S[bi] = bx;
                c = bc;
                if (c < runbest) { runbest = c; since = 0; } else since++;
            } else {
                since++;
            }
            temp = T0 * exp(-(double)(since % 20000) / 4000.0) + 0.05;
            if (c < bestc) { bestc = c; memcpy(best, S, sizeof(int) * d); }
            if (since > 60000) break;
            if (now() - lastp > 300) {
                lastp = now();
                printf("  t=%.0f best=%d run=%d cur=%d restarts=%d steps=%lld\n", lastp - t0, bestc, runbest, c, restarts, steps);
                fflush(stdout);
            }
        }
    }
    double el = now() - t0;
    printf("D=%d d=%d table=%s c=%d N=%d n=%d K=%d best=%d restarts=%d steps=%lld evals=%lld time=%.1f evals_per_s=%.0f\n",
           D, d, table, C, N, 2 * N, K, bestc, restarts, steps, evals, el, evals / el);
    if (bestc == 0 && out) {
        if (bfs_diam(best) > D) { fprintf(stderr, "internal: BFS disagrees on best\n"); return 2; }
        FILE *f = fopen(out, "w");
        if (!f) { fprintf(stderr, "cannot write %s\n", out); f = stdout; }
        fprintf(f, "%d %d %d %d %s\n", D, d, N, C, table);
        for (int i = 0; i < d; i++) fprintf(f, "%d\n", best[i]);
        if (f != stdout) fclose(f);
    }
    return 0;
}
