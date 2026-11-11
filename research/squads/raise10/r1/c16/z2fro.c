/* c16: Haar graphs H(G,S), G = Z_p^2 x| Z_k (Frobenius, B fixed-point-free of order k), |S| = DEG, D = 10.
 * Group element g = v*K + i, v = v0 + P*v1 in [0,P^2), i in [0,K); (v,i)(w,j) = (v + B^i w, i+j).
 * Right multiplications are automorphisms of H(G,S), so eccentricities of (e,0) and (e,1) give the diameter.
 * Usage: z2fro P K DEG seconds seed outfile [S0 S1 ...]   (optional start set of element indices)
 * Simulated annealing on S (replace one element), cost = #vertices at distance > DIAM from (e,0) and (e,1).
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <stdint.h>
#include <time.h>
static double wall(void){ struct timespec ts; clock_gettime(CLOCK_MONOTONIC,&ts); return ts.tv_sec+1e-9*ts.tv_nsec; }

static int P, K, N, DEG, DIAM = 10;
static int Bm[2][2];
static int Apow[1024][2][2];
static int S[16], Si[16];
static int *LT[16], *LIT[16];
static int *dist, *queue;
static int *SAVT, *SAVIT;
static uint64_t rs;

static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline double urand(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int *GV0, *GV1, *GI, *MODP;
static inline int mulg(int g, int h) {
    int i = GI[g], w0 = GV0[h], w1 = GV1[h];
    int (*M)[2] = Apow[i];
    int a0 = MODP[M[0][0] * w0 + M[0][1] * w1];
    int a1 = MODP[M[1][0] * w0 + M[1][1] * w1];
    int r0 = GV0[g] + a0; if (r0 >= P) r0 -= P;
    int r1 = GV1[g] + a1; if (r1 >= P) r1 -= P;
    int j = GI[h]; int ij = i + j; if (ij >= K) ij -= K;
    return (r1 * P + r0) * K + ij;
}

static inline int invg(int g) {
    int v = g / K, i = g % K, v0 = v % P, v1 = v / P;
    int ii = (K - i) % K;
    int (*M)[2] = Apow[ii];
    int u0 = (P - (M[0][0] * v0 + M[0][1] * v1) % P) % P;
    int u1 = (P - (M[1][0] * v0 + M[1][1] * v1) % P) % P;
    return (u1 * P + u0) * K + ii;
}

static void setrow(int t) {
    for (int g = 0; g < N; g++) { LT[t][g] = mulg(S[t], g); LIT[t][g] = mulg(Si[t], g); }
}

/* returns cost; sets *diam to max finite distance over both sources */
static int cost(int *diam) {
    int total = 0, md = 0;
    int srcs[2] = {0, N};
    for (int s = 0; s < 2; s++) {
        int tot = 2 * N;
        for (int x = 0; x < tot; x++) dist[x] = -1;
        int qh = 0, qt = 0;
        dist[srcs[s]] = 0; queue[qt++] = srcs[s];
        while (qh < qt) {
            int u = queue[qh++];
            int du = dist[u];
            if (u < N) {
                for (int t = 0; t < DEG; t++) {
                    int w = N + LT[t][u];
                    if (dist[w] < 0) { dist[w] = du + 1; queue[qt++] = w; }
                }
            } else {
                int g = u - N;
                for (int t = 0; t < DEG; t++) {
                    int w = LIT[t][g];
                    if (dist[w] < 0) { dist[w] = du + 1; queue[qt++] = w; }
                }
            }
        }
        if (getenv("Z2DBG")) {
            int h[64] = {0}, un = 0;
            for (int x = 0; x < tot; x++) { if (dist[x] < 0) un++; else if (dist[x] < 64) h[dist[x]]++; }
            fprintf(stderr, "src %d reached %d unreached %d hist:", s, qt, un);
            for (int d = 0; d < 20; d++) fprintf(stderr, " %d", h[d]);
            fprintf(stderr, "\n");
        }
        for (int x = 0; x < tot; x++) {
            if (dist[x] < 0) total += 1;
            else { if (dist[x] > DIAM) total += 1; if (dist[x] > md) md = dist[x]; }
        }
    }
    if (diam) *diam = md;
    return total;
}

static int fpf_ok(int (*M)[2], int k) {
    /* M^i - I invertible for i=1..k-1 (Frobenius), order of M divides k */
    int X[2][2] = {{M[0][0], M[0][1]}, {M[1][0], M[1][1]}};
    for (int i = 1; i < k; i++) {
        int d = ((X[0][0] - 1) * (X[1][1] - 1) - X[0][1] * X[1][0]) % P;
        if (d < 0) d += P;
        if (d == 0) return 0;
        int Y[2][2];
        for (int a = 0; a < 2; a++) for (int b = 0; b < 2; b++)
            Y[a][b] = (X[a][0] * M[0][b] + X[a][1] * M[1][b]) % P;
        memcpy(X, Y, sizeof X);
    }
    return 1;
}

static int find_B(void) {
    /* find M with M^K = I, M^i - I invertible for 0<i<K (K>1), exact order K */
    for (int a = 0; a < P; a++) for (int b = 0; b < P; b++) for (int c = 0; c < P; c++) for (int d = 0; d < P; d++) {
        int det = ((a * d - b * c) % P + P) % P;
        if (det == 0) continue;
        int M[2][2] = {{a, b}, {c, d}};
        int X[2][2] = {{1, 0}, {0, 1}};
        int ok = 1;
        for (int i = 1; i <= K; i++) {
            int Y[2][2];
            for (int r = 0; r < 2; r++) for (int s = 0; s < 2; s++)
                Y[r][s] = (X[r][0] * M[0][s] + X[r][1] * M[1][s]) % P;
            memcpy(X, Y, sizeof X);
            if (i < K && X[0][0] == 1 && X[1][1] == 1 && X[0][1] == 0 && X[1][0] == 0) { ok = 0; break; }
        }
        if (!ok) continue;
        if (!(X[0][0] == 1 && X[1][1] == 1 && X[0][1] == 0 && X[1][0] == 0)) continue;
        if (K > 1) {
            int M2[2][2] = {{a, b}, {c, d}};
            if (!fpf_ok((int (*)[2])M2, K)) continue;
        }
        Bm[0][0] = a; Bm[0][1] = b; Bm[1][0] = c; Bm[1][1] = d;
        return 1;
    }
    return 0;
}

int main(int argc, char **argv) {
    if (argc < 7) { fprintf(stderr, "usage: z2fro P K DEG seconds seed outfile [S...]\n"); return 1; }
    P = atoi(argv[1]); K = atoi(argv[2]); DEG = atoi(argv[3]);
    double secs = atof(argv[4]);
    rs = 0x9E3779B97F4A7C15ULL ^ (uint64_t)atoll(argv[5]) * 0x2545F4914F6CDD1DULL;
    for (int i = 0; i < 10; i++) rnd();
    const char *outfile = argv[6];
    N = P * P * K;
    if (!find_B()) { fprintf(stderr, "no fixed-point-free B of order %d mod %d\n", K, P); return 2; }
    /* Apow[i] = B^i */
    for (int a = 0; a < 2; a++) for (int b = 0; b < 2; b++) Apow[0][a][b] = (a == b);
    for (int i = 1; i < K; i++)
        for (int a = 0; a < 2; a++) for (int b = 0; b < 2; b++)
            Apow[i][a][b] = (Apow[i - 1][a][0] * Bm[0][b] + Apow[i - 1][a][1] * Bm[1][b]) % P;
    GV0 = malloc(sizeof(int) * N); GV1 = malloc(sizeof(int) * N); GI = malloc(sizeof(int) * N);
    MODP = malloc(sizeof(int) * (2 * P * P + 2));
    for (int x = 0; x < 2 * P * P + 2; x++) MODP[x] = x % P;
    for (int g = 0; g < N; g++) { int v = g / K; GV0[g] = v % P; GV1[g] = v / P; GI[g] = g % K; }
    /* self-test of group axioms on random triples */
    for (int t = 0; t < 2000; t++) {
        int g = rnd() % N, h = rnd() % N, x = rnd() % N;
        if (mulg(g, invg(g)) != 0 || mulg(invg(g), g) != 0) { fprintf(stderr, "inverse test failed\n"); return 3; }
        if (mulg(mulg(g, h), x) != mulg(g, mulg(h, x))) { fprintf(stderr, "assoc test failed\n"); return 3; }
    }
    for (int t = 0; t < DEG; t++) { LT[t] = malloc(sizeof(int) * N); LIT[t] = malloc(sizeof(int) * N); }
    SAVT = malloc(sizeof(int) * N); SAVIT = malloc(sizeof(int) * N);
    dist = malloc(sizeof(int) * 2 * N);
    queue = malloc(sizeof(int) * 2 * N);
    int startset = argc - 7;
    int set[16];
    if (startset >= DEG) {
        for (int t = 0; t < DEG; t++) set[t] = atoi(argv[7 + t]);
    } else {
        for (int t = 0; t < DEG; t++) {
            int x, dup;
            do { x = rnd() % N; dup = 0; for (int u = 0; u < t; u++) if (set[u] == x) dup = 1; } while (dup);
            set[t] = x;
        }
    }
    for (int t = 0; t < DEG; t++) { S[t] = set[t]; Si[t] = invg(S[t]); setrow(t); }
    int cur = cost(NULL);
    int best = cur;
    double T0 = getenv("T0") ? atof(getenv("T0")) : 1.5, T = T0;
    double c0 = wall();
    long it = 0;
    int bestS[16];
    memcpy(bestS, S, sizeof S);
    fprintf(stderr, "P=%d K=%d N=%d (2N=%d) B=[[%d,%d],[%d,%d]] start cost %d\n", P, K, N, 2 * N,
            Bm[0][0], Bm[0][1], Bm[1][0], Bm[1][1], cur);
    while (1) {
        it++;
        if ((it & 255) == 0) {
            double el = wall() - c0;
            if (el > secs) break;
            /* slow reheat cycle */
            T = T0 * (0.3 + 0.7 * fmod(el / 10.0, 1.0));
        }
        int t = rnd() % DEG;
        int x, dup;
        do { x = rnd() % N; dup = 0; for (int u = 0; u < DEG; u++) if (S[u] == x) dup = 1; } while (dup);
        int old = S[t], oldi = Si[t];
        memcpy(SAVT, LT[t], sizeof(int) * N); memcpy(SAVIT, LIT[t], sizeof(int) * N);
        S[t] = x; Si[t] = invg(x); setrow(t);
        int c = cost(NULL);
        if (c <= cur || urand() < exp(-(double)(c - cur) / T)) {
            cur = c;
            if (c < best) {
                best = c; memcpy(bestS, S, sizeof S);
                fprintf(stderr, "  it %ld best cost %d\n", it, best);
            }
            if (c == 0) break;
        } else {
            S[t] = old; Si[t] = oldi;
            memcpy(LT[t], SAVT, sizeof(int) * N); memcpy(LIT[t], SAVIT, sizeof(int) * N);
        }
    }
    int md = 0;
    int c = cost(&md);
    if (best == 0 && cur == 0) {
        /* S currently is the zero-cost set */
        FILE *f = fopen(outfile, "w");
        fprintf(f, "P %d K %d DEG %d N %d B %d %d %d %d\n", P, K, DEG, N, Bm[0][0], Bm[0][1], Bm[1][0], Bm[1][1]);
        fprintf(f, "S");
        for (int t = 0; t < DEG; t++) fprintf(f, " %d", S[t]);
        fprintf(f, "\n");
        fclose(f);
        printf("FOUND vertices %d diam %d P %d K %d S", 2 * N, md, P, K);
        for (int t = 0; t < DEG; t++) printf(" %d", S[t]);
        printf("\n");
    } else {
        memcpy(S, bestS, sizeof S);
        for (int t = 0; t < DEG; t++) { Si[t] = invg(S[t]); setrow(t); }
        c = cost(&md);
        FILE *f = fopen(outfile, "w");
        fprintf(f, "P %d K %d DEG %d N %d B %d %d %d %d\nBEST %d\nS", P, K, DEG, N, Bm[0][0], Bm[0][1], Bm[1][0], Bm[1][1], best);
        for (int t = 0; t < DEG; t++) fprintf(f, " %d", S[t]);
        fprintf(f, "\n");
        fclose(f);
        printf("NOTFOUND best cost %d (2N=%d) P %d K %d its %ld\n", best, 2 * N, P, K, it);
    }
    return 0;
}
