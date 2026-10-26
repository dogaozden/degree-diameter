/* girth_haar: annealing over S = {e, s1, s2, s3} in a group G (table file, groups.py format) for the Haar graph
 * H(G,S): vertices (x,A)=x and (y,B)=N+y, edges (x,A) ~ (s x,B) for s in S.
 * Hard constraint: girth >= GIRTH (default 8): BFS ball of radius R=(GIRTH-2)/2 around (e,A) must be a tree.
 * Cost = (#vertices farther than 8 from (e,A)) + (#vertices farther than 8 from (e,B)); 0 = diameter <= 8.
 * Usage: girth_haar TABLE.bin SECONDS SEED OUT.edges [GIRTH] */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <time.h>

#define D 4
#define DIAM 8
static int N, NV, R;
static uint16_t *T;
static int INV[1 << 16];
static const uint16_t *Lm[D], *Li[D];
static int S[D];
static int *vis, *par, *lev, *q;
static int epoch = 0;
static uint64_t rs = 88172645463325252ULL;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }

static void setS(void) {
    for (int i = 0; i < D; i++) { Lm[i] = T + (size_t)S[i] * N; Li[i] = T + (size_t)INV[S[i]] * N; }
}
static inline int nbr(int u, int i) { return u < N ? N + Lm[i][u] : Li[i][u - N]; }

static int girth_ok(void) {
    epoch++;
    int head = 0, tail = 0;
    q[tail++] = 0; vis[0] = epoch; par[0] = -1; lev[0] = 0;
    while (head < tail) {
        int u = q[head++];
        if (lev[u] >= R) continue;
        for (int i = 0; i < D; i++) {
            int w = nbr(u, i);
            if (w == par[u]) continue;
            if (vis[w] == epoch) return 0;
            vis[w] = epoch; par[w] = u; lev[w] = lev[u] + 1; q[tail++] = w;
        }
    }
    return 1;
}

/* number of vertices at distance > DIAM from root */
static int ball_miss(int root) {
    epoch++;
    int head = 0, tail = 0, reached = 0;
    q[tail++] = root; vis[root] = epoch; lev[root] = 0;
    while (head < tail) {
        int u = q[head++];
        reached++;
        if (lev[u] >= DIAM) continue;
        for (int i = 0; i < D; i++) {
            int w = nbr(u, i);
            if (vis[w] == epoch) continue;
            vis[w] = epoch; lev[w] = lev[u] + 1; q[tail++] = w;
        }
    }
    return 2 * N - reached;
}

static int eval_cost(void) {  /* -1 if girth constraint fails */
    if (!girth_ok()) return -1;
    return ball_miss(0) + ball_miss(N);
}

static int in_S(int g) { for (int i = 0; i < D; i++) if (S[i] == g) return 1; return 0; }

int main(int argc, char **argv) {
    if (argc < 5) { fprintf(stderr, "usage: %s TABLE.bin SECONDS SEED OUT.edges [GIRTH]\n", argv[0]); return 1; }
    int girth = argc > 5 ? atoi(argv[5]) : 8;
    R = (girth - 2) / 2;
    double secs = atof(argv[2]);
    rs ^= (uint64_t)atoll(argv[3]) * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 10; i++) rnd();
    FILE *f = fopen(argv[1], "rb"); if (!f) { perror("table"); return 1; }
    int32_t n32; if (fread(&n32, 4, 1, f) != 1) return 1;
    N = n32; NV = 2 * N;
    T = malloc((size_t)N * N * 2); if (fread(T, 2, (size_t)N * N, f) != (size_t)N * N) return 1; fclose(f);
    for (int g = 0; g < N; g++) for (int h = 0; h < N; h++) if (T[(size_t)g * N + h] == 0) { INV[g] = h; break; }
    vis = malloc(sizeof(int) * NV); par = malloc(sizeof(int) * NV); lev = malloc(sizeof(int) * NV); q = malloc(sizeof(int) * NV);
    for (int i = 0; i < NV; i++) vis[i] = 0;
    epoch = 0;

    struct timespec t0s, now; clock_gettime(CLOCK_MONOTONIC, &t0s);
    /* init: identity plus 3 random distinct elements, girth-feasible */
    long rejects = 0; int c;
    do {
        S[0] = 0;
        for (int i = 1; i < D; i++) { int g; do { g = rnd() % N; } while (in_S(g)); S[i] = g; }
        setS();
        c = eval_cost();
        if (c < 0) rejects++;
    } while (c < 0);
    int best = c; int bestS[D]; memcpy(bestS, S, sizeof S);
    double TA = argc > 6 ? atof(argv[6]) : 4.0, TB = 0.15;  /* annealing temperatures */
    long steps = 0; long K = 200000;  /* steps per cooling cycle */
    int done = 0;
    while (!done) {
        double frac = (double)(steps % K) / K;
        double T_ = TA * pow(TB / TA, frac);
        if (steps % K == 0 && steps > 0) { memcpy(S, bestS, sizeof S); setS(); c = best; }  /* restart cycle from best */
        int i = 1 + rnd() % (D - 1);
        int old = S[i], g;
        do { g = rnd() % N; } while (in_S(g));
        S[i] = g; setS();
        int c2 = eval_cost();
        steps++;
        if (c2 < 0) { rejects++; S[i] = old; setS(); }
        else if (c2 <= c || exp(-(c2 - c) / T_) > (double)(rnd() % 1000000007ULL) / 1000000007.0) {
            c = c2;
            if (c < best) { best = c; memcpy(bestS, S, sizeof S); }
            if (c == 0) { done = 1; break; }
        } else { S[i] = old; setS(); }
        if ((steps & 1023) == 0) {
            clock_gettime(CLOCK_MONOTONIC, &now);
            double el = (now.tv_sec - t0s.tv_sec) + 1e-9 * (now.tv_nsec - t0s.tv_nsec);
            if (el > secs) break;
        }
    }
    clock_gettime(CLOCK_MONOTONIC, &now);
    double el = (now.tv_sec - t0s.tv_sec) + 1e-9 * (now.tv_nsec - t0s.tv_nsec);
    memcpy(S, bestS, sizeof S); setS();
    int fc = eval_cost();
    printf("RESULT girth>=%d N=%d n=%d best=%d (recheck %d) steps=%ld girth_rejects=%ld S=[%d,%d,%d,%d] time=%.1f\n",
           girth, N, 2 * N, best, fc, steps, rejects, S[0], S[1], S[2], S[3], el);
    {  /* always write the best state (cost 0 = valid) */
        FILE *o = fopen(argv[4], "w");
        fprintf(o, "%d\n", 2 * N);
        for (int i = 0; i < D; i++) for (int x = 0; x < N; x++) fprintf(o, "%d %d\n", x, N + T[(size_t)S[i] * N + x]);
        fclose(o);
        printf("WROTE %s\n", argv[4]);
    }
    return 0;
}
