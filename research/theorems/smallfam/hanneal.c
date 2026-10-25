/* hanneal.c: simulated annealing for Haar graphs H(G,S), |S| = DELTA, diameter <= D, over any group given by a
   multiplication table (hx.c 'tab' format: "N e" then N rows; row x lists x*y).

   Cost (as hx.c / haar_gen3): D even: #B-side elements not within D-1 of (e,A);
                               D odd : #A not within D-1 of (e,A) + #B not within D-1 of (e,B).
   Move: replace one s_i (i >= 1; s_0 = e is fixed) by the best of K candidates; with probability TARGP a candidate is
   targeted: take an uncovered target t, a random walk of length a from the source and a random walk of length b
   backwards from t (a + b + 1 <= D - 1, right parities), and choose s_i so that one edge joins the two walk ends.
   Metropolis acceptance at temperature T, T halves every COOL seconds, reheat to the best state after REHEAT seconds
   without improvement.
   Usage: hanneal TABLE DELTA D SECONDS SEED K OUT      (writes OUT with "SOL s0 s1 ..." when cost 0 is reached)
   Env: TMAX (default 2), COOL (20), REHEAT (60), TARGP (0.5).
*/
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/time.h>

static int N, E, *T, *INV, DELTA, D;
static uint64_t rs = 88172645463325252ULL;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static double now(void) { struct timeval tv; gettimeofday(&tv, NULL); return tv.tv_sec + 1e-6 * tv.tv_usec; }
static inline int mul(int x, int y) { return T[(size_t)x * N + y]; }

static int *dA, *dB, *q, *unc, nunc;   /* distances from the current source, uncovered list */

/* BFS from (e, startB) to depth D-1; returns uncovered count on the target side (targetA); fills unc[] */
static int bfs(const int *S, int startB, int targetA, int collect) {
    for (int i = 0; i < N; i++) { dA[i] = -1; dB[i] = -1; }
    int head = 0, tail = 0;
    if (startB) { dB[E] = 0; q[tail++] = 2 * E + 1; } else { dA[E] = 0; q[tail++] = 2 * E; }
    while (head < tail) {
        int v = q[head++], g = v >> 1, side = v & 1, d = side ? dB[g] : dA[g];
        if (d >= D - 1) continue;
        if (!side) { for (int i = 0; i < DELTA; i++) { int h = mul(S[i], g); if (dB[h] < 0) { dB[h] = d + 1; q[tail++] = 2 * h + 1; } } }
        else { for (int i = 0; i < DELTA; i++) { int h = mul(INV[S[i]], g); if (dA[h] < 0) { dA[h] = d + 1; q[tail++] = 2 * h; } } }
    }
    int c = 0;
    for (int i = 0; i < N; i++) {
        int miss = targetA ? dA[i] < 0 : dB[i] < 0;
        if (miss) { c++; if (collect && nunc < N) unc[nunc++] = i * 2 + (targetA ? 0 : 1) + (startB ? 4 * N : 0); }
    }
    return c;
}

static int cost(const int *S, int collect) {
    nunc = 0;
    if (D % 2 == 0) return bfs(S, 0, 0, collect);
    int c = bfs(S, 0, 1, collect);
    return c + bfs(S, 1, 0, collect);
}

/* random walk of length len from (g, side) */
static void walk(const int *S, int g, int side, int len, int *og, int *oside) {
    int last = -1;
    for (int t = 0; t < len; t++) {
        int i; do { i = rnd() % DELTA; } while (i == last && DELTA > 1);
        g = side == 0 ? mul(S[i], g) : mul(INV[S[i]], g);
        side ^= 1; last = i;
    }
    *og = g; *oside = side;
}

int main(int argc, char **argv) {
    if (argc < 8) { fprintf(stderr, "usage: hanneal TABLE DELTA D SECONDS SEED K OUT\n"); return 2; }
    FILE *f = fopen(argv[1], "r"); if (!f) { perror("table"); return 2; }
    if (fscanf(f, "%d %d", &N, &E) != 2) return 2;
    T = malloc(sizeof(int) * (size_t)N * N);
    for (size_t i = 0; i < (size_t)N * N; i++) if (fscanf(f, "%d", &T[i]) != 1) return 2;
    fclose(f);
    DELTA = atoi(argv[2]); D = atoi(argv[3]); double secs = atof(argv[4]); rs ^= (uint64_t)atoll(argv[5]) * 0x9E3779B97F4A7C15ULL;
    int K = atoi(argv[6]); const char *out = argv[7];
    double TMAX = getenv("TMAX") ? atof(getenv("TMAX")) : 2.0, COOL = getenv("COOL") ? atof(getenv("COOL")) : 20;
    double REHEAT = getenv("REHEAT") ? atof(getenv("REHEAT")) : 60, TARGP = getenv("TARGP") ? atof(getenv("TARGP")) : 0.5;
    INV = malloc(sizeof(int) * N);
    for (int x = 0; x < N; x++) for (int y = 0; y < N; y++) if (mul(x, y) == E) { INV[x] = y; break; }
    dA = malloc(sizeof(int) * N); dB = malloc(sizeof(int) * N); q = malloc(sizeof(int) * 2 * N + 8); unc = malloc(sizeof(int) * N);
    int S[16], best[16], cand[16];
    S[0] = E;
    for (int i = 1; i < DELTA; i++) { int x; int ok; do { x = rnd() % N; ok = x != E; for (int j = 1; j < i; j++) if (S[j] == x) ok = 0; } while (!ok); S[i] = x; }
    int c = cost(S, 1), bc = c; memcpy(best, S, sizeof S);
    double t0 = now(), tstart = t0, tlast = t0, Tcur = TMAX, lastgain = t0; long long evals = 1, steps = 0;
    int *uncs = malloc(sizeof(int) * N), nuncs = nunc; memcpy(uncs, unc, sizeof(int) * nunc);
    while (bc > 0 && now() - tstart < secs) {
        steps++;
        int i = 1 + rnd() % (DELTA - 1);
        int bestcand = -1, bestcc = 1 << 30;
        for (int kk = 0; kk < K; kk++) {
            int x;
            if (nuncs > 0 && (rnd() % 1000) < TARGP * 1000) {
                int u = uncs[rnd() % nuncs];
                int tgt = (u % (4 * N)) / 2, tside = u % 2 == 0 ? 0 : 1, srcB = u >= 4 * N;
                /* target vertex (tgt, tside) [tside 0 = A]; source (e, srcB) */
                int L = D - 1;  /* total path length */
                int a = rnd() % L;   /* walk a from source, then one edge, then b back to target */
                int b = L - 1 - a;
                int g1, s1, g2, s2;
                walk(S, E, srcB, a, &g1, &s1);
                walk(S, tgt, tside, b, &g2, &s2);
                if (s1 == s2) { x = rnd() % N; }
                else if (s1 == 0) x = mul(g2, INV[g1]);      /* (g1,A) -> (x g1, B) = (g2, B) */
                else x = mul(g1, INV[g2]);                   /* (g2,A) -> (x g2, B) = (g1, B) */
            } else x = rnd() % N;
            int ok = x != E; for (int j = 1; j < DELTA; j++) if (j != i && S[j] == x) ok = 0;
            if (!ok) continue;
            memcpy(cand, S, sizeof S); cand[i] = x;
            int cc = cost(cand, 0); evals++;
            if (cc < bestcc) { bestcc = cc; bestcand = x; }
        }
        if (bestcand < 0) continue;
        double dlt = bestcc - c;
        if (dlt <= 0 || (double)(rnd() % 1000000) / 1e6 < exp(-dlt / Tcur)) {
            S[i] = bestcand; c = cost(S, 1); memcpy(uncs, unc, sizeof(int) * nunc); nuncs = nunc;
            if (c < bc) { bc = c; memcpy(best, S, sizeof S); lastgain = now(); }
        }
        double tn = now();
        Tcur = TMAX * pow(0.5, (tn - t0) / COOL); if (Tcur < 0.05) Tcur = 0.05;
        if (tn - lastgain > REHEAT) { memcpy(S, best, sizeof S); c = cost(S, 1); memcpy(uncs, unc, sizeof(int) * nunc); nuncs = nunc; lastgain = tn; t0 = tn - 0.0; }
        if (tn - tlast > 30) { fprintf(stderr, "t=%.0f steps=%lld evals=%lld cost=%d best=%d T=%.2f\n", tn - t0, steps, evals, c, bc, Tcur); tlast = tn; }
    }
    printf("RESULT N=%d DELTA=%d D=%d best=%d evals=%lld best_set", N, DELTA, D, bc, evals);
    for (int i = 0; i < DELTA; i++) printf(" %d", best[i]);
    printf("\n");
    if (bc == 0) { FILE *o = fopen(out, "w"); fprintf(o, "SOL"); for (int i = 0; i < DELTA; i++) fprintf(o, " %d", best[i]); fprintf(o, "\n"); fclose(o); }
    return 0;
}
