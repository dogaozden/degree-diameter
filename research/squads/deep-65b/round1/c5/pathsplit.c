/* pathsplit.c: tabu search over voltages of path-split 3+3 lifts of a degree-6 base (card c5).
 * Base blocks: 0=A0 1=A1 2=A2 (side A), 3=B0 4=B1 5=B2 (side B). Lift by group G of order m, n = 6m,
 * vertex (block,g) has id block*m+g, edge (u,g)~(v,g*s) for each voltage s of base dart u->v.
 * Internal path edges (voltage 1): A0-B0, A2-B0, A1-B1, A1-B2.
 * External darts (u->v, voltage set S_k): k=0 A0->B1 size a; k=1 A0->B2 size 5-a; k=2 A2->B1 size 5-a;
 *                                        k=3 A2->B2 size a;  k=4 A1->B0 size 4.
 * Normalisation: identity lies in S_0 (switching of the Y blocks), so S_0[0] = 0 is fixed.
 * Cost: G acts transitively on each block, so the vertices at distance > 5 from block representative r are
 * the same for all g in block r. cost = sum_r #unreached(rep_r) (6 BFS of depth 5).
 * unordered bad pairs = m*cost/2 (= score65's bad).
 * usage: pathsplit TAB a seed seconds [OUT.edges|-] [K]   (seconds = 0: evaluate one random state; K: sampled moves/iter)
 * Prints one RESULT line; with OUT writes the best state's edge list (first line n, then "u v" lines).
 */
#include <limits.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define DEG 6
#define STALL 300
static int m, n, A;
static int *mul;
static int sz[5];
static int *S[5];
static char *inS[5];
static const int EU[5] = {0, 0, 2, 2, 1};
static const int EV[5] = {4, 5, 4, 5, 3};
static int *stamp, *q, *inv;
static int gen = 0;
static unsigned long long rs = 88172645463325252ULL;

static unsigned long long rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndi(int k) { return (int)(rnd() % (unsigned long long)k); }

/* block-level incidences: each block has DEG slots; k=-1 internal (voltage 1), dir 0 out (g*s), dir 1 in (g*s^-1) */
typedef struct { int v, k, i, dir; } slot_t;
static slot_t slots[6][DEG];
static void make_slots(void) {
    int c[6] = {0, 0, 0, 0, 0, 0};
#define SL(u, V, KK, II, DD) do { slots[u][c[u]].v = (V); slots[u][c[u]].k = (KK); slots[u][c[u]].i = (II); slots[u][c[u]].dir = (DD); c[u]++; } while (0)
    SL(0, 3, -1, 0, 0); SL(3, 0, -1, 0, 0);
    SL(2, 3, -1, 0, 0); SL(3, 2, -1, 0, 0);
    SL(1, 4, -1, 0, 0); SL(4, 1, -1, 0, 0);
    SL(1, 5, -1, 0, 0); SL(5, 1, -1, 0, 0);
    for (int k = 0; k < 5; k++)
        for (int i = 0; i < sz[k]; i++) {
            SL(EU[k], EV[k], k, i, 0);
            SL(EV[k], EU[k], k, i, 1);
        }
    for (int u = 0; u < 6; u++) if (c[u] != DEG) { fprintf(stderr, "bad degree block %d: %d\n", u, c[u]); exit(1); }
#undef SL
}

static inline int nbr(int u, int g, int j) {
    slot_t *t = &slots[u][j];
    if (t->k < 0) return t->v * m + g;
    int s = S[t->k][t->i];
    if (t->dir) s = inv[s];
    return t->v * m + mul[g * m + s];
}

/* sum over the 6 representatives of #vertices at distance > 5; returns early once the sum exceeds lim */
static long cost_lim(long lim) {
    long tot = 0;
    for (int r = 0; r < 6; r++) {
        gen++;
        int src = r * m, head = 0, tail = 1;
        q[0] = src;
        stamp[src] = gen;
        for (int d = 0; d < 5; d++) {
            int end = tail;
            for (; head < end; head++) {
                int w0 = q[head];
                int u = w0 / m, g = w0 - u * m;
                for (int j = 0; j < DEG; j++) {
                    int w = nbr(u, g, j);
                    if (stamp[w] != gen) { stamp[w] = gen; q[tail++] = w; }
                }
            }
        }
        tot += n - tail;
        if (tot > lim) return tot;
    }
    return tot;
}

static void apply(int k, int i, int y) {
    int old = S[k][i];
    inS[k][old] = 0;
    inS[k][y] = 1;
    S[k][i] = y;
}

static void randinit(void) {
    for (int k = 0; k < 5; k++) {
        memset(inS[k], 0, m);
        int start = 0;
        if (k == 0) { S[0][0] = 0; inS[0][0] = 1; start = 1; }
        for (int i = start; i < sz[k]; i++) {
            int y;
            do { y = rndi(m); } while (inS[k][y]);
            S[k][i] = y;
            inS[k][y] = 1;
        }
    }
}

static void write_edges(const char *fn) {
    FILE *o = fopen(fn, "w");
    if (!o) return;
    fprintf(o, "%d\n", n);
    for (int v = 0; v < n; v++) {
        int u = v / m, g = v - u * m;
        for (int j = 0; j < DEG; j++) {
            int w = nbr(u, g, j);
            if (w > v) fprintf(o, "%d %d\n", v, w);
        }
    }
    fclose(o);
}

int main(int argc, char **argv) {
    if (argc < 5) { fprintf(stderr, "usage: pathsplit TAB a seed seconds [OUT.edges]\n"); return 2; }
    FILE *f = fopen(argv[1], "r");
    if (!f || fscanf(f, "%d", &m) != 1) { fprintf(stderr, "bad table\n"); return 2; }
    mul = malloc((size_t)m * m * sizeof(int));
    for (int i = 0; i < m * m; i++) if (fscanf(f, "%d", &mul[i]) != 1) { fprintf(stderr, "short table\n"); return 2; }
    fclose(f);
    A = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double secs = atof(argv[4]);
    const char *out = (argc > 5 && argv[5][0] != '-') ? argv[5] : NULL;
    int K = argc > 6 ? atoi(argv[6]) : 0;   /* 0: full neighbourhood, K>0: K random candidate moves per iteration */
    if (A < 0 || A > 5) return 2;
    rs = seed * 2654435761ULL + 88172645463325252ULL;
    n = 6 * m;
    stamp = calloc((size_t)n, sizeof(int));
    q = malloc((size_t)n * sizeof(int));
    inv = malloc((size_t)m * sizeof(int));
    for (int g = 0; g < m; g++) for (int h = 0; h < m; h++) if (mul[g * m + h] == 0) inv[g] = h;
    sz[0] = A; sz[1] = 5 - A; sz[2] = 5 - A; sz[3] = A; sz[4] = 4;
    int *bestS[5];
    long *tabu[5];
    make_slots();
    for (int k = 0; k < 5; k++) {
        S[k] = malloc((size_t)(sz[k] + 1) * sizeof(int));
        bestS[k] = malloc((size_t)(sz[k] + 1) * sizeof(int));
        inS[k] = calloc((size_t)m, 1);
        tabu[k] = calloc((size_t)m, sizeof(long));
    }
    struct timespec t0, t1;
    clock_gettime(CLOCK_MONOTONIC, &t0);
    if (secs <= 0) {
        randinit();
        long c = cost_lim(LONG_MAX);
        printf("EVAL m=%d a=%d seed=%llu cost=%ld bad=%ld\n", m, A, seed, c, (long)m * c / 2);
        if (out) write_edges(out);
        return 0;
    }
    long bestcost = LONG_MAX, it = 0, restarts = 0, t_best_it = 0;
    double t_best = 0;
    while (1) {
        randinit(); restarts++;
        long cur = cost_lim(LONG_MAX);
        long runbest = cur;
        int stall = 0;
        if (cur < bestcost) {
            bestcost = cur; t_best_it = it;
            for (int k = 0; k < 5; k++) memcpy(bestS[k], S[k], (size_t)sz[k] * sizeof(int));
            clock_gettime(CLOCK_MONOTONIC, &t1);
            t_best = (t1.tv_sec - t0.tv_sec) + 1e-9 * (t1.tv_nsec - t0.tv_nsec);
        }
        while (bestcost > 0 && stall <= STALL) {
            clock_gettime(CLOCK_MONOTONIC, &t1);
            double el = (t1.tv_sec - t0.tv_sec) + 1e-9 * (t1.tv_nsec - t0.tv_nsec);
            if (el > secs) goto done;
            it++;
            long bc = LONG_MAX; int bk = -1, bi = -1, by = -1, ties = 0;
            if (K == 0) {
              for (int k = 0; k < 5; k++)
                for (int i = (k == 0 ? 1 : 0); i < sz[k]; i++) {
                    int old = S[k][i];
                    for (int y = 0; y < m; y++) {
                        if (inS[k][y]) continue;
                        int istabu = tabu[k][y] > it;
                        long lim = bc;
                        if (istabu && bestcost - 1 < lim) lim = bestcost - 1;
                        apply(k, i, y);
                        long c = cost_lim(lim);
                        apply(k, i, old);
                        if (c > lim) continue;
                        if (c < bc) { bc = c; bk = k; bi = i; by = y; ties = 1; }
                        else if (c == bc && c <= lim) { ties++; if (rndi(ties) == 0) { bk = k; bi = i; by = y; } }
                    }
                }
            } else {
              for (int t = 0; t < K; t++) {
                int k, i, y;
                do { k = rndi(5); } while (k == 0 && sz[0] == 1);
                i = (k == 0) ? 1 + rndi(sz[0] - 1) : rndi(sz[k]);
                do { y = rndi(m); } while (inS[k][y]);
                int old = S[k][i];
                int istabu = tabu[k][y] > it;
                long lim = bc;
                if (istabu && bestcost - 1 < lim) lim = bestcost - 1;
                apply(k, i, y);
                long c = cost_lim(lim);
                apply(k, i, old);
                if (c > lim) continue;
                if (c < bc) { bc = c; bk = k; bi = i; by = y; ties = 1; }
                else if (c == bc) { ties++; if (rndi(ties) == 0) { bk = k; bi = i; by = y; } }
              }
            }
            if (bk < 0) { stall = STALL + 1; break; }
            int old = S[bk][bi];
            apply(bk, bi, by);
            tabu[bk][old] = it + 5 + rndi(8);
            cur = bc;
            if (cur < runbest) { runbest = cur; stall = 0; } else stall++;
            if (cur < bestcost) {
                bestcost = cur; t_best_it = it;
                for (int k = 0; k < 5; k++) memcpy(bestS[k], S[k], (size_t)sz[k] * sizeof(int));
                clock_gettime(CLOCK_MONOTONIC, &t1);
                t_best = (t1.tv_sec - t0.tv_sec) + 1e-9 * (t1.tv_nsec - t0.tv_nsec);
            }
        }
        if (bestcost == 0) break;
    }
done:
    clock_gettime(CLOCK_MONOTONIC, &t1);
    double tot = (t1.tv_sec - t0.tv_sec) + 1e-9 * (t1.tv_nsec - t0.tv_nsec);
    for (int k = 0; k < 5; k++) memcpy(S[k], bestS[k], (size_t)sz[k] * sizeof(int));
    printf("RESULT m=%d n=%d a=%d seed=%llu best_bad=%ld best_cost=%ld iters=%ld restarts=%ld t_best=%.2f t=%.2f sets=",
           m, n, A, seed, (long)m * bestcost / 2, bestcost, it, restarts, t_best, tot);
    for (int k = 0; k < 5; k++) {
        printf("[");
        for (int i = 0; i < sz[k]; i++) printf("%d%s", S[k][i], i + 1 < sz[k] ? "," : "");
        printf("]%s", k < 4 ? " " : "");
    }
    printf("\n");
    if (out) write_edges(out);
    return 0;
}
