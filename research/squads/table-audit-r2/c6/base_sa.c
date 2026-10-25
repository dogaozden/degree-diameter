/* base_sa.c: simulated annealing over cubic bipartite base multigraphs AND their voltages.
   Group G = Z_m x|_r Z_k (element g = y*m + x; (x1,y1)(x2,y2) = (x1 + r^y1 x2 mod m, y1+y2 mod k)).
   r = 1 gives Z_m x Z_k; k = 1 gives cyclic Z_m.
   Base: b = 2h vertices, side A = 0..h-1, side B = h..2h-1, E = 3h base edges (eu[i] in A, ew[i] in B),
   each with voltage volt[i] in G. Lift vertex (u,g) -> index u*N+g, n = b*N; base edge (u,w,a) gives
   (u,g) ~ (w, g*a). Left multiplication by G acts as automorphisms, so BFS from (s,0) for s in 0..b-1
   gives the exact diameter.
   Moves: (a) change one voltage; (b) 2-switch on two base edges (u1-w1, u2-w2 -> u1-w2, u2-w1),
   the rewired edges keep their voltages (optionally re-randomised).
   Cost = number of (s, x) pairs with dist((s,0), x) > D (unreachable counts), summed over s.
   Lifts with parallel darts (same neighbour and same multiplier at one base vertex) are rejected.
   Usage: base_sa m k r b D iters restarts seed T0 T1 OUTPREFIX [pswitch]
   Writes OUTPREFIX.edges (cost 0 lift, n = bN) or OUTPREFIX_best.edges (best seen). */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <stdint.h>
#include <time.h>

#define MAXB 64
#define MAXE 96

static int b, h, E, N, D, n;
static int eu[MAXE], ew[MAXE], volt[MAXE];
static int beu[MAXE], bew[MAXE], bvolt[MAXE];
static int gbeu[MAXE], gbew[MAXE], gbvolt[MAXE];
static int *mul, *inv;
static int adjW[MAXB * 3], adjR[MAXB * 3];
static int *stamp, *queue, *dist;
static int curstamp = 0;
static uint64_t rs;

static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static double rndu(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }
static int rndi(int k) { return (int)(rnd() % (uint64_t)k); }

static void build_group(int m, int k, int r) {
    N = m * k;
    mul = malloc(sizeof(int) * N * N);
    inv = malloc(sizeof(int) * N);
    int *rp = malloc(sizeof(int) * k);
    rp[0] = 1 % m;
    for (int y = 1; y < k; y++) rp[y] = (int)((long)rp[y - 1] * r % m);
    if ((long)rp[k - 1] * r % m != 1 % m) { fprintf(stderr, "bad group: r^k != 1 mod m\n"); exit(2); }
    for (int g1 = 0; g1 < N; g1++)
        for (int g2 = 0; g2 < N; g2++) {
            int x1 = g1 % m, y1 = g1 / m, x2 = g2 % m, y2 = g2 / m;
            int x = (int)((x1 + (long)rp[y1] * x2) % m);
            int y = (y1 + y2) % k;
            mul[g1 * N + g2] = y * m + x;
        }
    for (int g = 0; g < N; g++) {
        int found = 0;
        for (int hh = 0; hh < N; hh++) if (mul[g * N + hh] == 0) { inv[g] = hh; found = 1; break; }
        if (!found) { fprintf(stderr, "no inverse\n"); exit(2); }
    }
    for (int a = 0; a < N; a++)
        for (int c = 0; c < N; c++)
            for (int d = 0; d < N; d++)
                if (mul[mul[a * N + c] * N + d] != mul[a * N + mul[c * N + d]]) { fprintf(stderr, "not associative\n"); exit(2); }
    free(rp);
}

static void build_adj(void) {
    int cnt[MAXB];
    memset(cnt, 0, sizeof(cnt));
    for (int i = 0; i < E; i++) {
        int u = eu[i], w = ew[i], a = volt[i];
        adjW[u * 3 + cnt[u]] = w; adjR[u * 3 + cnt[u]] = a; cnt[u]++;
        adjW[w * 3 + cnt[w]] = u; adjR[w * 3 + cnt[w]] = inv[a]; cnt[w]++;
    }
}

/* simple-lift check: the three darts at each base vertex must have distinct (neighbour, multiplier) */
static int valid(void) {
    for (int u = 0; u < b; u++)
        for (int p = 0; p < 3; p++)
            for (int q = p + 1; q < 3; q++)
                if (adjW[u * 3 + p] == adjW[u * 3 + q] && adjR[u * 3 + p] == adjR[u * 3 + q]) return 0;
    return 1;
}

static int base_connected(void) {
    int seen[MAXB], bq[MAXB], bh = 0, bt = 0;
    memset(seen, 0, sizeof(seen));
    seen[0] = 1; bq[bt++] = 0;
    while (bh < bt) {
        int x = bq[bh++];
        for (int i = 0; i < E; i++) {
            int y = -1;
            if (eu[i] == x) y = ew[i]; else if (ew[i] == x) y = eu[i];
            if (y >= 0 && !seen[y]) { seen[y] = 1; bq[bt++] = y; }
        }
    }
    return bt == b;
}

/* returns the exact cost, or some value > limit as soon as the partial sum exceeds limit */
static long cost_eval(long limit) {
    long total = 0;
    for (int s = 0; s < b; s++) {
        if (total > limit) return total;
        curstamp++;
        int head = 0, tail = 0, src = s * N;
        stamp[src] = curstamp; dist[src] = 0; queue[tail++] = src;
        while (head < tail) {
            int x = queue[head++];
            int d = dist[x];
            if (d == D) continue;
            int u = x / N, g = x - u * N;
            const int *mrow = mul + g * N;
            for (int kk = 0; kk < 3; kk++) {
                int y = adjW[u * 3 + kk] * N + mrow[adjR[u * 3 + kk]];
                if (stamp[y] != curstamp) { stamp[y] = curstamp; dist[y] = d + 1; queue[tail++] = y; }
            }
        }
        total += n - tail;
    }
    return total;
}

static void random_base(void) {
    int stA[MAXE], stB[MAXE];
    for (int i = 0; i < E; i++) { stA[i] = i / 3; stB[i] = h + i / 3; }
    for (int i = E - 1; i > 0; i--) { int j = rndi(i + 1); int t = stB[i]; stB[i] = stB[j]; stB[j] = t; }
    for (int i = 0; i < E; i++) { eu[i] = stA[i]; ew[i] = stB[i]; volt[i] = rndi(N); }
}

static void save_best(void) {
    memcpy(beu, eu, sizeof(int) * E);
    memcpy(bew, ew, sizeof(int) * E);
    memcpy(bvolt, volt, sizeof(int) * E);
}

static void write_lift(const char *fn, const int *U, const int *W, const int *V) {
    FILE *f = fopen(fn, "w");
    if (!f) { fprintf(stderr, "cannot open %s\n", fn); exit(2); }
    fprintf(f, "%d\n", n);
    for (int i = 0; i < E; i++)
        for (int g = 0; g < N; g++)
            fprintf(f, "%d %d\n", U[i] * N + g, W[i] * N + mul[g * N + V[i]]);
    fclose(f);
}

static void print_base(FILE *f, const int *U, const int *W, const int *V) {
    fprintf(f, "BASE_EDGES");
    for (int i = 0; i < E; i++) fprintf(f, " %d-%d:%d", U[i], W[i], V[i]);
    fprintf(f, "\n");
}

int main(int argc, char **argv) {
    if (argc < 12) { fprintf(stderr, "usage: base_sa m k r b D iters restarts seed T0 T1 OUTPREFIX [pswitch]\n"); return 1; }
    int m = atoi(argv[1]), k = atoi(argv[2]), r = atoi(argv[3]);
    b = atoi(argv[4]); D = atoi(argv[5]);
    long iters = atol(argv[6]);
    int restarts = atoi(argv[7]);
    uint64_t seed = strtoull(argv[8], 0, 10);
    double T0 = atof(argv[9]), T1 = atof(argv[10]);
    const char *outp = argv[11];
    double pswitch = argc > 12 ? atof(argv[12]) : 0.3;
    if (b % 2 || b > MAXB) { fprintf(stderr, "b must be even and <= %d\n", MAXB); return 2; }
    h = b / 2; E = 3 * h;
    build_group(m, k, r);
    n = b * N;
    stamp = calloc((long)n, sizeof(int));
    queue = malloc(sizeof(int) * (long)n);
    dist = malloc(sizeof(int) * (long)n);
    rs = seed ? seed : (uint64_t)time(NULL) * 2654435761ULL + 1;
    long globalbest = -1;
    char fn[512];
    for (int rep = 0; rep < restarts; rep++) {
        for (;;) {
            random_base();
            build_adj();
            if (valid() && base_connected()) break;
        }
        long cur = cost_eval(1L << 60);
        long best = cur;
        save_best();
        long it;
        for (it = 0; it < iters && cur > 0; it++) {
            double T = T0 * pow(T1 / T0, (double)it / iters);
            if (rndu() < pswitch) {
                int i = rndi(E), j = rndi(E);
                if (i == j) continue;
                int u1 = eu[i], w1 = ew[i], u2 = eu[j], w2 = ew[j];
                if (u1 == u2 || w1 == w2) continue;
                int oi = ew[i], oj = ew[j], ovi = volt[i], ovj = volt[j];
                ew[i] = w2; ew[j] = w1;
                if (rndu() < 0.5) volt[i] = rndi(N);
                if (rndu() < 0.5) volt[j] = rndi(N);
                build_adj();
                if (!valid()) {
                    ew[i] = oi; ew[j] = oj; volt[i] = ovi; volt[j] = ovj; build_adj(); continue;
                }
                long lim = (long)floor(cur - T * log(rndu() + 1e-300));
                long c = cost_eval(lim);
                if (c <= lim) {
                    cur = c;
                    if (cur < best) { best = cur; save_best(); }
                } else {
                    ew[i] = oi; ew[j] = oj; volt[i] = ovi; volt[j] = ovj; build_adj();
                }
            } else {
                int i = rndi(E);
                int nv = rndi(N);
                if (nv == volt[i]) continue;
                int old = volt[i];
                volt[i] = nv;
                build_adj();
                if (!valid()) { volt[i] = old; build_adj(); continue; }
                long lim = (long)floor(cur - T * log(rndu() + 1e-300));
                long c = cost_eval(lim);
                if (c <= lim) {
                    cur = c;
                    if (cur < best) { best = cur; save_best(); }
                } else {
                    volt[i] = old; build_adj();
                }
            }
            if ((it & 0x3ffff) == 0 && it) fprintf(stderr, "  rep %d it %ld T %.3f cur %ld best %ld\n", rep, it, T, cur, best);
        }
        if (globalbest < 0 || best < globalbest) {
            globalbest = best;
            memcpy(gbeu, beu, sizeof(int) * E); memcpy(gbew, bew, sizeof(int) * E); memcpy(gbvolt, bvolt, sizeof(int) * E);
        }
        fprintf(stderr, "restart %d: best cost %ld (final %ld) after %ld iters\n", rep, best, cur, it);
        if (best == 0) {
            snprintf(fn, sizeof(fn), "%s.edges", outp);
            write_lift(fn, beu, bew, bvolt);
            printf("FOUND n=%d D=%d m=%d k=%d r=%d b=%d file=%s\n", n, D, m, k, r, b, fn);
            print_base(stdout, beu, bew, bvolt);
            return 0;
        }
    }
    snprintf(fn, sizeof(fn), "%s_best.edges", outp);
    write_lift(fn, gbeu, gbew, gbvolt);
    printf("NOTFOUND n=%d D=%d m=%d k=%d r=%d b=%d best=%ld file=%s\n", n, D, m, k, r, b, globalbest, fn);
    print_base(stdout, gbeu, gbew, gbvolt);
    return 0;
}
