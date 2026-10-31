/* lift66.c: simulated annealing over voltage assignments of a K_{K,K} base graph (K=6 gives degree 6).
   Lift: vertices (u,g), u in base (A_i = i, B_j = K+j), g in group G.  Edge (A_i,g) -- (B_j, g*a_ij).
   G acts semiregularly on the left, so all distances from (u,e) give the whole score:
     bad (unordered pairs at distance > 5) = M * sum_u #{x : d((u,e),x) > 5} / 2.
   Group: type 0 = cyclic Z_M, type 1 = dihedral D_{M/2} (order M).
   Usage: lift66 TYPE M K SEED SECONDS T0 T1 [OUTFILE]
   Writes the best assignment to OUTFILE (if given) as: n, then edge list "u v" for the lift. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <time.h>
#include <stdint.h>

static int M, K, NB, NE, TYPE;
static int *mul, *inv_;          /* M x M table, inverses */
static int *val;                 /* NE voltages, edge e = i*K+j */
static int *nbr, *dv;            /* NB x K arrays: neighbour base vertex and direction voltage */
static int *seen, *dep, *queue_;
static int stamp = 0;

static uint64_t rs = 88172645463325252ULL;
static inline uint64_t xr(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline double u01(void) { return (xr() >> 11) * (1.0 / 9007199254740992.0); }

static void build_group(void) {
    mul = malloc(sizeof(int) * M * M); inv_ = malloc(sizeof(int) * M);
    if (TYPE == 0) {
        for (int g = 0; g < M; g++) for (int h = 0; h < M; h++) mul[g * M + h] = (g + h) % M;
        for (int g = 0; g < M; g++) inv_[g] = (M - g) % M;
    } else {
        int n = M / 2;   /* element index g = i + n*e, meaning r^i s^e */
        for (int g = 0; g < M; g++) for (int h = 0; h < M; h++) {
            int i = g % n, e = g / n, j = h % n, f = h / n;
            int jj = e ? (n - j) % n : j;
            int r = (i + jj) % n;
            mul[g * M + h] = r + n * (e ^ f);
        }
        for (int g = 0; g < M; g++) {
            int i = g % n, e = g / n;
            if (e == 0) inv_[g] = (n - i) % n; else inv_[g] = g;
        }
    }
}

static void setup_base(void) {
    NB = 2 * K; NE = K * K;
    nbr = malloc(sizeof(int) * NB * K); dv = malloc(sizeof(int) * NB * K);
    for (int i = 0; i < K; i++) for (int j = 0; j < K; j++) {
        nbr[i * K + j] = K + j;          /* A_i -> B_j */
        nbr[(K + j) * K + i] = i;        /* B_j -> A_i */
    }
    seen = malloc(sizeof(int) * NB * M); dep = malloc(sizeof(int) * NB * M); queue_ = malloc(sizeof(int) * NB * M);
    val = malloc(sizeof(int) * NE);
}

static inline void set_edge(int i, int j) {
    int a = val[i * K + j];
    dv[i * K + j] = a;               /* A_i side: g -> g*a */
    dv[(K + j) * K + i] = inv_[a];   /* B_j side: h -> h*a^{-1} */
}

/* bad = unordered pairs at distance > 5 */
static long score(void) {
    long total = 0; int N = NB * M;
    for (int u = 0; u < NB; u++) {
        stamp++;
        int head = 0, tail = 0, src = u * M;   /* identity is index 0 in both group types */
        seen[src] = stamp; dep[src] = 0; queue_[tail++] = src;
        long reached = 0;
        while (head < tail) {
            int x = queue_[head++]; int d = dep[x];
            reached++;
            if (d == 5) continue;
            int ub = x / M, g = x - ub * M;
            for (int t = 0; t < K; t++) {
                int h = mul[g * M + dv[ub * K + t]];
                int y = nbr[ub * K + t] * M + h;
                if (seen[y] != stamp) { seen[y] = stamp; dep[y] = d + 1; queue_[tail++] = y; }
            }
        }
        total += N - reached;
    }
    return (long)M * total / 2;
}

int main(int argc, char **argv) {
    if (argc < 8) { fprintf(stderr, "usage: lift66 TYPE M K SEED SECONDS T0 T1 [OUT]\n"); return 1; }
    TYPE = atoi(argv[1]); M = atoi(argv[2]); K = atoi(argv[3]);
    rs ^= (uint64_t)atoll(argv[4]) * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 10; i++) xr();
    double secs = atof(argv[5]), T0 = atof(argv[6]), T1 = atof(argv[7]);
    const char *outf = argc > 8 ? argv[8] : NULL;
    build_group(); setup_base();
    for (int e = 0; e < NE; e++) val[e] = xr() % M;
    for (int i = 0; i < K; i++) for (int j = 0; j < K; j++) set_edge(i, j);
    long cur = score(), best = cur; int *bestv = malloc(sizeof(int) * NE); memcpy(bestv, val, sizeof(int) * NE);
    clock_t c0 = clock(); long it = 0, acc = 0;
    double T = T0;
    while (best > 0) {
        it++;
        if ((it & 255) == 0) {
            double el = (double)(clock() - c0) / CLOCKS_PER_SEC;
            if (el >= secs) break;
            double fr = el / secs; T = T0 * pow(T1 / T0, fr);
        }
        int e = xr() % NE; int old = val[e]; int nv = xr() % M;
        if (nv == old) continue;
        val[e] = nv; set_edge(e / K, e % K);
        long s = score(); long d = s - cur;
        if (d <= 0 || u01() < exp(-(double)d / T)) {
            cur = s; acc++;
            if (cur < best) { best = cur; memcpy(bestv, val, sizeof(int) * NE); }
        } else {
            val[e] = old; set_edge(e / K, e % K);
        }
    }
    double el = (double)(clock() - c0) / CLOCKS_PER_SEC;
    printf("type=%d M=%d K=%d n=%d iters=%ld accepted=%ld time=%.1fs best_bad=%ld\n",
           TYPE, M, K, 2 * K * M, it, acc, el, best);
    printf("voltages (rows A_i, cols B_j):\n");
    for (int i = 0; i < K; i++) { for (int j = 0; j < K; j++) printf("%d ", bestv[i * K + j]); printf("\n"); }
    if (outf) {
        /* lift edge list: vertex (u,g) -> u*M+g ; edges (A_i,g)-(B_j,g*a) */
        FILE *f = fopen(outf, "w");
        fprintf(f, "%d\n", 2 * K * M);
        for (int i = 0; i < K; i++) for (int j = 0; j < K; j++) {
            int a = bestv[i * K + j];
            for (int g = 0; g < M; g++) fprintf(f, "%d %d\n", i * M + g, (K + j) * M + mul[g * M + a]);
        }
        fclose(f);
    }
    return best == 0 ? 0 : 2;
}
