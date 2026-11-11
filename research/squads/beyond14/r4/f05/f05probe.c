/* f05probe: start-state statistics of random lifts of d-regular bipartite p+p base multigraphs over the metacyclic
 * group G = Z_m x|_r Z_k (implicit multiplication, no tables), for a radius D.
 * Usage: f05probe d D p m k r nstates seed nroots
 * Per random state (random base = d random perfect matchings, reject disconnected; random voltages, reject equal
 * voltages on parallel edges) prints one line:
 *   state cost B13 B14 E13 Wnb
 * cost  = #(source w, vertex x) with dist > D  (same definition as salift_s; exact by left-regularity)
 * B13   = mean over sources of |ball of radius 13|
 * E13   = mean over roots of #distinct endpoints of ALL non-backtracking walks of length <= 13 from the root
 * Wnb   = number of non-backtracking walks of length <= 13 from a root (= sum_L d (d-1)^(L-1), same for all roots)
 * Summary lines start with '#'. Build: gcc -O3 -march=native -o f05probe f05probe.c -lm */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

static int d, D, p, m, k, r, N, n, W2;            /* W2 = 2p sources */
static int *Rp, *nbr, *revw;      /* nbr[x*d+i], revw[w*d+i], base slots dv/da */
static uint64_t *R, *R2;
static uint64_t rng = 0x9E3779B97F4A7C15ULL;
static inline uint64_t xr(void) { rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17; return rng; }

static inline int gmul(int x, int y) {
    int a = x / k, j = x % k, b = y / k, l = y % k;
    return (int)((((long long)a + (long long)Rp[j] * b) % m) * k + (j + l) % k);
}
static inline int ginv(int x) {
    int a = x / k, j = x % k, l = (k - j) % k;
    long long t = ((long long)a * Rp[l]) % m;
    return (int)(((m - t) % m) * k + l);
}

static int bdv[64][16], bda[64][16], brev[64][16], bcnt[64];
static int ep[64], eq[64], ea[64];
static int *bfsq, *bfsd;
static double comp_mean(void) {
    double tot = 0;
    for (int w = 0; w < W2; w++) {
        memset(bfsd, 0xff, sizeof(int) * (size_t)n);
        int h = 0, t = 0; bfsq[t++] = w * N; bfsd[w * N] = 0;
        while (h < t) { int x = bfsq[h++]; for (int i = 0; i < d; i++) { int y = nbr[x * d + i]; if (bfsd[y] < 0) { bfsd[y] = 1; bfsq[t++] = y; } } }
        tot += t;
    }
    return tot / W2;
}
static int ne;

static int connected(void) {
    int par[64]; for (int i = 0; i < W2; i++) par[i] = i;
    for (int e = 0; e < ne; e++) {
        int x = ep[e], y = eq[e];
        while (par[x] != x) x = par[x]; while (par[y] != y) y = par[y];
        if (x != y) par[x] = y;
    }
    int r0 = 0; for (int i = 0; i < W2; i++) { int x = i; while (par[x] != x) x = par[x]; if (i == 0) r0 = x; else if (x != r0) return 0; }
    return 1;
}

static void build_base(void) {
    /* random d-regular bipartite base: d random permutations, whites 0..p-1, blacks p..2p-1 */
    for (;;) {
        ne = 0;
        for (int s = 0; s < d; s++) {
            int pm[32]; for (int i = 0; i < p; i++) pm[i] = i;
            for (int i = p - 1; i > 0; i--) { int j = xr() % (i + 1); int t = pm[i]; pm[i] = pm[j]; pm[j] = t; }
            for (int i = 0; i < p; i++) { ep[ne] = i; eq[ne] = p + pm[i]; ne++; }
        }
        if (connected()) break;
    }
}

static void build_volt(void) {
    for (;;) {
        for (int e = 0; e < ne; e++) ea[e] = xr() % N;
        int ok = 1;
        for (int e = 0; e < ne && ok; e++) for (int f = e + 1; f < ne && ok; f++)
            if (ep[e] == ep[f] && eq[e] == eq[f] && ea[e] == ea[f]) ok = 0;
        if (ok) break;
    }
    for (int w = 0; w < W2; w++) bcnt[w] = 0;
    for (int e = 0; e < ne; e++) {
        int u = ep[e], v = eq[e], iu = bcnt[u]++, iv = bcnt[v]++;
        bdv[u][iu] = v; bda[u][iu] = ea[e]; brev[u][iu] = iv;
        bdv[v][iv] = u; bda[v][iv] = ginv(ea[e]); brev[v][iv] = iu;
    }
    for (int w = 0; w < W2; w++) if (bcnt[w] != d) { fprintf(stderr, "degree\n"); exit(2); }
    for (int w = 0; w < W2; w++) for (int i = 0; i < d; i++) {
        for (int g = 0; g < N; g++) {
            int x = w * N + g;
            nbr[x * d + i] = bdv[w][i] * N + gmul(g, bda[w][i]);
        }
        for (int g = 0; g < N; g++) revw[(w * N + g) * d + i] = brev[w][i];
    }
}

static long cost_and_profile(double *B13, double *B14) {
    int full = W2;
    memset(R, 0, 8L * n);
    for (int w = 0; w < W2; w++) R[w * N] = 1ULL << w;
    long sumpop = 0; double prof[64] = {0};
    for (int t = 1; t <= D; t++) {
        for (int x = 0; x < n; x++) {
            uint64_t v = R[x];
            int *q = &nbr[x * d];
            for (int i = 0; i < d; i++) v |= R[q[i]];
            R2[x] = v;
        }
        uint64_t *tmp = R; R = R2; R2 = tmp;
        sumpop = 0;
        for (int x = 0; x < n; x++) sumpop += __builtin_popcountll(R[x]);
        prof[t] = (double)sumpop / W2;
    }
    (void)full;
    *B13 = prof[13 <= D ? 13 : D]; *B14 = prof[D];
    return (long)W2 * n - sumpop;
}

static unsigned *stamp; static unsigned curstamp = 1; static char *endp;
static int *fa, *fb;
static double e13_from_root(int w0) {
    /* NB walk DP: states (y,s) = at vertex y having arrived through slot s; index y*d+s */
    memset(endp, 0, n);
    int nf = 0, nn = 0;
    unsigned st = ++curstamp;
    int x0 = w0 * N;
    for (int i = 0; i < d; i++) {
        int y = nbr[x0 * d + i], s2 = revw[x0 * d + i];
        int id = y * d + s2;
        if (stamp[id] != st) { stamp[id] = st; fa[nf++] = id; endp[y] = 1; }
    }
    long cnt_e = 0;
    for (int L = 2; L <= 13; L++) {
        st = ++curstamp; nn = 0;
        for (int q = 0; q < nf; q++) {
            int y = fa[q] / d, s = fa[q] % d, w = y / N;
            for (int t = 0; t < d; t++) {
                if (t == s) continue;
                int z = nbr[y * d + t], s2 = revw[y * d + t];
                (void)w;
                int id = z * d + s2;
                if (stamp[id] != st) { stamp[id] = st; fb[nn++] = id; endp[z] = 1; }
            }
        }
        int *tmp = fa; fa = fb; fb = tmp; nf = nn;
    }
    for (int x = 0; x < n; x++) cnt_e += endp[x];
    return (double)cnt_e;
}

int main(int argc, char **argv) {
    if (argc < 10) { fprintf(stderr, "usage: f05probe d D p m k r nstates seed nroots\n"); return 2; }
    d = atoi(argv[1]); D = atoi(argv[2]); p = atoi(argv[3]); m = atoi(argv[4]); k = atoi(argv[5]); r = atoi(argv[6]);
    int nst = atoi(argv[7]); rng ^= (uint64_t)atoll(argv[8]) * 0xD1B54A32D192ED03ULL; xr(); xr();
    int nroots = atoi(argv[9]);
    N = m * k; n = 2 * p * N; W2 = 2 * p;
    Rp = malloc(sizeof(int) * k); Rp[0] = 1 % m; for (int j = 1; j < k; j++) Rp[j] = (int)(((long long)Rp[j - 1] * r) % m);
    if (((long long)Rp[k - 1] * r) % m != 1 % m) { fprintf(stderr, "need r^k = 1 mod m\n"); return 2; }
    bfsq = malloc(sizeof(int) * (size_t)n); bfsd = malloc(sizeof(int) * (size_t)n);
    nbr = malloc(sizeof(int) * (size_t)n * d); revw = malloc(sizeof(int) * (size_t)n * d);
    R = malloc(8L * n); R2 = malloc(8L * n);
    stamp = calloc((size_t)n * d, sizeof(unsigned)); endp = malloc(n); fa = malloc(sizeof(int) * (size_t)n * d); fb = malloc(sizeof(int) * (size_t)n * d);
    long Wnb = 0;
    { double tot = d; double pw = 1; for (int L = 2; L <= 13; L++) { pw *= (d - 1); tot += d * pw; } Wnb = (long)tot; }
    printf("# d=%d D=%d p=%d n=%d N=%d group Z%dx|%dZ%d walksNB13=%ld\n", d, D, p, n, N, m, r, k, Wnb);
    for (int s = 0; s < nst; s++) {
        build_base(); build_volt();
        double B13, B14; long c = cost_and_profile(&B13, &B14);
        double e13 = 0; int nr = nroots > 0 && nroots < W2 ? nroots : W2;
        for (int w = 0; w < nr; w++) e13 += e13_from_root(w);
        e13 /= nr;
        printf("%d %ld %.1f %.1f %.1f %ld %.1f\n", s, c, B13, B14, e13, Wnb, comp_mean());
        if (getenv("PRINTV")) { printf("#V"); for (int e = 0; e < ne; e++) { int a = ea[e]; printf(" (%d,%d,a=%d/%d)", ep[e], eq[e], a / k, a % k); } printf("\n"); }
        if (getenv("DUMP") && s == (getenv("DUMPIDX") ? atoi(getenv("DUMPIDX")) : 0)) { FILE *f = fopen(getenv("DUMP"), "w"); fprintf(f, "%d %d\n", n, n * d / 2);
            for (int x = 0; x < n; x++) for (int i = 0; i < d; i++) { int y = nbr[x * d + i]; if (x < y) fprintf(f, "%d %d\n", x, y); }
            fclose(f); }
        fflush(stdout);
    }
    return 0;
}
