/* c8: a copy-attachment family (not hubs on X(M)).
   Base: X(M) = 3 copies (levels 0,1,2) of the incidence graph of H(q), point p at level c ~ line M(p) at level c+1.
   Attached: one copy of the incidence graph of H(q2) (or C_12 for q2 = 1). Each attached vertex has S = q+1-q2
   spare edges (degree q+2 in total). A removed X(M) cross edge (p,c)-(M(p),c+1) frees two X(M) endpoints, which
   take the spares of the attached copy: the freed point gets an attached line, the freed line an attached point.
   Freed count K = S*N2, so the attached copy has 2*N2 vertices and the graph has 6N + 2*N2 vertices.
   State: removed cross edges (K of them), attached-line slot of each freed point (dls), attached-point slot of
   each freed line (dps). Cost = ordered pairs at distance > 7 (bit-parallel BFS). Simulated annealing.
   usage: attach q q2 seed seconds T0 out.edges */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <time.h>

static uint64_t rs = 88172645463325252ULL;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline int rndi(int n) { return (int)(rnd() % (uint64_t)n); }
static inline double rndu(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int Q, N, NL, Q2, N2, S, K, V;
static int *LP, *LP2, *M, *rem, *FP, *FPart, *dls, *dps;
static int *bFP, *bdls, *bdps;
static int *eu, *ev, *deg, *st, *adj, *fillp;
static uint64_t *vis, *fr, *nx;

#define IDP(p, c) ((c) * 2 * N + (p))
#define IDL(l, c) ((c) * 2 * N + N + (l))
#define DP(p) (6 * N + (p))
#define DL(l) (6 * N + N2 + (l))

static int load_hex(const char *fn, int *qq, int *nn, int **lp) {
    FILE *f = fopen(fn, "rb");
    if (!f) { perror(fn); exit(1); }
    int h[3];
    if (fread(h, 4, 3, f) != 3) { fprintf(stderr, "header\n"); exit(1); }
    *qq = h[0]; *nn = h[1];
    int L = h[2];
    int *a = malloc(sizeof(int) * (size_t)L * (h[0] + 1));
    if (fread(a, 4, (size_t)L * (h[0] + 1), f) != (size_t)L * (h[0] + 1)) { fprintf(stderr, "short\n"); exit(1); }
    fclose(f);
    *lp = a;
    return L;
}

static int build_edges(void) {
    int m = 0;
    for (int c = 0; c < 3; c++)
        for (int l = 0; l < NL; l++)
            for (int k = 0; k <= Q; k++) { eu[m] = IDP(LP[l * (Q + 1) + k], c); ev[m] = IDL(l, c); m++; }
    for (int l = 0; l < N2; l++)
        for (int k = 0; k <= Q2; k++) { eu[m] = DP(LP2[l * (Q2 + 1) + k]); ev[m] = DL(l); m++; }
    for (int p = 0; p < N; p++)
        for (int c = 0; c < 3; c++)
            if (!rem[p * 3 + c]) { eu[m] = IDP(p, c); ev[m] = IDL(M[p], (c + 1) % 3); m++; }
    for (int i = 0; i < K; i++) {
        int p = FP[i] / 3, c = FP[i] % 3;
        eu[m] = IDP(p, c); ev[m] = DL(dls[i]); m++;
        int l = FPart[i] / 3, c2 = FPart[i] % 3;
        eu[m] = DP(dps[i]); ev[m] = IDL(l, c2); m++;
    }
    return m;
}

/* ordered pairs (s,v) with dist(s,v) > 7 */
static long cost(void) {
    int m = build_edges();
    memset(deg, 0, sizeof(int) * (V + 1));
    for (int i = 0; i < m; i++) { deg[eu[i]]++; deg[ev[i]]++; }
    st[0] = 0;
    for (int v = 0; v < V; v++) st[v + 1] = st[v] + deg[v];
    for (int v = 0; v < V; v++) fillp[v] = st[v];
    for (int i = 0; i < m; i++) { adj[fillp[eu[i]]++] = ev[i]; adj[fillp[ev[i]]++] = eu[i]; }
    long bad = 0;
    for (int b = 0; b < V; b += 64) {
        int ns = V - b < 64 ? V - b : 64;
        uint64_t mask = ns == 64 ? ~0ULL : ((1ULL << ns) - 1);
        memset(vis, 0, sizeof(uint64_t) * V);
        memset(fr, 0, sizeof(uint64_t) * V);
        for (int k = 0; k < ns; k++) { vis[b + k] |= 1ULL << k; fr[b + k] |= 1ULL << k; }
        uint64_t *F = fr, *X = nx;
        for (int lev = 1; lev <= 7; lev++) {
            for (int v = 0; v < V; v++) {
                uint64_t acc = 0;
                for (int j = st[v]; j < st[v + 1]; j++) acc |= F[adj[j]];
                X[v] = acc & ~vis[v];
            }
            for (int v = 0; v < V; v++) vis[v] |= X[v];
            uint64_t *t = F; F = X; X = t;
        }
        for (int v = 0; v < V; v++) bad += ns - __builtin_popcountll(vis[v] & mask);
    }
    return bad;
}

static void shuffle_int(int *a, int n) {
    for (int i = n - 1; i > 0; i--) { int j = rndi(i + 1); int t = a[i]; a[i] = a[j]; a[j] = t; }
}

int main(int argc, char **argv) {
    if (argc < 7) { fprintf(stderr, "usage: attach q q2 seed seconds T0 out.edges\n"); return 1; }
    int q = atoi(argv[1]), q2 = atoi(argv[2]);
    rs ^= (uint64_t)atoll(argv[3]) * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 10; i++) rnd();
    double secs = atof(argv[4]), T0 = atof(argv[5]);
    const char *out = argv[6];
    char fn[512];
    sprintf(fn, "/home/user/degree-diameter/research/d10D7/hex/hex_q%d.bin", q);
    int qq, nn;
    NL = load_hex(fn, &qq, &nn, &LP);
    Q = qq; N = nn;
    if (q2 == 1) {
        N2 = 6; Q2 = 1; LP2 = malloc(sizeof(int) * 6 * 2);
        for (int l = 0; l < 6; l++) { LP2[2 * l] = l; LP2[2 * l + 1] = (l + 1) % 6; }
    } else {
        sprintf(fn, "/home/user/degree-diameter/research/d10D7/hex/hex_q%d.bin", q2);
        int q2q, n2;
        N2 = load_hex(fn, &q2q, &n2, &LP2);
        Q2 = q2q;
    }
    S = Q + 1 - Q2;
    K = S * N2;
    V = 6 * N + 2 * N2;
    fprintf(stderr, "H(%d): N=%d  attached H(%d): N2=%d  spares S=%d  K=%d  V=%d  degree check: %d\n",
            Q, N, Q2, N2, S, K, V, Q + 2);
    /* M: random bijection points -> lines */
    M = malloc(sizeof(int) * N);
    for (int i = 0; i < N; i++) M[i] = i;
    shuffle_int(M, N);
    rem = calloc(3 * N, sizeof(int));
    FP = malloc(sizeof(int) * K); FPart = malloc(sizeof(int) * K);
    dls = malloc(sizeof(int) * K); dps = malloc(sizeof(int) * K);
    bFP = malloc(sizeof(int) * K); bdls = malloc(sizeof(int) * K); bdps = malloc(sizeof(int) * K);
    int *perm = malloc(sizeof(int) * 3 * N);
    for (int i = 0; i < 3 * N; i++) perm[i] = i;
    shuffle_int(perm, 3 * N);
    for (int i = 0; i < K; i++) {
        FP[i] = perm[i]; rem[perm[i]] = 1;
        FPart[i] = M[FP[i] / 3] * 3 + (FP[i] % 3 + 1) % 3;
    }
    for (int i = 0; i < K; i++) { dls[i] = i / S; dps[i] = i / S; }
    shuffle_int(dls, K); shuffle_int(dps, K);
    int maxE = 3 * (Q + 1) * NL + 3 * N * 3 + 2 * K + 2 * N2 * (Q2 + 1) + 16;
    eu = malloc(sizeof(int) * maxE); ev = malloc(sizeof(int) * maxE);
    deg = malloc(sizeof(int) * (V + 1)); st = malloc(sizeof(int) * (V + 1));
    adj = malloc(sizeof(int) * 2 * maxE); fillp = malloc(sizeof(int) * V);
    vis = malloc(sizeof(uint64_t) * V); fr = malloc(sizeof(uint64_t) * V); nx = malloc(sizeof(uint64_t) * V);

    long cur = cost(), best = cur;
    fprintf(stderr, "initial bad ordered pairs = %ld\n", cur);
    memcpy(bFP, FP, sizeof(int) * K); memcpy(bdls, dls, sizeof(int) * K); memcpy(bdps, dps, sizeof(int) * K);
    clock_t t0 = clock();
    long it = 0;
    for (;;) {
        if ((it & 63) == 0) {
            double el = (double)(clock() - t0) / CLOCKS_PER_SEC;
            if (el > secs || best == 0) break;
            if ((it & 1023) == 0) fprintf(stderr, "it %ld t=%.0f cur=%ld best=%ld\n", it, el, cur, best);
        }
        double el = (double)(clock() - t0) / CLOCKS_PER_SEC;
        double T = T0 * pow(0.02 / 1.0, el / secs);   /* T0 -> 0.02*T0 over the run */
        int mt = rndi(3);
        int i = rndi(K), j = 0, e = 0, old = 0, oldPart = 0;
        if (mt == 0) {
            j = rndi(K); while (j == i) j = rndi(K);
            int t = dls[i]; dls[i] = dls[j]; dls[j] = t;
        } else if (mt == 1) {
            j = rndi(K); while (j == i) j = rndi(K);
            int t = dps[i]; dps[i] = dps[j]; dps[j] = t;
        } else {
            do { e = rndi(3 * N); } while (rem[e]);
            old = FP[i]; oldPart = FPart[i];
            rem[old] = 0; rem[e] = 1; FP[i] = e;
            FPart[i] = M[e / 3] * 3 + (e % 3 + 1) % 3;
        }
        long nc = cost();
        int acc = (nc <= cur) || (rndu() < exp((double)(cur - nc) / T));
        if (acc) {
            cur = nc;
            if (cur < best) {
                best = cur;
                memcpy(bFP, FP, sizeof(int) * K); memcpy(bdls, dls, sizeof(int) * K); memcpy(bdps, dps, sizeof(int) * K);
            }
        } else {
            if (mt == 0) { int t = dls[i]; dls[i] = dls[j]; dls[j] = t; }
            else if (mt == 1) { int t = dps[i]; dps[i] = dps[j]; dps[j] = t; }
            else { rem[e] = 0; rem[old] = 1; FP[i] = old; FPart[i] = oldPart; }
        }
        it++;
    }
    fprintf(stderr, "done: iterations=%ld best bad ordered pairs=%ld\n", it, best);
    /* restore best state and write edges */
    memset(rem, 0, sizeof(int) * 3 * N);
    memcpy(FP, bFP, sizeof(int) * K); memcpy(dls, bdls, sizeof(int) * K); memcpy(dps, bdps, sizeof(int) * K);
    for (int i = 0; i < K; i++) { rem[FP[i]] = 1; FPart[i] = M[FP[i] / 3] * 3 + (FP[i] % 3 + 1) % 3; }
    long chk = cost();
    int m = build_edges();
    FILE *f = fopen(out, "w");
    fprintf(f, "%d\n", V);
    for (int i = 0; i < m; i++) fprintf(f, "%d %d\n", eu[i], ev[i]);
    fclose(f);
    printf("q=%d q2=%d S=%d K=%d V=%d best_bad=%ld recheck=%ld edges=%d out=%s\n", Q, Q2, S, K, V, best, chk, m, out);
    return 0;
}
