/* lift_ex: voltage lifts of a cubic bipartite base multigraph B over a finite group G, for bipartite (3,D) graphs.
 * Lift: vertices (u,g) = u*m+g (u a base vertex, g in G); each base edge x->y with voltage v gives (x,g) ~ (y, g v).
 * G acts by left multiplication, so diam <= D  iff  every base vertex u has ecc((u,e)) <= D.
 * Spanning-tree edges of B get voltage e (gauge); the other edges are free.
 *
 * Usage:
 *   lift_ex GROUP BASEFILE D check v_1 .. v_E        voltages (group indices) of all base edges, in file order
 *   lift_ex GROUP BASEFILE D ex [OUT]                exhaustive over all free voltages (stops at 1st solution if STOP=1)
 *   lift_ex GROUP BASEFILE D anneal SECONDS SEED [OUT]
 * GROUP spec (identity = index 0): meta m k r | zp2 p k a b c d | prod SPEC SPEC | cyc n
 *   meta m k r : Z_m x|_r Z_k,  (a,j)(b,l) = (a + r^j b, j+l), index a + m j
 *   zp2 p k a b c d : Z_p^2 x|_M Z_k, M = [[a,b],[c,d]] over Z_p with M^k = I, (v,j)(w,l) = (v + M^j w, j+l), index x + p y + p^2 j
 *   prod G1 G2 : direct product, index i1*m2 + i2
 *   cyc n : cyclic group Z_n
 * BASEFILE: "b E" then E lines "x y" (0-based, every vertex of degree 3, bipartite).
 * Output OUT: "n" then the lift's edges "u v" (apsp format).
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <math.h>
#include <limits.h>

#define MAXB 16
#define MAXE 64
#define MAXM 1024

static int m, b, E, D;
static int *mul, *inv_;
static int ex_[MAXE], ey_[MAXE];
static int istree[MAXE], freeE[MAXE], nfree;
static int volt[MAXE];
static int dt[MAXB][3], dv[MAXB][3];
static int *seen, *qu, stamp = 0, N;

/* ---- group construction ---- */
typedef struct { int m; int *t; } grp;
static int *alloc_t(int m) { return calloc((size_t)m * m, sizeof(int)); }

static int tok_i;
static char **tok;
static int ntok;

static grp parse_group(void);
static grp parse_group(void) {
    grp G; const char *w = tok[tok_i++];
    if (!strcmp(w, "cyc")) {
        int n = atoi(tok[tok_i++]); G.m = n; G.t = alloc_t(n);
        for (int i = 0; i < n; i++) for (int j = 0; j < n; j++) G.t[i * n + j] = (i + j) % n;
    } else if (!strcmp(w, "meta")) {
        int mm = atoi(tok[tok_i++]), k = atoi(tok[tok_i++]), r = atoi(tok[tok_i++]);
        int n = mm * k; G.m = n; G.t = alloc_t(n);
        int *rp = malloc(sizeof(int) * (k + 1)); rp[0] = 1 % mm;
        for (int j = 1; j <= k; j++) rp[j] = (int)(((long long)rp[j - 1] * r) % mm);
        if (rp[k] != 1 % mm) { fprintf(stderr, "meta: r^k != 1 mod m\n"); exit(2); }
        for (int ia = 0; ia < mm; ia++) for (int j = 0; j < k; j++)
            for (int ib = 0; ib < mm; ib++) for (int l = 0; l < k; l++) {
                int a = ia + mm * j, bb = ib + mm * l;
                int c = (int)(((ia + (long long)rp[j] * ib) % mm)) + mm * ((j + l) % k);
                G.t[a * n + bb] = c;
            }
        free(rp);
    } else if (!strcmp(w, "zp2")) {
        int p = atoi(tok[tok_i++]), k = atoi(tok[tok_i++]);
        int M[4]; for (int i = 0; i < 4; i++) M[i] = atoi(tok[tok_i++]);
        int n = p * p * k; G.m = n; G.t = alloc_t(n);
        int (*Mp)[4] = malloc(sizeof(int[4]) * (k + 1));
        Mp[0][0] = 1 % p; Mp[0][1] = 0; Mp[0][2] = 0; Mp[0][3] = 1 % p;
        for (int j = 1; j <= k; j++) {
            int *A = Mp[j - 1], *B = M, *C = Mp[j];
            C[0] = (A[0] * B[0] + A[1] * B[2]) % p; C[1] = (A[0] * B[1] + A[1] * B[3]) % p;
            C[2] = (A[2] * B[0] + A[3] * B[2]) % p; C[3] = (A[2] * B[1] + A[3] * B[3]) % p;
        }
        if (!(Mp[k][0] == 1 % p && Mp[k][1] == 0 && Mp[k][2] == 0 && Mp[k][3] == 1 % p)) { fprintf(stderr, "zp2: M^k != I\n"); exit(2); }
        for (int x = 0; x < p; x++) for (int y = 0; y < p; y++) for (int j = 0; j < k; j++)
            for (int x2 = 0; x2 < p; x2++) for (int y2 = 0; y2 < p; y2++) for (int l = 0; l < k; l++) {
                int *P = Mp[j];
                int ux = (x + P[0] * x2 + P[1] * y2) % p, uy = (y + P[2] * x2 + P[3] * y2) % p;
                int a = x + p * y + p * p * j, bb = x2 + p * y2 + p * p * l;
                G.t[a * n + bb] = ux + p * uy + p * p * ((j + l) % k);
            }
        free(Mp);
    } else if (!strcmp(w, "prod")) {
        grp A = parse_group(), B = parse_group();
        int n = A.m * B.m; G.m = n; G.t = alloc_t(n);
        for (int i1 = 0; i1 < A.m; i1++) for (int i2 = 0; i2 < B.m; i2++)
            for (int j1 = 0; j1 < A.m; j1++) for (int j2 = 0; j2 < B.m; j2++)
                G.t[(i1 * B.m + i2) * n + (j1 * B.m + j2)] = A.t[i1 * A.m + j1] * B.m + B.t[i2 * B.m + j2];
        free(A.t); free(B.t);
    } else { fprintf(stderr, "unknown group %s\n", w); exit(2); }
    return G;
}

/* ---- base graph ---- */
static void read_base(const char *path) {
    FILE *f = fopen(path, "r"); if (!f) { perror(path); exit(2); }
    if (fscanf(f, "%d %d", &b, &E) != 2) exit(2);
    for (int e = 0; e < E; e++) if (fscanf(f, "%d %d", &ex_[e], &ey_[e]) != 2) exit(2);
    fclose(f);
}
static void build_tree(void) {
    int vis[MAXB] = {0}, q[MAXB], h = 0, t = 0; vis[0] = 1; q[t++] = 0;
    memset(istree, 0, sizeof istree);
    while (h < t) {
        int x = q[h++];
        for (int e = 0; e < E; e++) {
            int y = -1;
            if (ex_[e] == x) y = ey_[e]; else if (ey_[e] == x) y = ex_[e];
            if (y >= 0 && !vis[y]) { vis[y] = 1; istree[e] = 1; q[t++] = y; }
        }
    }
    if (t != b) { fprintf(stderr, "base disconnected\n"); exit(2); }
    nfree = 0;
    for (int e = 0; e < E; e++) { if (!istree[e]) freeE[nfree++] = e; volt[e] = 0; }
}

/* ---- lift cost: total number of (u, x) pairs with dist((u,e), x) > D, u over base vertices ---- */
static void setup_darts(void) {
    int deg[MAXB] = {0};
    for (int e = 0; e < E; e++) {
        int x = ex_[e], y = ey_[e], v = volt[e];
        dt[x][deg[x]] = y; dv[x][deg[x]] = v; deg[x]++;
        dt[y][deg[y]] = x; dv[y][deg[y]] = inv_[v]; deg[y]++;
    }
}
static long cost_of(long bound) {
    setup_darts();
    long tot = 0;
    for (int u0 = 0; u0 < b; u0++) {
        stamp++;
        int s = u0 * m; seen[s] = stamp; qu[0] = s;
        int head = 0, tail = 1;
        for (int lev = 0; lev < D && head < tail; lev++) {
            int end = tail;
            while (head < end) {
                int x = qu[head++]; int ux = x / m, g = x - ux * m;
                for (int k = 0; k < 3; k++) {
                    int y = dt[ux][k] * m + mul[g * m + dv[ux][k]];
                    if (seen[y] != stamp) { seen[y] = stamp; qu[tail++] = y; }
                }
            }
        }
        tot += N - tail;
        if (tot > bound) return tot;
    }
    return tot;
}

static void write_lift(const char *out) {
    FILE *f = fopen(out, "w"); if (!f) { perror(out); return; }
    fprintf(f, "%d\n", N);
    for (int e = 0; e < E; e++) for (int g = 0; g < m; g++)
        fprintf(f, "%d %d\n", ex_[e] * m + g, ey_[e] * m + mul[g * m + volt[e]]);
    fclose(f);
}

static unsigned long long rs = 88172645463325252ULL;
static unsigned long long rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }

int main(int argc, char **argv) {
    if (argc < 5) { fprintf(stderr, "usage: see header\n"); return 2; }
    tok = argv + 0; /* placeholder, group spec parsed from argv[1] */
    /* group spec: tokens of argv[1] split by spaces */
    static char *gtok[64]; int ng = 0; char *copy = strdup(argv[1]);
    for (char *p = strtok(copy, " "); p; p = strtok(NULL, " ")) gtok[ng++] = p;
    tok = gtok; ntok = ng; tok_i = 0;
    grp G = parse_group();
    m = G.m; mul = G.t;
    if (m > MAXM) { fprintf(stderr, "group too large\n"); return 2; }
    inv_ = malloc(sizeof(int) * m);
    for (int i = 0; i < m; i++) { inv_[i] = -1; for (int j = 0; j < m; j++) if (mul[i * m + j] == 0) inv_[i] = j; if (inv_[i] < 0) { fprintf(stderr, "no inverse\n"); return 2; } }
    read_base(argv[2]); D = atoi(argv[3]); N = b * m;
    build_tree();
    seen = calloc(N, sizeof(int)); qu = malloc(sizeof(int) * N);
    const char *mode = argv[4];

    if (!strcmp(mode, "check")) {
        if (argc < 5 + E) { fprintf(stderr, "need %d voltages\n", E); return 2; }
        for (int e = 0; e < E; e++) volt[e] = atoi(argv[5 + e]);
        long c = cost_of(LONG_MAX);
        printf("RESULT check group=%s b=%d n=%d D=%d cost=%ld %s\n", argv[1], b, N, D, c, c == 0 ? "VALID" : "INVALID");
        if (c == 0 && argc > 5 + E) { for (int e = 0; e < E; e++) volt[e] = atoi(argv[5 + e]); write_lift(argv[5 + E]); }
        return 0;
    }
    if (!strcmp(mode, "ex")) {
        const char *out = argc > 5 ? argv[5] : NULL;
        int stop = getenv("STOP") ? atoi(getenv("STOP")) : 0;
        long long total = 1; for (int i = 0; i < nfree; i++) total *= m;
        long long nsol = 0; long bestc = LONG_MAX;
        int dig[MAXE] = {0};
        for (int i = 0; i < nfree; i++) volt[freeE[i]] = 0;
        for (long long it = 0; it < total; it++) {
            long c = cost_of(0);
            if (c == 0) {
                nsol++;
                if (nsol == 1 && out) {
                    write_lift(out);
                    printf("SOL");
                    for (int e = 0; e < E; e++) printf(" %d", volt[e]);
                    printf("\n");
                }
                if (stop) break;
            }
            /* odometer */
            for (int i = 0; i < nfree; i++) {
                if (++dig[i] < m) { volt[freeE[i]] = dig[i]; break; }
                dig[i] = 0; volt[freeE[i]] = 0;
            }
        }
        printf("RESULT ex group=%s b=%d n=%d D=%d free=%d evals=%lld solutions=%lld %s\n", argv[1], b, N, D, nfree, total, nsol, nsol ? "FOUND" : "none");
        return 0;
    }
    if (!strcmp(mode, "anneal")) {
        double secs = atof(argv[5]); rs ^= (unsigned long long)atoll(argv[6]) * 2654435761ULL + 1;
        const char *out = argc > 7 ? argv[7] : NULL;
        clock_t t0 = clock(); long long iters = 0; long bestc = LONG_MAX; int found = 0;
        while (!found && (double)(clock() - t0) / CLOCKS_PER_SEC < secs) {
            for (int i = 0; i < nfree; i++) volt[freeE[i]] = rnd() % m;
            long cur = cost_of(LONG_MAX);
            double T = 2.0;
            for (long long it = 0; it < 200000 && !found; it++, iters++) {
                int i = rnd() % nfree; int old = volt[freeE[i]];
                int nv = rnd() % m; if (nv == old) continue;
                volt[freeE[i]] = nv;
                long c = cost_of(LONG_MAX);
                if (c <= cur || (double)(rnd() % 1000000) / 1e6 < exp(-(double)(c - cur) / T)) {
                    cur = c;
                    if (c < bestc) bestc = c;
                    if (c == 0) { found = 1; break; }
                } else volt[freeE[i]] = old;
                T *= 0.99997; if (T < 0.05) T = 0.05;
            }
        }
        if (found && out) {
            write_lift(out);
        }
        printf("RESULT anneal group=%s b=%d n=%d D=%d iters=%lld best=%ld %s", argv[1], b, N, D, iters, bestc, found ? "FOUND" : "none");
        if (found) { printf(" volt"); for (int e = 0; e < E; e++) printf(" %d", volt[e]); }
        printf("\n");
        return 0;
    }
    fprintf(stderr, "unknown mode\n");
    return 2;
}
