/* c3s.c (card c3): structured voltage lifts of the 4-vertex base A0,A1,B0,B1.
 * Classes: C1 = A0B0 (a edges), C2 = A1B1 (a edges), C3 = A0B1 (b edges), C4 = A1B0 (b edges), b = 7 - a.
 * Lift over group K (table from research/d75-raise/src/export.g): (X,h) ~ (Y, h g) for every voltage g of the class
 * joining base A-vertex X to base B-vertex Y.  Every class is invariant under alpha (automorphism of K of prime
 * order p, listed by export.g), so (X,h) -> (X, alpha h) is an automorphism of the lift.  Left translations
 * (X,h) -> (X,u h) are automorphisms too, so the lift has diameter <= 5 iff the BFS ball of radius 5 around each of
 * the 4 vertices (X,1) is everything.
 * COST = sum over X of #{vertices at distance > 5 from (X,1)}  (0 = valid, counted over ordered base-source pairs).
 * usage: c3s FILE.ht a ALPHAIDX SECS SEED [EDGES_OUT]
 * Output lines: "BEST cost ..." and, on cost 0, "SOL ..." plus the edge file if EDGES_OUT given.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <stdint.h>
#include <math.h>

static int n;
static uint16_t *mul;
static int *inv;
static int nalpha; static int alp_p[64]; static int *alp[64];

static int rdint(FILE *f) { int x; if (fscanf(f, "%d", &x) != 1) { fprintf(stderr, "read error\n"); exit(1); } return x; }

static void load(const char *path) {
    FILE *f = fopen(path, "r"); if (!f) { perror(path); exit(1); }
    n = rdint(f); (void)rdint(f);
    mul = malloc(sizeof(uint16_t) * n * n); inv = malloc(sizeof(int) * n);
    for (int i = 0; i < n * n; i++) mul[i] = (uint16_t)rdint(f);
    for (int i = 0; i < n; i++) inv[i] = rdint(f);
    char w[32];
    while (fscanf(f, "%31s", w) == 1) {
        if (!strcmp(w, "ALPHA")) {
            int p = rdint(f); int *perm = malloc(sizeof(int) * n);
            for (int i = 0; i < n; i++) perm[i] = rdint(f);
            if (fscanf(f, "%31s", w) != 1 || strcmp(w, "CENT")) { fprintf(stderr, "format\n"); exit(1); }
            int k = rdint(f);
            for (int j = 0; j < k * n; j++) (void)rdint(f);
            alp_p[nalpha] = p; alp[nalpha] = perm; nalpha++;
            if (nalpha >= 64) break;
        }
    }
    fclose(f);
}

/* alpha orbits */
static int norb; static int *orb_of; static int orb_size[4096]; static int *orb_el[4096];
static int *sz1, nsz1, *szp, nszp;
static int P;

static void build_orbits(const int *perm) {
    orb_of = malloc(sizeof(int) * n); for (int i = 0; i < n; i++) orb_of[i] = -1;
    norb = 0; nsz1 = nszp = 0; sz1 = malloc(sizeof(int) * n); szp = malloc(sizeof(int) * n);
    for (int x = 0; x < n; x++) {
        if (orb_of[x] >= 0) continue;
        int len = 0, y = x; int buf[64];
        do { buf[len++] = y; orb_of[y] = norb; y = perm[y]; } while (y != x && len < 64);
        orb_size[norb] = len; orb_el[norb] = malloc(sizeof(int) * len); memcpy(orb_el[norb], buf, sizeof(int) * len);
        if (len == 1) sz1[nsz1++] = norb; else szp[nszp++] = norb;
        norb++;
    }
}

/* base structure */
static const int Xa[4] = {0, 1, 0, 1};   /* A-endpoint of class */
static const int Xb[4] = {2, 3, 3, 2};   /* B-endpoint of class */
static int S[4];                          /* class sizes */
static int cls_orb[4][8]; static int cls_nslot[4]; static char *incl[4];
static int V[4][8], Vi[4][8];

static void rebuild_class(int c) {
    int k = 0;
    for (int s = 0; s < cls_nslot[c]; s++) {
        int o = cls_orb[c][s];
        for (int j = 0; j < orb_size[o]; j++) { V[c][k] = orb_el[o][j]; k++; }
    }
    for (int j = 0; j < k; j++) Vi[c][j] = inv[V[c][j]];
}

static uint64_t rs = 88172645463325252ULL;
static inline uint64_t rnd64(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline double urand(void) { return (rnd64() >> 11) * (1.0 / 9007199254740992.0); }

/* initial random state: each class is a union of alpha-orbits with total size S[c]; returns 0 if infeasible */
static int init_state(void) {
    for (int c = 0; c < 4; c++) {
        incl[c] = calloc(norb, 1); cls_nslot[c] = 0;
        int opts[16], no = 0;
        for (int j = 0; j * P <= S[c]; j++) {
            int i = S[c] - j * P;
            if (i <= nsz1 && j <= nszp) opts[no++] = j;
        }
        if (no == 0) return 0;
        int j = opts[rnd64() % no];
        int i = S[c] - j * P;
        for (int t = 0; t < i; t++) {
            int o; do { o = sz1[rnd64() % nsz1]; } while (incl[c][o]);
            incl[c][o] = 1; cls_orb[c][cls_nslot[c]++] = o;
        }
        for (int t = 0; t < j; t++) {
            int o; do { o = szp[rnd64() % nszp]; } while (incl[c][o]);
            incl[c][o] = 1; cls_orb[c][cls_nslot[c]++] = o;
        }
        rebuild_class(c);
    }
    return 1;
}

/* BFS ball around (X,1) of radius 5 over the lift */
static int *vis; static int epoch = 0; static int *q;
static int nbT[4][8]; static int nbG[4][8];   /* neighbour type / multiplier list per type, deg 7 */
static void build_nb(void) {
    for (int X = 0; X < 4; X++) {
        int k = 0;
        for (int c = 0; c < 4; c++) {
            if (Xa[c] == X) for (int j = 0; j < S[c]; j++) { nbT[X][k] = Xb[c]; nbG[X][k] = V[c][j]; k++; }
            if (Xb[c] == X) for (int j = 0; j < S[c]; j++) { nbT[X][k] = Xa[c]; nbG[X][k] = Vi[c][j]; k++; }
        }
    }
}
static int ball(int X0) {
    if (++epoch == 0x7fffffff) { memset(vis, 0, sizeof(int) * 4 * n); epoch = 1; }
    int head = 0, tail = 0; int src = X0 * n;
    vis[src] = epoch; q[tail++] = src;
    for (int d = 0; d < 5 && head < tail; d++) {
        int lend = tail;
        while (head < lend) {
            int v = q[head++]; int X = v / n, h = v - X * n;
            const uint16_t *row = mul + (size_t)h * n;
            for (int j = 0; j < 7; j++) {
                int w = nbT[X][j] * n + row[nbG[X][j]];
                if (vis[w] != epoch) { vis[w] = epoch; q[tail++] = w; }
            }
        }
    }
    return tail;
}
static long long evals = 0;
static int cost(void) {
    evals++;
    int c = 0;
    for (int X = 0; X < 4; X++) c += 4 * n - ball(X);
    return c;
}

static void write_edges(const char *path) {
    FILE *f = fopen(path, "w"); if (!f) { perror(path); exit(1); }
    fprintf(f, "%d\n", 4 * n);
    for (int c = 0; c < 4; c++) for (int j = 0; j < S[c]; j++) for (int h = 0; h < n; h++)
        fprintf(f, "%d %d\n", Xa[c] * n + h, Xb[c] * n + mul[(size_t)h * n + V[c][j]]);
    fclose(f);
}

int main(int argc, char **argv) {
    if (argc < 6) { fprintf(stderr, "usage: c3s FILE.ht a ALPHAIDX SECS SEED [EDGES_OUT]\n"); return 1; }
    load(argv[1]);
    int a = atoi(argv[2]); int ai = atoi(argv[3]); double secs = atof(argv[4]);
    rs ^= (uint64_t)atoll(argv[5]) * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 20; i++) rnd64();
    const char *eout = argc > 6 ? argv[6] : NULL;
    if (ai >= nalpha) { fprintf(stderr, "no alpha %d\n", ai); return 1; }
    int b = 7 - a;
    S[0] = a; S[1] = a; S[2] = b; S[3] = b;
    if (ai >= 0) { P = alp_p[ai]; build_orbits(alp[ai]); }
    else { /* ai = -1: no symmetry (identity), plain random voltages */
        int *idp = malloc(sizeof(int) * n); for (int i = 0; i < n; i++) idp[i] = i;
        P = 1; build_orbits(idp); }
    if (!init_state()) { printf("INFEASIBLE n=%d a=%d alpha=%d p=%d fix=%d\n", n, a, ai, P, nsz1); return 0; }
    vis = calloc(4 * n, sizeof(int)); q = malloc(sizeof(int) * 4 * n);
    build_nb();
    int cur = cost(); int best = cur;
    int bestcls[4][8]; int bestn[4];
    memcpy(bestcls, cls_orb, sizeof(bestcls)); memcpy(bestn, cls_nslot, sizeof(bestn));
    struct timespec t0, t1; clock_gettime(CLOCK_MONOTONIC, &t0);
    double T0 = 2.0, T1 = 0.05, el = 0; long long it = 0;
    int found = (cur == 0);
    while (!found) {
        if ((it & 255) == 0) {
            clock_gettime(CLOCK_MONOTONIC, &t1);
            el = (t1.tv_sec - t0.tv_sec) + 1e-9 * (t1.tv_nsec - t0.tv_nsec);
            if (el >= secs) break;
        }
        double T = T0 * pow(T1 / T0, el / secs);
        it++;
        int c = rnd64() % 4;
        if (cls_nslot[c] == 0) continue;
        int s = rnd64() % cls_nslot[c];
        int oold = cls_orb[c][s];
        int sz = orb_size[oold];
        int *L = (sz == 1) ? sz1 : szp; int nL = (sz == 1) ? nsz1 : nszp;
        int onew = -1;
        for (int tries = 0; tries < 50; tries++) {
            int cand = L[rnd64() % nL];
            if (!incl[c][cand]) { onew = cand; break; }
        }
        if (onew < 0) continue;
        /* apply */
        int save_orb = oold; int save_v[8], save_vi[8]; int sn = S[c];
        memcpy(save_v, V[c], sizeof(int) * 8); memcpy(save_vi, Vi[c], sizeof(int) * 8);
        incl[c][oold] = 0; incl[c][onew] = 1; cls_orb[c][s] = onew; rebuild_class(c); build_nb();
        int nc = cost();
        int d = nc - cur;
        if (d <= 0 || urand() < exp(-d / T)) {
            cur = nc;
            if (cur < best) {
                best = cur; memcpy(bestcls, cls_orb, sizeof(bestcls)); memcpy(bestn, cls_nslot, sizeof(bestn));
                if (best == 0) found = 1;
            }
        } else {
            incl[c][onew] = 0; incl[c][save_orb] = 1; cls_orb[c][s] = save_orb;
            memcpy(V[c], save_v, sizeof(int) * 8); memcpy(Vi[c], save_vi, sizeof(int) * 8); build_nb();
            (void)sn;
        }
    }
    clock_gettime(CLOCK_MONOTONIC, &t1);
    el = (t1.tv_sec - t0.tv_sec) + 1e-9 * (t1.tv_nsec - t0.tv_nsec);
    printf("BEST cost=%d n=%d a=%d alpha=%d p=%d fix=%d evals=%lld secs=%.1f\n", best, 4 * n, a, ai, P, nsz1, evals, el);
    if (best == 0) {
        /* rebuild best state and print it */
        memcpy(cls_orb, bestcls, sizeof(bestcls)); memcpy(cls_nslot, bestn, sizeof(bestn));
        for (int c = 0; c < 4; c++) rebuild_class(c);
        build_nb();
        printf("SOL a=%d alpha=%d p=%d n=%d classes:", a, ai, P, 4 * n);
        for (int c = 0; c < 4; c++) { printf(" C%d{", c + 1); for (int j = 0; j < S[c]; j++) printf("%s%d", j ? "," : "", V[c][j]); printf("}"); }
        printf("\n");
        if (eout) { write_edges(eout); printf("EDGES %s\n", eout); }
    }
    return 0;
}
