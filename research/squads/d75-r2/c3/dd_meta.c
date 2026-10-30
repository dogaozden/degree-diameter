/* dd_meta.c: self-dual Haar graphs H(G,S) of valency 7 for metacyclic G = C_m : C_k (no GAP, no tables from GAP).
 *
 *   G = <x, y | x^m = y^k = 1, y x y^-1 = x^r>, element (i,j) = x^i y^j, index i*k + j, identity 0,
 *   product (i,j)(a,b) = (i + r^j a, j + b).  Haar graph: (g,A) ~ (s g,B) for s in S.
 *
 * Automorphisms used: phi(x) = x^u, phi(y) = x^t y^v with u a unit mod m, t arbitrary, v a unit mod k with
 * r^v = r mod m (this is exactly the set of relations-respecting maps; surjective iff gcd(v,k) = 1).
 * beta = phi with phi^2 = id (checked on the generators), psi(g) = beta(g)^-1; psi-orbits have size 1 or 2.
 * Sets: S = {e, f1, f2, pair, pair} (type (3,2), f1, f2 psi-fixed) or {e, pair, pair, pair} (type (1,3)), S a union
 * of psi-orbits.  Reduction: f1 (resp. the first pair) is taken up to the centralizer C(beta) in the family
 * (phi(S) is again beta-invariant and gives the same graph); NORED=1 disables it (calibration).
 * Test: X X = G with X = S^-1 S (move-to-front pp_full of haar75.c); then Y Y = G and Y Y S = G (fullcheck).
 * Hits are confirmed by an all-pairs BFS (diameter <= 5, 7-regular).
 *
 * usage: dd_meta one M K R            (one group, prints hits)
 *        dd_meta sweep LO HI [OUTDIR] (all C_p : C_k, p prime, LO <= p*k <= HI, r of each order d | gcd(k,p-1), d > 1)
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

static int M, K, R, N;
static int *rp;
static uint16_t *mt;
static int *ivt;
static uint32_t *mk; static uint32_t stM = 0;
static int *ordA;
static int *vlist, nv;
static int NORED = 0, FULLT = 0;
static long long nsets = 0, npassX = 0, nvalid = 0, nbeta = 0, ninvol = 0;
static char outdir[512] = "";
static int wrote = 0;

static inline int mulf(int a, int b) {
    int i = a / K, j = a % K, c = b / K, d = b % K;
    int ii = (i + rp[j] * c) % M;
    int jj = (j + d) % K;
    return ii * K + jj;
}
static inline int mulT(int a, int b) { return mt[(size_t)a * N + b]; }

static int gcd(int a, int b) { while (b) { int t = a % b; a = b; b = t; } return a; }

static void setup(int m, int k, int r) {
    M = m; K = k; R = r; N = m * k;
    rp = realloc(rp, sizeof(int) * K);
    rp[0] = 1 % M;
    for (int j = 1; j < K; j++) rp[j] = (rp[j - 1] * r) % M;
    mt = realloc(mt, sizeof(uint16_t) * (size_t)N * N);
    for (int a = 0; a < N; a++) for (int b = 0; b < N; b++) mt[(size_t)a * N + b] = (uint16_t)mulf(a, b);
    ivt = realloc(ivt, sizeof(int) * N);
    for (int a = 0; a < N; a++) { ivt[a] = -1; for (int b = 0; b < N; b++) if (mt[(size_t)a * N + b] == 0) { ivt[a] = b; break; } }
    mk = realloc(mk, sizeof(uint32_t) * N); memset(mk, 0, sizeof(uint32_t) * N); stM = 0;
    ordA = realloc(ordA, sizeof(int) * N); for (int i = 0; i < N; i++) ordA[i] = i;
    vlist = realloc(vlist, sizeof(int) * K); nv = 0;
    for (int v = 0; v < K; v++) if (gcd(v, K) == 1 && rp[v] == R % M) vlist[nv++] = v;
}

/* X X = G test (left=1: X = S^-1 S; left=0: X = S S^-1) with move-to-front target order (haar75 pp_full) */
static int pp_full(const int *S, int k, int left) {
    int X[64], nx = 0; stM++;
    for (int i = 0; i < k; i++) for (int j = 0; j < k; j++) {
        int x = left ? mulT(ivt[S[i]], S[j]) : mulT(S[i], ivt[S[j]]);
        if (mk[x] != stM) { mk[x] = stM; X[nx++] = x; }
    }
    int ix[64];
    for (int i = 0; i < nx; i++) ix[i] = ivt[X[i]];
    for (int t = 0; t < N; t++) {
        int z = ordA[t], ok = 0;
        for (int i = 0; i < nx; i++) if (mk[mulT(ix[i], z)] == stM) { ok = 1; break; }
        if (!ok) { if (t) { int u = t / 2; ordA[t] = ordA[u]; ordA[u] = z; } return 0; }
    }
    return 1;
}

/* full check: Y Y = G and Y Y S = G */
static int fullcheck(const int *S, int k) {
    if (!pp_full(S, k, 0)) return 0;
    int Y[64], ny = 0; stM++;
    for (int i = 0; i < k; i++) for (int j = 0; j < k; j++) { int y = mulT(S[i], ivt[S[j]]); if (mk[y] != stM) { mk[y] = stM; Y[ny++] = y; } }
    static uint32_t *yy = NULL, *cov = NULL, sy = 0; static int cap = 0;
    if (cap < N) { yy = realloc(yy, sizeof(uint32_t) * N); cov = realloc(cov, sizeof(uint32_t) * N); memset(yy, 0, sizeof(uint32_t) * N); memset(cov, 0, sizeof(uint32_t) * N); cap = N; }
    sy++;
    for (int i = 0; i < ny; i++) for (int j = 0; j < ny; j++) yy[mulT(Y[i], Y[j])] = sy;
    sy++;
    int cnt = 0;
    for (int z = 0; z < N; z++) if (yy[z] == sy - 1) for (int i = 0; i < k; i++) { int w = mulT(z, S[i]); if (cov[w] != sy) { cov[w] = sy; cnt++; } }
    return cnt == N;
}

/* BFS all pairs on H(G,S): 7-regular bipartite, diameter */
static int diam_of(const int *S, int k, int *degok) {
    int V = 2 * N;
    int *adj = malloc(sizeof(int) * V * k), *deg = calloc(V, sizeof(int));
    for (int g = 0; g < N; g++) for (int i = 0; i < k; i++) {
        int b = N + mulT(S[i], g);
        adj[g * k + deg[g]++] = b; adj[b * k + deg[b]++] = g;
    }
    *degok = 1;
    int *dist = malloc(sizeof(int) * V), *q = malloc(sizeof(int) * V), D = 0;
    for (int v = 0; v < V; v++) if (deg[v] != k) *degok = 0;
    for (int s = 0; s < V; s++) {
        for (int v = 0; v < V; v++) dist[v] = -1;
        int h = 0, t = 0; q[t++] = s; dist[s] = 0;
        while (h < t) { int u = q[h++]; for (int i = 0; i < deg[u]; i++) { int w = adj[u * k + i]; if (dist[w] < 0) { dist[w] = dist[u] + 1; q[t++] = w; } } }
        if (t < V) { D = -1; break; }
        if (dist[q[t - 1]] > D) D = dist[q[t - 1]];
    }
    free(adj); free(deg); free(dist); free(q);
    return D;
}

static void write_edges(const char *path, const int *S, int k) {
    FILE *f = fopen(path, "w"); if (!f) { perror(path); return; }
    fprintf(f, "%d\n", 2 * N);
    for (int g = 0; g < N; g++) for (int i = 0; i < k; i++) fprintf(f, "%d %d\n", g, N + mulT(S[i], g));
    fclose(f);
}

/* state for one beta */
static int *img, *psi, *posF, *orbid, *orbA, *orbB, *fixl, nfix, npair, *uf;
static int *gphi, *gbeta;
static int *cA, *cT, *cV;
static int *gtmp;
static int findr(int x) { while (uf[x] != x) { uf[x] = uf[uf[x]]; x = uf[x]; } return x; }
static void unite(int a, int b) { a = findr(a); b = findr(b); if (a != b) { if (a < b) uf[b] = a; else uf[a] = b; } }

static void mkgyp(int t, int v, int *g) {
    int gy = t * K + v; g[0] = 0;
    for (int j = 1; j < K; j++) g[j] = mulf(g[j - 1], gy);
}
static inline int app(int u, const int *g, int e) {
    int i = e / K, j = e % K;
    return mulf(((u * i) % M) * K, g[j]);
}

static long long nhit_beta = 0;
static int bestN = 0;

static void print_set(const char *tag, const int *S, int k) {
    printf("HIT %s", tag);
    for (int i = 0; i < k; i++) printf(" %d,%d", S[i] / K, S[i] % K);
    printf("\n");
}

static void test_set(const int *S, int k, const char *tag) {
    nsets++;
    if (!pp_full(S, k, 1)) return;
    npassX++;
    if (!fullcheck(S, k)) return;
    int dok = 0, D = diam_of(S, k, &dok);
    if (!dok || D > 5) { printf("NOTE xx-yys-pass but diam %d deg %d (tag %s)\n", D, dok, tag); return; }
    nvalid++; nhit_beta++;
    if (nhit_beta <= 4 || N > bestN) { print_set(tag, S, k); }
    if (outdir[0] && (getenv("EDGESALL") || N > bestN)) {
        char path[700]; snprintf(path, sizeof path, "%s/hit_%d_%d_%d_%lld.edges", outdir, M, K, R, nvalid);
        if (getenv("EDGESALL") || !wrote) { write_edges(path, S, k); wrote = 1; }
    }
    if (N > bestN) bestN = N;
}

/* all involutory automorphisms of the family, their psi-orbit structure, and the enumeration */
static void do_beta(int u, int t, int v) {
    int *g = gphi; mkgyp(t, v, g);
    /* involution check on generators: phi(phi(x)) = x, phi(phi(y)) = y */
    int x = K, y = 1;
    if (app(u, g, app(u, g, x)) != x || app(u, g, app(u, g, y)) != y) return;
    for (int e = 0; e < N; e++) img[e] = app(u, g, e);
    for (int e = 0; e < N; e++) if (img[img[e]] != e) { fprintf(stderr, "not involution at %d\n", e); return; }
    ninvol++;
    for (int e = 0; e < N; e++) psi[e] = ivt[img[e]];
    for (int e = 0; e < N; e++) if (psi[psi[e]] != e) { fprintf(stderr, "psi not involution\n"); return; }
    /* psi-fixed (non-identity) and pair orbits */
    nfix = 0; npair = 0;
    for (int e = 0; e < N; e++) posF[e] = -1;
    for (int e = 1; e < N; e++) if (psi[e] == e) { posF[e] = nfix; fixl[nfix++] = e; }
    for (int e = 1; e < N; e++) orbid[e] = -1;
    for (int e = 1; e < N; e++) if (psi[e] > e) { orbA[npair] = e; orbB[npair] = psi[e]; orbid[e] = npair; orbid[psi[e]] = npair; npair++; }
    if (nfix < 2 && npair < 3) return;
    /* centralizer of beta in the family (on generators) */
    for (int i = 0; i < nfix + npair; i++) uf[i] = i;
    /* union-find: fixed elements use indices 0..nfix-1, pair orbits use nfix..nfix+npair-1 */
    int ncent = 0;
    if (!NORED) {
        int *h = gbeta; mkgyp(t, v, h);   /* h = gbeta (table of beta powers) */
        for (int a = 0; a < M; a++) {
            if (gcd(a, M) != 1) continue;
            for (int tt = 0; tt < M; tt++) for (int vi = 0; vi < nv; vi++) {
                int vv = vlist[vi];
                int *gp = gphi; mkgyp(tt, vv, gp);
                /* phi(beta(x)) = beta(phi(x)), phi(beta(y)) = beta(phi(y)) */
                int bxx = app(u, h, K);            /* beta(x) index */
                int pbx = app(a, gp, bxx);         /* phi(beta(x)) */
                int px = app(a, gp, K);            /* phi(x) */
                int bpx = app(u, h, px);           /* beta(phi(x)) */
                if (pbx != bpx) continue;
                int byy = app(u, h, 1);
                int pby = app(a, gp, byy);
                int py = app(a, gp, 1);
                int bpy = app(u, h, py);
                if (pby != bpy) continue;
                cA[ncent] = a; cT[ncent] = tt; cV[ncent] = vv; ncent++;
                /* act on fixed elements and pair orbits */
                for (int f = 0; f < nfix; f++) { int f2 = app(a, gp, fixl[f]); if (posF[f2] < 0) { fprintf(stderr, "centralizer maps fixed out\n"); exit(2); } unite(f, posF[f2]); }
                for (int o = 0; o < npair; o++) { int o2 = orbid[app(a, gp, orbA[o])]; unite(nfix + o, nfix + o2); }
            }
        }
    }
    /* reps */
    int *isrepF = malloc(sizeof(int) * (nfix + 1)), *isrepP = malloc(sizeof(int) * (npair + 1));
    int nrepF = 0, nrepP = 0;
    if (NORED) for (int i = 0; i < nfix + npair; i++) uf[i] = i;
    for (int f = 0; f < nfix; f++) { isrepF[f] = (findr(f) == f); nrepF += isrepF[f]; }
    for (int o = 0; o < npair; o++) { isrepP[o] = (findr(nfix + o) == nfix + o); nrepP += isrepP[o]; }
    /* (3,2): f1 = orbit rep among fixed elements; pair orbit o1 = rep under Stab(f1) in C(beta); f2, o2 any */
    long long ns32 = 0;
    if (nfix >= 2) {
        char tag[200];
        snprintf(tag, sizeof tag, "beta(%d,%d,%d) p(3,2)", u, t, v);
        int *uf2 = malloc(sizeof(int) * (npair + 1)), *isrepS = malloc(sizeof(int) * (npair + 1));
        for (int f1 = 0; f1 < nfix; f1++) if (isrepF[f1]) {
            for (int o = 0; o < npair; o++) uf2[o] = o;
            for (int c = 0; c < ncent; c++) {
                mkgyp(cT[c], cV[c], gtmp);
                if (app(cA[c], gtmp, fixl[f1]) != fixl[f1]) continue;   /* stabilizer of f1 */
                for (int o = 0; o < npair; o++) {
                    int o2 = orbid[app(cA[c], gtmp, orbA[o])];
                    int r1 = o, r2 = o2; while (uf2[r1] != r1) r1 = uf2[r1]; while (uf2[r2] != r2) r2 = uf2[r2];
                    if (r1 != r2) { if (r1 < r2) uf2[r2] = r1; else uf2[r1] = r2; }
                }
            }
            for (int o = 0; o < npair; o++) { int r = o; while (uf2[r] != r) r = uf2[r]; isrepS[o] = (r == o); }
            for (int f2 = 0; f2 < nfix; f2++) if (f2 != f1) for (int o1 = 0; o1 < npair; o1++) if (isrepS[o1])
                for (int o2 = 0; o2 < npair; o2++) if (o2 != o1) {
                    int S[7] = { 0, fixl[f1], fixl[f2], orbA[o1], orbB[o1], orbA[o2], orbB[o2] };
                    test_set(S, 7, tag); ns32++;
                }
        }
        free(uf2); free(isrepS);
    }
    /* (1,3): first pair-orbit = orbit rep, other two any */
    long long ns13 = 0;
    if (npair >= 3) {
        char tag[200];
        snprintf(tag, sizeof tag, "beta(%d,%d,%d) p(1,3)", u, t, v);
        for (int o1 = 0; o1 < npair; o1++) if (isrepP[o1]) for (int o2 = 0; o2 < npair; o2++) if (o2 != o1) for (int o3 = o2 + 1; o3 < npair; o3++) if (o3 != o1) {
            int S[7] = { 0, orbA[o1], orbB[o1], orbA[o2], orbB[o2], orbA[o3], orbB[o3] };
            test_set(S, 7, tag); ns13++;
        }
    }
    nbeta++;
    if (getenv("VERBOSE")) { printf("beta(%d,%d,%d): nfix %d npair %d centralizer %d reps F %d P %d sets32 %lld sets13 %lld nvalid %lld\n", u, t, v, nfix, npair, ncent, nrepF, nrepP, ns32, ns13, nvalid); fflush(stdout); }
    free(isrepF); free(isrepP);
}

static void run_group(int m, int k, int r) {
    setup(m, k, r);
    img = malloc(sizeof(int) * N); psi = malloc(sizeof(int) * N); posF = malloc(sizeof(int) * N);
    orbid = malloc(sizeof(int) * N); orbA = malloc(sizeof(int) * N); orbB = malloc(sizeof(int) * N);
    fixl = malloc(sizeof(int) * N); uf = malloc(sizeof(int) * (2 * N + 2));
    gphi = malloc(sizeof(int) * K); gbeta = malloc(sizeof(int) * K);
    nvalid = 0; nbeta = 0; ninvol = 0; nsets = 0; npassX = 0; bestN = 0; wrote = 0;
    long long nsets0 = nsets;
    cA = malloc(sizeof(int) * ((size_t)M * M * nv + 1)); cT = malloc(sizeof(int) * ((size_t)M * M * nv + 1));
    cV = malloc(sizeof(int) * ((size_t)M * M * nv + 1)); gtmp = malloc(sizeof(int) * K);
    for (int u = 1; u < M; u++) {
        if (gcd(u, M) != 1 || (u * u) % M != 1 % M) continue;   /* beta^2(x) = x forces u^2 = 1 */
        /* u = -1: x -> x^-1, y -> x^t y^v is conjugate (by x^a: y -> x^{a(1-r)} y) to t = 0 when 2 and 1-r are units */
        int tmax = (u == M - 1 && !FULLT) ? 1 : M;
        for (int t = 0; t < tmax; t++) for (int vi = 0; vi < nv; vi++) do_beta(u, t, vlist[vi]);
    }
    free(cA); free(cT); free(cV); free(gtmp);
    (void)nsets0;
    free(img); free(psi); free(posF); free(orbid); free(orbA); free(orbB); free(fixl); free(uf); free(gphi); free(gbeta);
}

static int isprime(int n) { if (n < 2) return 0; for (int d = 2; d * d <= n; d++) if (n % d == 0) return 0; return 1; }
static int order_mod(int r, int p) { int x = r % p, o = 1; while (x != 1) { x = (x * r) % p; o++; } return o; }

int main(int argc, char **argv) {
    if (argc < 2) { fprintf(stderr, "usage: dd_meta one M K R | sweep LO HI [OUTDIR]\n"); return 2; }
    NORED = getenv("NORED") ? atoi(getenv("NORED")) : 0;
    FULLT = getenv("FULLT") ? atoi(getenv("FULLT")) : 0;
    clock_t c0 = clock();
    if (!strcmp(argv[1], "one")) {
        int m = atoi(argv[2]), k = atoi(argv[3]), r = atoi(argv[4]);
        if (argc > 5) strncpy(outdir, argv[5], sizeof outdir - 1);
        run_group(m, k, r);
        printf("GROUP %d %d %d n %d invol %lld betas %lld valid %lld sets %lld passXX %lld secs %.2f\n", m, k, r, m * k, ninvol, nbeta, nvalid, nsets, npassX,
               (double)(clock() - c0) / CLOCKS_PER_SEC);
        return 0;
    }
    if (!strcmp(argv[1], "sweep")) {
        int lo = atoi(argv[2]), hi = atoi(argv[3]);
        if (argc > 4) strncpy(outdir, argv[4], sizeof outdir - 1);
        long long ng = 0, nvalidg = 0, bestn = 0;
        for (int p = 3; p <= hi; p++) {
            if (!isprime(p)) continue;
            for (int k = 2; p * k <= hi; k++) {
                if (p * k < lo) continue;
                int g = gcd(k, p - 1);
                for (int d = 2; d <= g; d++) {
                    if (g % d) continue;
                    if (getenv("PMIN") && p < atoi(getenv("PMIN"))) continue;
                    if (getenv("K2D") && k != 2 * d) continue;
                    if (getenv("PMAX") && p > atoi(getenv("PMAX"))) continue;
                    /* r of exact order d mod p */
                    int r = -1;
                    for (int c = 2; c < p; c++) if (order_mod(c, p) % 1 == 0) { if (order_mod(c, p) == d) { r = c; break; } }
                    if (r < 0) continue;
                    clock_t t0 = clock();
                    long long v0 = nvalid;
                    run_group(p, k, r);
                    ng++;
                    if (nvalid > v0) {
                        nvalidg++; if (p * k * 2 > bestn) bestn = p * k * 2;
                        printf("VALID-GROUP p %d k %d r %d n %d valid %lld\n", p, k, r, p * k, nvalid - v0);
                    }
                    if (getenv("VERBOSE") || (clock() - t0) > 2 * CLOCKS_PER_SEC)
                        printf("done p %d k %d r %d n %d invol %lld betas %lld sets %lld passXX %lld secs %.2f\n", p, k, r, p * k, ninvol, nbeta, nsets, npassX,
                               (double)(clock() - t0) / CLOCKS_PER_SEC);
                    fflush(stdout);
                }
            }
        }
        printf("SWEEP done groups %lld with-valid %lld best-vertices %lld secs %.1f\n", ng, nvalidg, bestn, (double)(clock() - c0) / CLOCKS_PER_SEC);
        return 0;
    }
    return 2;
}
