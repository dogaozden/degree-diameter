/* t2design.c: many units on the polygon cover GH(q) + j matchings over Z_m (DGQ lift) with the "type-2" design.
   Session cell-14-7 (second session), 2026-10-24.

   Unit (p, t) with l = sigma_t(p) a line THROUGH p (incident flag). It deletes the lifted edges (p,c) ~ (l,c+h_t)
   and adds hubs z ~ {(p,c)}, z' ~ {(l,c)}. Let
       W = points at distance 2 from p, not on l          (q lines through p other than l, q points each: q^2)
       K = lines at distance 2 from l, not through p      (q points of l other than p, q lines each: q^2)
   and let sigma_t map W onto K (any bijection). Then:
   - every point y opposite p has a unique line N through y at distance 4 from l (its path to l avoids p), and N meets
     a unique K in K; with w = sigma_t^-1(K): (p,c) -2- (w,c) -hop- (K,c+h) -3- (y,c+h) has length 6;
   - every line T opposite l has a unique point y at distance 4 from p not via l, collinear with a unique w in W;
     (l,c+h) -2- (sigma_t(w),c+h) -hop- (w,c) -1- . -1- (y,c) -1- (T,c) has length 6.
   Everything else the unit endpoints need goes through the hubs or other matchings (README), so the endpoints keep
   eccentricity <= 7. Units of one matching use disjoint W's and K's, no freed point in any W, no freed line in any K.
   Hubs of the same side are kept within distance 6 by a hub graph (line-side hub ~ point-side hub links).

   Usage: t2design GHFILE STATE_IN J NMAX STATE_OUT UNITS_OUT [SEED]
     adds random incident flags on matchings 1..J alternately until NMAX units or no more fit (many failed tries).
     env BOTH=1: also allow a point to be freed on several matchings. SCAN=1: scan all points in random order.
     FLAGS=file: try the flags "p l" of the file on every matching in turn (e.g. a packing from pack.c).
   Output units file: "p t l". Compile: gcc -O3 -march=native -o t2design t2design.c */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

static int P, q, Q1, J, m;
static int32_t *LP, *PL;
static int *sig, *hv;
static uint64_t rs = 0x9E3779B97F4A7C15ULL;
static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndi(int n) { return (int)(rnd() % (uint64_t)n); }

int main(int argc, char **argv) {
    if (argc < 7) { fprintf(stderr, "usage: t2design GHFILE STATE_IN J NMAX STATE_OUT UNITS_OUT [SEED]\n"); return 2; }
    FILE *f = fopen(argv[1], "r"); if (!f || fscanf(f, "%d %d", &P, &q) != 2) return 2; Q1 = q + 1;
    LP = malloc(sizeof(int32_t) * (size_t)P * Q1); PL = malloc(sizeof(int32_t) * (size_t)P * Q1);
    for (size_t i = 0; i < (size_t)P * Q1; i++) if (fscanf(f, "%d", &LP[i]) != 1) return 2;
    fclose(f);
    { int *c = calloc(P, sizeof(int)); for (int l = 0; l < P; l++) for (int k = 0; k < Q1; k++) { int p = LP[l * Q1 + k]; PL[p * Q1 + c[p]++] = l; } free(c); }
    int JJ = atoi(argv[3]), NMAX = atoi(argv[4]);
    if (argc > 7) rs ^= strtoull(argv[7], 0, 10) * 0x2545F4914F6CDD1DULL;
    char buf[256]; int dd;
    f = fopen(argv[2], "r"); if (!f || fscanf(f, "glift %d %d %d %d\n", &dd, &J, &m, &dd) != 4) { fprintf(stderr, "bad state\n"); return 2; }
    if (!fgets(buf, sizeof buf, f)) return 2;
    sig = malloc(sizeof(int) * (size_t)J * P); hv = malloc(sizeof(int) * (size_t)J * P);
    for (int p = 0; p < P; p++) for (int t = 0; t < J; t++) if (fscanf(f, "%d %d", &sig[t * P + p], &hv[t * P + p]) != 2) return 2;
    fclose(f);
    if (JJ > J) JJ = J;
    int both = getenv("BOTH") != NULL;
    /* per matching: usedP (point in some W or freed), usedL (line in some K or freed), freedP, freedL */
    char *usedP = calloc((size_t)J * P, 1), *usedL = calloc((size_t)J * P, 1), *frP = calloc((size_t)J * P, 1), *frL = calloc((size_t)J * P, 1);
    char *anyFr = calloc(P, 1);
    int *fixL = malloc(sizeof(int) * (size_t)J * P); for (size_t i = 0; i < (size_t)J * P; i++) fixL[i] = -1;   /* designed sigma_t(p) */
    int *cntFrOnLine = calloc((size_t)J * P, sizeof(int)), *cntFrLinesAtPoint = calloc((size_t)J * P, sizeof(int));
    int cap = 1 << 20; int *up = malloc(sizeof(int) * cap), *ut = malloc(sizeof(int) * cap), *ul = malloc(sizeof(int) * cap); int nu = 0;
    int *W = malloc(sizeof(int) * Q1 * Q1), *Kl = malloc(sizeof(int) * Q1 * Q1);
    int t = 0; long fails = 0, maxfails = getenv("MAXFAILS") ? atol(getenv("MAXFAILS")) : 20000;
    /* SCAN=1: visit every point in random order (per matching, in turn) and try its lines in random order */
    int scan = getenv("SCAN") != NULL; int *perm = NULL; long sidx = 0, slen = (long)P * JJ;
    if (scan) { perm = malloc(sizeof(int) * P); for (int i = 0; i < P; i++) perm[i] = i;
        for (int i = P - 1; i > 0; i--) { int r = rndi(i + 1); int tmp = perm[i]; perm[i] = perm[r]; perm[r] = tmp; } }
    int lord[64];
    /* FLAGS=file ("p l" per line): try exactly these flags, on every matching 1..J in turn (use BOTH=1 to allow a
       point on several matchings) */
    int nfl = 0, *flp = NULL, *fll = NULL; long fidx = 0;
    if (getenv("FLAGS")) { FILE *ff = fopen(getenv("FLAGS"), "r"); flp = malloc(sizeof(int) * P); fll = malloc(sizeof(int) * P); int a, b;
        while (ff && nfl < P && fscanf(ff, "%d %d", &a, &b) == 2) { flp[nfl] = a; fll[nfl] = b; nfl++; } if (ff) fclose(ff); scan = 0; }
    while (nu < NMAX && (flp ? fidx < (long)nfl * JJ : scan ? sidx < slen * Q1 : fails < maxfails)) {
        int p, l;
        if (flp) { long f2 = fidx++; t = (int)(f2 / nfl); p = flp[f2 % nfl]; l = fll[f2 % nfl]; }
        else if (scan) { long s2 = sidx++; int li = (int)(s2 % Q1); long s3 = s2 / Q1; t = (int)(s3 % JJ); p = perm[(s3 / JJ) % P];
            if (li == 0) { for (int a = 0; a < Q1; a++) lord[a] = a; for (int a = Q1 - 1; a > 0; a--) { int r = rndi(a + 1); int tmp = lord[a]; lord[a] = lord[r]; lord[r] = tmp; } }
            l = PL[p * Q1 + lord[li]]; }
        else { p = rndi(P); l = PL[p * Q1 + rndi(Q1)]; }
        char *uP = usedP + (size_t)t * P, *uL = usedL + (size_t)t * P;
        if (uP[p] || uL[l] || (!both && anyFr[p])) { fails++; continue; }
        /* W and K */
        int nw = 0, nk = 0, ok = 1;
        for (int a = 0; a < Q1 && ok; a++) { int L = PL[p * Q1 + a]; if (L == l) continue;
            for (int b = 0; b < Q1; b++) { int w = LP[L * Q1 + b]; if (w == p) continue; if (uP[w] || frP[(size_t)t * P + w]) { ok = 0; break; } W[nw++] = w; } }
        for (int a = 0; a < Q1 && ok; a++) { int x = LP[l * Q1 + a]; if (x == p) continue;
            for (int b = 0; b < Q1; b++) { int K = PL[x * Q1 + b]; if (K == l) continue; if (uL[K] || frL[(size_t)t * P + K]) { ok = 0; break; } Kl[nk++] = K; } }
        if (!ok) { fails++; continue; }
        /* the new freed point / line must not lie in an existing W / K (checked by usedP/usedL above), and
           DGQ side conditions: no line with all its points freed, no point with all its lines freed (same matching) */
        if (cntFrLinesAtPoint[(size_t)t * P + 0] < 0) {}
        int bad = 0;
        for (int a = 0; a < Q1; a++) { int L = PL[p * Q1 + a]; if (cntFrOnLine[(size_t)t * P + L] + 1 >= Q1) bad = 1; }
        for (int a = 0; a < Q1; a++) { int x = LP[l * Q1 + a]; if (cntFrLinesAtPoint[(size_t)t * P + x] + 1 >= Q1) bad = 1; }
        if (bad) { fails++; continue; }
        /* accept */
        uP[p] = 1; uL[l] = 1; frP[(size_t)t * P + p] = 1; frL[(size_t)t * P + l] = 1; anyFr[p] = 1;
        for (int a = 0; a < Q1; a++) { cntFrOnLine[(size_t)t * P + PL[p * Q1 + a]]++; cntFrLinesAtPoint[(size_t)t * P + LP[l * Q1 + a]]++; }
        fixL[(size_t)t * P + p] = l;
        /* random bijection W -> K */
        for (int i = nk - 1; i > 0; i--) { int r = rndi(i + 1); int tmp = Kl[i]; Kl[i] = Kl[r]; Kl[r] = tmp; }
        for (int i = 0; i < nw; i++) { uP[W[i]] = 1; uL[Kl[i]] = 1; fixL[(size_t)t * P + W[i]] = Kl[i]; }
        up[nu] = p; ut[nu] = t; ul[nu] = l; nu++;
        fails = 0; if (flp) {} else if (!scan) t = (t + 1) % JJ; else sidx = (sidx / Q1 + 1) * Q1;   /* next (point, matching) */
        if (nu % 200 == 0) fprintf(stderr, "  %d units\n", nu);
    }
    /* complete each matching at random */
    for (int tt = 0; tt < J; tt++) {
        char *taken = calloc(P, 1); int *fp = malloc(sizeof(int) * P), *fl = malloc(sizeof(int) * P), nfp = 0, nfl = 0;
        for (int p = 0; p < P; p++) if (fixL[(size_t)tt * P + p] >= 0) { if (taken[fixL[(size_t)tt * P + p]]) { fprintf(stderr, "internal error: line used twice\n"); return 3; } taken[fixL[(size_t)tt * P + p]] = 1; }
        for (int p = 0; p < P; p++) if (fixL[(size_t)tt * P + p] < 0) fp[nfp++] = p;
        for (int L = 0; L < P; L++) if (!taken[L]) fl[nfl++] = L;
        if (nfp != nfl) { fprintf(stderr, "internal error %d %d\n", nfp, nfl); return 3; }
        for (int i = nfl - 1; i > 0; i--) { int r = rndi(i + 1); int tmp = fl[i]; fl[i] = fl[r]; fl[r] = tmp; }
        for (int p = 0; p < P; p++) sig[tt * P + p] = fixL[(size_t)tt * P + p];
        for (int i = 0; i < nfp; i++) sig[tt * P + fp[i]] = fl[i];
        free(taken); free(fp); free(fl);
    }
    f = fopen(argv[5], "w");
    fprintf(f, "glift %d %d %d 7\ncyc %d\n", q, J, m, m);
    for (int p = 0; p < P; p++) { for (int tt = 0; tt < J; tt++) fprintf(f, "%s%d %d", tt ? " " : "", sig[tt * P + p], hv[tt * P + p]); fprintf(f, "\n"); }
    for (int l = 0; l < P; l++) { for (int k = 0; k < Q1; k++) fprintf(f, k ? " 0" : "0"); fprintf(f, "\n"); }
    fclose(f);
    f = fopen(argv[6], "w"); for (int i = 0; i < nu; i++) fprintf(f, "%d %d %d\n", up[i], ut[i] + 1, ul[i]); fclose(f);
    int per[64] = {0}; for (int i = 0; i < nu; i++) per[ut[i]]++;
    fprintf(stderr, "wrote %d units (", nu); for (int tt = 0; tt < J; tt++) fprintf(stderr, "%s%d", tt ? " + " : "", per[tt]); fprintf(stderr, ")\n");
    return 0;
}
