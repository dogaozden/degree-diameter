/* c5_sym.c: card c5 (squad d14D7-r2, session cell-14-7 second). Monomial automorphisms of H(11) in Tits
   coordinates, and orbit-level packings of type-2 flags (zones as in cell147/units/pack.c) that are unions of
   orbits of a chosen subgroup H of the automorphism group.

   Usage:
     c5_sym auts AUTFILE
         enumerates all monomial 7x7 matrices M (g e_i = d_i e_{pi_i}) that preserve x0x4+x1x5+x2x6-x3^2
         (pi must preserve the partition {0,4},{1,5},{2,6},{3}; d_3 = 1, d_{i} d_{partner(i)} = 1) and keeps those
         that map every hexagon line to a line. Writes one line per automorphism: "pi0..pi6 d0..d6".
     c5_sym orb AUTFILE GENS SECS SEED OUTFLAGS [LAM0 LAM1 T0 T1]
         GENS = comma list of 0-based indices into AUTFILE, or "all". H = <GENS>. Computes the flag orbits of H,
         keeps the orbits whose own flags have pairwise disjoint zones, and runs simulated annealing over unions
         of orbits (energy = -#flags + lambda * #overlaps). Writes the best valid flag set (lines "p l").
   Points/lines: data/gh_11.txt (P q, then P lines of q+1 point ids); Tits coordinates: c5_COORDS11.txt
   (written by `gh_build 11 COORDS`).
   Compile: gcc -O2 -o c5_sym c5_sym.c -lm */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define QQ 11
#define Q1 12
#define NCO 7
#define GHFILE "/home/user/degree-diameter/research/cell147/data/gh_11.txt"
#define COORDFILE "/home/user/degree-diameter/research/squads/d14D7-r2/c5/c5_COORDS11.txt"

static int P;
static int *X, *LP, *PL;     /* X: P*7 coords; LP[l*12+k]: points on line l; PL[p*12+k]: lines through p */
static int32_t *idxtab;      /* QQ^7 -> point index */
static int inv11[QQ];

typedef struct { int pi[NCO]; int d[NCO]; } Mono;   /* g e_i = d_i e_{pi_i} */

static void load(void) {
    FILE *f = fopen(GHFILE, "r"); int q;
    if (!f || fscanf(f, "%d %d", &P, &q) != 2 || q != QQ) { fprintf(stderr, "bad GH file\n"); exit(2); }
    LP = malloc(sizeof(int) * (size_t)P * Q1); PL = malloc(sizeof(int) * (size_t)P * Q1);
    for (size_t i = 0; i < (size_t)P * Q1; i++) if (fscanf(f, "%d", &LP[i]) != 1) { fprintf(stderr, "bad GH body\n"); exit(2); }
    fclose(f);
    f = fopen(COORDFILE, "r"); X = malloc(sizeof(int) * (size_t)P * NCO);
    for (size_t i = 0; i < (size_t)P * NCO; i++) if (fscanf(f, "%d", &X[i]) != 1) { fprintf(stderr, "bad coords\n"); exit(2); }
    fclose(f);
    for (int a = 1; a < QQ; a++) { for (int b = 1; b < QQ; b++) if (a * b % QQ == 1) inv11[a] = b; }
    long long tot = 1; for (int i = 0; i < NCO; i++) tot *= QQ;
    idxtab = malloc(sizeof(int32_t) * (size_t)tot); for (long long i = 0; i < tot; i++) idxtab[i] = -1;
    for (int p = 0; p < P; p++) {   /* normalized coordinates (first nonzero = 1) -> index */
        int v[NCO]; for (int i = 0; i < NCO; i++) v[i] = X[p * NCO + i];
        int fi = -1; for (int i = 0; i < NCO; i++) if (v[i]) { fi = i; break; }
        if (fi < 0 || v[fi] != 1) { fprintf(stderr, "coords not normalized at %d\n", p); exit(2); }
        long long e = 0; for (int i = 0; i < NCO; i++) e = e * QQ + v[i];
        idxtab[e] = p;
    }
    int *cnt = calloc(P, sizeof(int));
    for (int l = 0; l < P; l++) for (int k = 0; k < Q1; k++) { int p = LP[l * Q1 + k]; PL[p * Q1 + cnt[p]++] = l; }
    for (int p = 0; p < P; p++) if (cnt[p] != Q1) { fprintf(stderr, "point %d has %d lines\n", p, cnt[p]); exit(2); }
    free(cnt);
}

static int lookup_vec(const int *v) {   /* entries in [0,QQ): normalize, return point index or -1 */
    int fi = -1; for (int i = 0; i < NCO; i++) if (v[i]) { fi = i; break; }
    if (fi < 0) return -1;
    int s = inv11[v[fi]]; long long e = 0;
    for (int i = 0; i < NCO; i++) e = e * QQ + (v[i] * s) % QQ;
    return idxtab[e];
}
static int image_point(const Mono *g, int p) {
    int y[NCO] = {0}; const int *x = X + NCO * p;
    for (int i = 0; i < NCO; i++) y[g->pi[i]] = (g->d[i] * x[i]) % QQ;
    return lookup_vec(y);
}

/* memo of point images for the current element */
static int *memoV; static unsigned *memoS; static unsigned curS = 0;
static inline int imgP(const Mono *g, int p) {
    if (memoS[p] == curS) return memoV[p];
    int r = image_point(g, p); memoS[p] = curS; memoV[p] = r; return r;
}
/* g is an automorphism iff every line maps onto a line; permL (optional) receives the line images; the point
   images are left in the memo (memoV/memoS with the current stamp). */
static int aut_test(const Mono *g, int *permL) {
    curS++;
    int nl = getenv("SCREEN") ? atoi(getenv("SCREEN")) : P; if (nl > P) nl = P;
    for (int i = 0; i < nl; i++) { int l = nl == P ? i : (int)(((long long)i * 591) % P);
        int a[Q1];
        for (int k = 0; k < Q1; k++) { a[k] = imgP(g, LP[l * Q1 + k]); if (a[k] < 0) return 0; }
        int found = -1;
        for (int j = 0; j < Q1 && found < 0; j++) {
            int L2 = PL[a[0] * Q1 + j];
            for (int k = 0; k < Q1; k++) if (LP[L2 * Q1 + k] == a[1]) { found = L2; break; }
        }
        if (found < 0) return 0;
        for (int k = 2; k < Q1; k++) {
            int ok = 0; for (int m = 0; m < Q1; m++) if (LP[found * Q1 + m] == a[k]) { ok = 1; break; }
            if (!ok) return 0;
        }
        if (permL) permL[l] = found;
    }
    return 1;
}

static void mono_mul(const Mono *h, const Mono *g, Mono *out) {   /* out = h after g */
    for (int i = 0; i < NCO; i++) { out->pi[i] = h->pi[g->pi[i]]; out->d[i] = (g->d[i] * h->d[g->pi[i]]) % QQ; }
}
static int mono_eq(const Mono *a, const Mono *b) { return memcmp(a, b, sizeof(Mono)) == 0; }
static int mono_order(const Mono *g) {
    Mono c = *g; int k = 1;
    for (;;) { int id = 1; for (int i = 0; i < NCO; i++) if (c.pi[i] != i || c.d[i] != 1) { id = 0; break; } if (id) return k; Mono t; mono_mul(g, &c, &t); c = t; k++; }
}

static int partner(int i) { return i < 3 ? i + 4 : (i > 3 ? i - 4 : 3); }

/* closure of a set of monomial elements (BFS with a hash set); returns number of elements, stored in *out */
#define HSZ (1u << 18)
static uint64_t mkey(const Mono *g) { uint64_t k = 0; for (int i = 0; i < NCO; i++) k = k * 8 + g->pi[i]; for (int i = 0; i < NCO; i++) k = k * 16 + g->d[i]; return k + 1; }
static int closure(Mono *gens, int ng, Mono **out, int cap) {
    Mono *el = malloc(sizeof(Mono) * cap); int n = 0;
    uint64_t *hk = calloc(HSZ, sizeof(uint64_t));
    Mono id; for (int i = 0; i < NCO; i++) { id.pi[i] = i; id.d[i] = 1; }
    el[n++] = id; { uint64_t k = mkey(&id); uint32_t s = (uint32_t)(k * 0x9E3779B97F4A7C15ULL >> 46) & (HSZ - 1); while (hk[s]) s = (s + 1) & (HSZ - 1); hk[s] = k; }
    for (int h = 0; h < n; h++) for (int j = 0; j < ng; j++) {
        Mono t; mono_mul(&gens[j], &el[h], &t);
        uint64_t k = mkey(&t); uint32_t s = (uint32_t)(k * 0x9E3779B97F4A7C15ULL >> 46) & (HSZ - 1); int f = 0;
        while (hk[s]) { if (hk[s] == k) { f = 1; break; } s = (s + 1) & (HSZ - 1); }
        if (!f) { if (n >= cap) { fprintf(stderr, "closure overflow\n"); exit(3); } hk[s] = k; el[n++] = t; }
    }
    free(hk); *out = el; return n;
}

static int read_auts(const char *fn, Mono **A) {
    FILE *f = fopen(fn, "r"); if (!f) { fprintf(stderr, "no %s\n", fn); exit(2); }
    int cap = 4096, n = 0; Mono *a = malloc(sizeof(Mono) * cap);
    while (1) {
        Mono m; int ok = 1;
        for (int i = 0; i < NCO && ok; i++) if (fscanf(f, "%d", &m.pi[i]) != 1) ok = 0;
        for (int i = 0; i < NCO && ok; i++) if (fscanf(f, "%d", &m.d[i]) != 1) ok = 0;
        if (!ok) break;
        if (n == cap) { cap *= 2; a = realloc(a, sizeof(Mono) * cap); }
        a[n++] = m;
    }
    fclose(f); *A = a; return n;
}

/* zones (pack.c): point zone {p} + points collinear with p off l; line zone {l} + lines meeting l off p */
static int zone_point(int p, int l, int *out) { int c = 0; out[c++] = p;
    for (int a = 0; a < Q1; a++) { int L = PL[p * Q1 + a]; if (L == l) continue; for (int b = 0; b < Q1; b++) { int w = LP[L * Q1 + b]; if (w != p) out[c++] = w; } }
    return c; }
static int zone_line(int p, int l, int *out) { int c = 0; out[c++] = l;
    for (int a = 0; a < Q1; a++) { int x = LP[l * Q1 + a]; if (x == p) continue; for (int b = 0; b < Q1; b++) { int K = PL[x * Q1 + b]; if (K != l) out[c++] = K; } }
    return c; }

static uint64_t rs = 0x9E3779B97F4A7C15ULL;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline double rndu(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int mode_auts(const char *outfn) {
    memoV = malloc(sizeof(int) * P); memoS = calloc(P, sizeof(unsigned));
    /* partition-preserving permutations fixing 3 */
    static int perms[5040][NCO]; int np = 0;
    int t[NCO];
    for (long long c = 0; c < 823543LL; c++) {
        long long x = c; int used[NCO] = {0}, ok = 1;
        for (int i = 0; i < NCO; i++) { t[i] = (int)(x % 7); x /= 7; if (used[t[i]]) { ok = 0; break; } used[t[i]] = 1; }
        if (!ok || t[3] != 3) continue;
        for (int i = 0; i < NCO && ok; i++) if (t[partner(i)] != partner(t[i])) ok = 0;
        if (ok) { memcpy(perms[np], t, sizeof(t)); np++; }
    }
    fprintf(stderr, "partition-preserving permutations: %d\n", np);
    FILE *out = fopen(outfn, "w"); int nauts = 0, ncand = 0;
    for (int pi_i = 0; pi_i < np; pi_i++) for (int t0 = 1; t0 < QQ; t0++) for (int t1 = 1; t1 < QQ; t1++) for (int t2 = 1; t2 < QQ; t2++) {
        Mono g; memcpy(g.pi, perms[pi_i], sizeof(g.pi));
        int dd[3] = {t0, t1, t2};
        for (int a = 0; a < 3; a++) { g.d[a] = dd[a]; g.d[a + 4] = inv11[dd[a]]; }
        g.d[3] = 1;
        ncand++;
        if (aut_test(&g, NULL)) {
            nauts++;
            for (int i = 0; i < NCO; i++) fprintf(out, "%d ", g.pi[i]);
            for (int i = 0; i < NCO; i++) fprintf(out, i < NCO - 1 ? "%d " : "%d\n", g.d[i]);
        }
    }
    fclose(out);
    printf("candidates %d, automorphisms (monomial, all lines checked) %d -> %s\n", ncand, nauts, outfn);
    /* group structure */
    Mono *A; int na = read_auts(outfn, &A);
    Mono *G; int ng = closure(A, na, &G, 200000);
    printf("group generated by all of them: order %d (list has %d)\n", ng, na);
    /* orders of elements, and point-fixing info */
    int cnt[64] = {0};
    for (int i = 0; i < na; i++) { int o = mono_order(&A[i]); if (o < 64) cnt[o]++; }
    for (int o = 1; o < 64; o++) if (cnt[o]) printf("  elements of order %d: %d\n", o, cnt[o]);
    return 0;
}

/* union-find on flags */
static int *uf;
static int uf_find(int x) { while (uf[x] != x) { uf[x] = uf[uf[x]]; x = uf[x]; } return x; }
static void uf_union(int a, int b) { a = uf_find(a); b = uf_find(b); if (a != b) uf[a < b ? b : a] = a < b ? a : b; }

static int mode_orb(int argc, char **argv) {
    if (argc < 7) { fprintf(stderr, "usage: c5_sym orb AUTFILE GENS SECS SEED OUTFLAGS [LAM0 LAM1 T0 T1]\n"); return 2; }
    const char *autfn = argv[2], *gspec = argv[3]; double secs = atof(argv[4]); rs ^= strtoull(argv[5], 0, 10) * 0x2545F4914F6CDD1DULL;
    const char *outfn = argv[6];
    double lam0 = argc > 7 ? atof(argv[7]) : 0.3, lam1 = argc > 8 ? atof(argv[8]) : 3.0;
    double T0 = argc > 9 ? atof(argv[9]) : 0.5, T1 = argc > 10 ? atof(argv[10]) : 0.05;
    memoV = malloc(sizeof(int) * P); memoS = calloc(P, sizeof(unsigned));
    Mono *A; int na = read_auts(autfn, &A);
    Mono *gens = malloc(sizeof(Mono) * na); int ng = 0;
    if (strcmp(gspec, "all") == 0) { memcpy(gens, A, sizeof(Mono) * na); ng = na; }
    else { char *s = strdup(gspec); for (char *tok = strtok(s, ","); tok; tok = strtok(NULL, ",")) { int k = atoi(tok); if (k < 0 || k >= na) { fprintf(stderr, "bad index %d\n", k); return 2; } gens[ng++] = A[k]; } free(s); }
    Mono *H; int nh = closure(gens, ng, &H, 200000);
    printf("subgroup order %d from %d generators\n", nh, ng);
    /* flags: f = 12*p + k, line PL[f] */
    int F = P * Q1;
    uf = malloc(sizeof(int) * F); for (int f = 0; f < F; f++) uf[f] = f;
    int *permP = malloc(sizeof(int) * P), *permL = malloc(sizeof(int) * P);
    for (int gi = 0; gi < ng; gi++) {
        if (!aut_test(&gens[gi], permL)) { fprintf(stderr, "generator %d is not an automorphism\n", gi); return 3; }
        for (int p = 0; p < P; p++) permP[p] = imgP(&gens[gi], p);
        for (int f = 0; f < F; f++) {
            int p = f / Q1, l = PL[f]; int p2 = permP[p], l2 = permL[l]; int j;
            for (j = 0; j < Q1; j++) if (PL[p2 * Q1 + j] == l2) break;
            if (j == Q1) { fprintf(stderr, "flag image not incident\n"); return 3; }
            uf_union(f, p2 * Q1 + j);
        }
    }
    /* orbits */
    int *oid = malloc(sizeof(int) * F); for (int f = 0; f < F; f++) oid[f] = -1;
    int *rootid = malloc(sizeof(int) * F); int no = 0;
    for (int f = 0; f < F; f++) { int r = uf_find(f); if (oid[r] < 0) oid[r] = no++; oid[f] = oid[r]; }
    int *osz = calloc(no, sizeof(int)); for (int f = 0; f < F; f++) osz[oid[f]]++;
    int *ost = malloc(sizeof(int) * (no + 1)); ost[0] = 0; for (int o = 0; o < no; o++) ost[o + 1] = ost[o] + osz[o];
    int *oflags = malloc(sizeof(int) * F); int *fillp = malloc(sizeof(int) * no); for (int o = 0; o < no; o++) fillp[o] = ost[o];
    for (int f = 0; f < F; f++) oflags[fillp[oid[f]]++] = f;
    (void)rootid;
    /* self-valid orbits: pairwise disjoint zones inside the orbit */
    uint8_t *tP = calloc(P, 1), *tL = calloc(P, 1);
    int *valid = malloc(sizeof(int) * no); int nv = 0;
    int zp[128], zl[128];
    int maxsz = 0; for (int o = 0; o < no; o++) if (osz[o] > maxsz) maxsz = osz[o];
    int *touchP = malloc(sizeof(int) * (size_t)(maxsz * 122 + 128)), *touchL = malloc(sizeof(int) * (size_t)(maxsz * 122 + 128));
    for (int o = 0; o < no; o++) {
        int ok = 1, nt = 0; int tpc = 0, tlc = 0;
        for (int i = ost[o]; i < ost[o + 1] && ok; i++) {
            int f = oflags[i], p = f / Q1, l = PL[f];
            int a = zone_point(p, l, zp), b = zone_line(p, l, zl);
            for (int k = 0; k < a; k++) { if (tP[zp[k]]) { ok = 0; break; } tP[zp[k]] = 1; touchP[tpc++] = zp[k]; }
            if (!ok) break;
            for (int k = 0; k < b; k++) { if (tL[zl[k]]) { ok = 0; break; } tL[zl[k]] = 1; touchL[tlc++] = zl[k]; }
        }
        for (int k = 0; k < tpc; k++) tP[touchP[k]] = 0;
        for (int k = 0; k < tlc; k++) tL[touchL[k]] = 0;
        (void)nt;
        if (ok) valid[nv++] = o;
    }
    /* orbit size histogram */
    {
        int hist[4096] = {0}; for (int i = 0; i < nv; i++) { int s = osz[valid[i]]; if (s < 4096) hist[s]++; }
        printf("orbits %d, self-valid orbits %d, max size %d\n", no, nv, maxsz);
        printf("valid orbit sizes:"); for (int s = 1; s < 4096; s++) if (hist[s]) printf(" %d:%d", s, hist[s]); printf("\n");
    }
    if (nv == 0) { printf("BEST 0\n"); return 0; }
    /* annealing over unions of valid orbits */
    uint16_t *occP = calloc(P, 2), *occL = calloc(P, 2);
    char *chosen = calloc(no, 1); int *cl = malloc(sizeof(int) * no); int *cpos = malloc(sizeof(int) * no); int ncl = 0;
    long over = 0, nflags = 0;
    int *bestL = malloc(sizeof(int) * no); int nbest = 0; long bestN = 0;
    /* helpers */
    #define ZONES(f, a, b) { int _p = (f) / Q1, _l = PL[f]; a = zone_point(_p, _l, zp); b = zone_line(_p, _l, zl); }
    struct timespec t0s, t1s; clock_gettime(CLOCK_MONOTONIC, &t0s);
    long it = 0; double el = 0;
    int moves_done = 0;
    for (;;) {
        it++;
        if ((it & 63) == 0) { clock_gettime(CLOCK_MONOTONIC, &t1s); el = (t1s.tv_sec - t0s.tv_sec) + 1e-9 * (t1s.tv_nsec - t0s.tv_nsec); if (el >= secs) break; }
        double fr = el / secs;
        double lam = lam0 * pow(lam1 / lam0, fr), T = T0 * pow(T1 / T0, fr);
        int o = valid[rnd() % nv];
        int s = osz[o];
        if (!chosen[o]) {
            long dO = 0;
            for (int i = ost[o]; i < ost[o + 1]; i++) { int f = oflags[i]; int a, b; ZONES(f, a, b);
                for (int k = 0; k < a; k++) dO += occP[zp[k]] > 0; for (int k = 0; k < b; k++) dO += occL[zl[k]] > 0; }
            double dE = -(double)s + lam * dO;
            if (dE <= 0 || rndu() < exp(-dE / T)) {
                for (int i = ost[o]; i < ost[o + 1]; i++) { int f = oflags[i]; int a, b; ZONES(f, a, b);
                    for (int k = 0; k < a; k++) { if (occP[zp[k]]++ > 0) over++; }
                    for (int k = 0; k < b; k++) { if (occL[zl[k]]++ > 0) over++; } }
                chosen[o] = 1; cpos[o] = ncl; cl[ncl++] = o; nflags += s; moves_done++;
            }
        } else {
            long dO = 0;
            for (int i = ost[o]; i < ost[o + 1]; i++) { int f = oflags[i]; int a, b; ZONES(f, a, b);
                for (int k = 0; k < a; k++) dO += occP[zp[k]] > 1; for (int k = 0; k < b; k++) dO += occL[zl[k]] > 1; }
            double dE = (double)s - lam * dO;
            if (dE <= 0 || rndu() < exp(-dE / T)) {
                for (int i = ost[o]; i < ost[o + 1]; i++) { int f = oflags[i]; int a, b; ZONES(f, a, b);
                    for (int k = 0; k < a; k++) { if (--occP[zp[k]] > 0) over--; }
                    for (int k = 0; k < b; k++) { if (--occL[zl[k]] > 0) over--; } }
                chosen[o] = 0; int pos = cpos[o]; cl[pos] = cl[--ncl]; cpos[cl[pos]] = pos; nflags -= s; moves_done++;
            }
        }
        if (over == 0 && nflags > bestN) {
            bestN = nflags; nbest = ncl; memcpy(bestL, cl, sizeof(int) * ncl);
        }
    }
    printf("annealing: %ld iterations, %d accepted moves, final flags %ld overlaps %ld, best valid %ld (%d orbits)\n",
           it, moves_done, nflags, over, bestN, nbest);
    /* write best valid flag set and re-check it from scratch */
    FILE *fo = fopen(outfn, "w"); long nf = 0;
    uint8_t *cP = calloc(P, 1), *cL = calloc(P, 1); long ov = 0, bad = 0;
    for (int i = 0; i < nbest; i++) { int o = bestL[i];
        for (int j = ost[o]; j < ost[o + 1]; j++) { int f = oflags[j], p = f / Q1, l = PL[f];
            fprintf(fo, "%d %d\n", p, l); nf++;
            int a = zone_point(p, l, zp), b = zone_line(p, l, zl);
            for (int k = 0; k < a; k++) { if (cP[zp[k]]++) ov++; }
            for (int k = 0; k < b; k++) { if (cL[zl[k]]++) ov++; } } }
    fclose(fo);
    printf("BEST %ld flags in %s (recheck overlaps %ld)\n", nf, outfn, ov);
    return ov == 0 ? 0 : 1;
}

int main(int argc, char **argv) {
    if (argc < 3) { fprintf(stderr, "usage: c5_sym auts AUTFILE | c5_sym orb AUTFILE GENS SECS SEED OUTFLAGS\n"); return 2; }
    load();
    if (strcmp(argv[1], "auts") == 0) return mode_auts(argv[2]);
    if (strcmp(argv[1], "orb") == 0) return mode_orb(argc, argv);
    fprintf(stderr, "unknown mode\n"); return 2;
}
