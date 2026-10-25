/* c2_ils.c: iterated local search with (1,2)-swaps (Andrade-Resende-Werneck style) for flag packings in GH(q).
   Zones and scoring as in pack.c: flag f = (p, l) with f = p*Q1 + a, l = PL[f]; point zone = p plus the q^2 points
   collinear with p off l; line zone = l plus the q^2 lines meeting l off p. A solution S is a set of flags with pairwise
   disjoint point zones and pairwise disjoint line zones. The conflict graph is implicit:
     cnt[f]  = number of zone elements of flag f that are owned by a solution flag (owners: ownP, ownL),
     a non-solution flag f is free iff cnt[f] == 0, and 1-tight w.r.t. s iff all its owned elements belong to s.
   encP(x) lists the 1464 flags whose point zone contains x, encL(e) the 1464 flags whose line zone contains e.
   Moves: (1,2)-swap (remove s, add two zone-disjoint flags that are 1-tight w.r.t. s), free insertion, and perturbation
   (force in a non-solution flag with few owners, remove those owners). Acceptance: worse solutions are kept with
   probability 1/(1 + d*d*), otherwise the iteration is undone from an undo log.
   Usage: c2_ils GHFILE SECONDS SEED OUTFLAGS [INFLAGS]     (output lines "p l")
   Check:  cd /home/user/degree-diameter/research/cell147/units && CHECKONLY=1 ./pack ../data/gh_11.txt 0 1 /dev/null OUTFLAGS
   Compile: gcc -O2 -march=native -o c2_ils c2_ils.c -lm */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <time.h>

static int P, q, Q1, ZN, NF;
static int32_t *LP, *PL, *FIDL;
static uint64_t rs = 0x9E3779B97F4A7C15ULL;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline int rndi(int n) { return (int)(rnd() % (uint64_t)n); }
static inline double rndu(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static uint8_t *cnt, *inS, *tmpc;
static int *ownP, *ownL, *markP, *markL, *stampF, *Spos, *Sl, *D, *U, *bestS;
static int nS = 0, bestN = 0, nU = 0;
static int stampCur = 0, markCur = 0;
static int *freeQ, nfq = 0, capfq = 0;
static int *dirtyQ, ndirty = 0, capdirty = 0;
static int *logF; static char *logT; static int nlog = 0, caplog = 0, logging = 0;
static int enc[2048];

static void pushFree(int f) { if (nfq == capfq) { capfq = capfq ? 2 * capfq : 1 << 16; freeQ = realloc(freeQ, sizeof(int) * capfq); } freeQ[nfq++] = f; }
static void pushDirty(int f) { if (ndirty == capdirty) { capdirty = capdirty ? 2 * capdirty : 1 << 12; dirtyQ = realloc(dirtyQ, sizeof(int) * capdirty); } dirtyQ[ndirty++] = f; }
static void pushLog(int f, char t) { if (nlog == caplog) { caplog = caplog ? 2 * caplog : 1 << 16; logF = realloc(logF, sizeof(int) * caplog); logT = realloc(logT, caplog); } logF[nlog] = f; logT[nlog] = t; nlog++; }

/* zones of flag f (each has ZN elements) */
static void zoneOf(int f, int *zp, int *zl) {
    int p = f / Q1, l = PL[f], c = 0;
    zp[c++] = p;
    for (int a = 0; a < Q1; a++) { int L = PL[p * Q1 + a]; if (L == l) continue;
        for (int b = 0; b < Q1; b++) { int w = LP[L * Q1 + b]; if (w != p) zp[c++] = w; } }
    c = 0; zl[c++] = l;
    for (int a = 0; a < Q1; a++) { int x = LP[l * Q1 + a]; if (x == p) continue;
        for (int b = 0; b < Q1; b++) { int K = PL[x * Q1 + b]; if (K != l) zl[c++] = K; } }
}

/* flags whose point zone contains point x (1464 of them) */
static int encP(int x, int *out) {
    int c = 0;
    for (int a = 0; a < Q1; a++) out[c++] = x * Q1 + a;
    for (int a = 0; a < Q1; a++) { int M = PL[x * Q1 + a];
        for (int b = 0; b < Q1; b++) { int pp = LP[M * Q1 + b]; if (pp == x) continue;
            for (int c2 = 0; c2 < Q1; c2++) { if (PL[pp * Q1 + c2] == M) continue; out[c++] = pp * Q1 + c2; } } }
    return c;
}

/* flags whose line zone contains line e (1464 of them) */
static int encL(int e, int *out) {
    int c = 0;
    for (int b = 0; b < Q1; b++) out[c++] = FIDL[e * Q1 + b];
    for (int i = 0; i < Q1; i++) { int x = LP[e * Q1 + i];
        for (int j = 0; j < Q1; j++) { int lp = PL[x * Q1 + j]; if (lp == e) continue;
            for (int k = 0; k < Q1; k++) { if (LP[lp * Q1 + k] == x) continue; out[c++] = FIDL[lp * Q1 + k]; } } }
    return c;
}

/* insert (add=1) or delete (add=0) flag f in the solution, maintaining owners and cnt */
static void setFlag(int f, int add) {
    int zp[256], zl[256]; zoneOf(f, zp, zl);
    if (add) {
        inS[f] = 1; for (int i = 0; i < ZN; i++) { ownP[zp[i]] = f; ownL[zl[i]] = f; }
        Spos[f] = nS; Sl[nS++] = f;
    } else {
        inS[f] = 0; for (int i = 0; i < ZN; i++) { ownP[zp[i]] = -1; ownL[zl[i]] = -1; }
        int k = Spos[f], g = Sl[--nS]; Sl[k] = g; Spos[g] = k;
    }
    for (int i = 0; i < ZN; i++) { int n = encP(zp[i], enc);
        if (add) { for (int j = 0; j < n; j++) cnt[enc[j]]++; }
        else { for (int j = 0; j < n; j++) { int g = enc[j]; if (--cnt[g] == 0 && !inS[g]) pushFree(g); } } }
    for (int i = 0; i < ZN; i++) { int n = encL(zl[i], enc);
        if (add) { for (int j = 0; j < n; j++) cnt[enc[j]]++; }
        else { for (int j = 0; j < n; j++) { int g = enc[j]; if (--cnt[g] == 0 && !inS[g]) pushFree(g); } } }
}
static void addF(int f) { setFlag(f, 1); if (logging) pushLog(f, 1); }
static void remF(int f) { setFlag(f, 0); if (logging) pushLog(f, 0); }

/* distinct solution flags whose zones meet the zone of f; out must hold 2*ZN entries */
static int distinctOwners(int f, int *out) {
    int zp[256], zl[256]; zoneOf(f, zp, zl);
    stampCur++; int c = 0;
    for (int i = 0; i < ZN; i++) { int g = ownP[zp[i]]; if (g >= 0 && stampF[g] != stampCur) { stampF[g] = stampCur; out[c++] = g; } }
    for (int i = 0; i < ZN; i++) { int g = ownL[zl[i]]; if (g >= 0 && stampF[g] != stampCur) { stampF[g] = stampCur; out[c++] = g; } }
    return c;
}

/* U = non-solution flags whose only conflicting solution flag is s (exact: tmpc[g] == cnt[g]) */
static int findTight(int s) {
    int zp[256], zl[256]; zoneOf(s, zp, zl);
    int nd = 0;
    for (int i = 0; i < ZN; i++) { int n = encP(zp[i], enc);
        for (int j = 0; j < n; j++) { int g = enc[j]; if (tmpc[g]++ == 0) D[nd++] = g; } }
    for (int i = 0; i < ZN; i++) { int n = encL(zl[i], enc);
        for (int j = 0; j < n; j++) { int g = enc[j]; if (tmpc[g]++ == 0) D[nd++] = g; } }
    nU = 0;
    for (int i = 0; i < nd; i++) { int g = D[i]; if (!inS[g] && tmpc[g] == cnt[g]) U[nU++] = g; tmpc[g] = 0; }
    return nU;
}

/* (1,2)-swap at solution flag s: remove s, add two zone-disjoint flags that are 1-tight w.r.t. s */
static int trySwap(int s) {
    int n = findTight(s);
    if (n < 2) return 0;
    int tries = n < 40 ? n : 40;
    for (int t = 0; t < tries; t++) {
        int i = rndi(n), u = U[i];
        int zpu[256], zlu[256]; zoneOf(u, zpu, zlu);
        markCur++;
        for (int k = 0; k < ZN; k++) { markP[zpu[k]] = markCur; markL[zlu[k]] = markCur; }
        for (int j = 0; j < n; j++) { if (j == i) continue; int v = U[j];
            int zpv[256], zlv[256]; zoneOf(v, zpv, zlv);
            int ok = 1;
            for (int k = 0; k < ZN && ok; k++) if (markP[zpv[k]] == markCur || markL[zlv[k]] == markCur) ok = 0;
            if (ok) { remF(s); addF(u); addF(v); pushDirty(u); pushDirty(v); return 1; } }
    }
    return 0;
}

static void localSearch(void) {
    for (;;) {
        while (nfq > 0) { int f = freeQ[--nfq]; if (!inS[f] && cnt[f] == 0) { addF(f); pushDirty(f); } }
        if (ndirty == 0) break;
        int s = dirtyQ[--ndirty];
        if (inS[s]) trySwap(s);
    }
}

/* force a non-solution flag in: sample 64, take the one with fewest conflicting solution flags */
static void perturb(void) {
    int out[256], bf = -1, bc = 1 << 30;
    for (int k = 0; k < 64; k++) { int f = rndi(NF); if (inS[f]) continue; int c = distinctOwners(f, out);
        if (c < bc || (c == bc && rndi(2))) { bc = c; bf = f; } }
    if (bf < 0) return;
    int c = distinctOwners(bf, out);
    for (int i = 0; i < c; i++) remF(out[i]);
    addF(bf); pushDirty(bf);
}

static double now(void) { struct timespec ts; clock_gettime(CLOCK_MONOTONIC, &ts); return ts.tv_sec + ts.tv_nsec * 1e-9; }

int main(int argc, char **argv) {
    if (argc < 5) { fprintf(stderr, "usage: c2_ils GHFILE SECONDS SEED OUTFLAGS [INFLAGS]\n"); return 2; }
    FILE *f = fopen(argv[1], "r"); if (!f || fscanf(f, "%d %d", &P, &q) != 2) return 2;
    Q1 = q + 1; ZN = q * q + 1; NF = P * Q1;
    LP = malloc(sizeof(int32_t) * (size_t)NF); PL = malloc(sizeof(int32_t) * (size_t)NF); FIDL = malloc(sizeof(int32_t) * (size_t)NF);
    for (int i = 0; i < NF; i++) if (fscanf(f, "%d", &LP[i]) != 1) return 2;
    fclose(f);
    { int *c = calloc(P, sizeof(int)); for (int l = 0; l < P; l++) for (int k = 0; k < Q1; k++) { int p = LP[l * Q1 + k]; PL[p * Q1 + c[p]++] = l; } free(c); }
    for (int l = 0; l < P; l++) for (int b = 0; b < Q1; b++) { int p = LP[l * Q1 + b], got = -1;
        for (int a = 0; a < Q1; a++) if (PL[p * Q1 + a] == l) { got = p * Q1 + a; break; } FIDL[l * Q1 + b] = got; }
    double secs = atof(argv[2]); rs ^= strtoull(argv[3], 0, 10) * 0x2545F4914F6CDD1DULL; if (!rs) rs = 1;
    cnt = calloc(NF, 1); inS = calloc(NF, 1); tmpc = calloc(NF, 1);
    ownP = malloc(sizeof(int) * P); ownL = malloc(sizeof(int) * P);
    for (int i = 0; i < P; i++) ownP[i] = ownL[i] = -1;
    markP = calloc(P, sizeof(int)); markL = calloc(P, sizeof(int));
    stampF = calloc(NF, sizeof(int)); Spos = malloc(sizeof(int) * NF);
    Sl = malloc(sizeof(int) * (P + 1)); bestS = malloc(sizeof(int) * (P + 1));
    D = malloc(sizeof(int) * NF); U = malloc(sizeof(int) * NF);

    if (argc > 5) { FILE *g = fopen(argv[5], "r"); int a, b;
        while (g && fscanf(g, "%d %d", &a, &b) == 2) { int got = -1;
            if (a >= 0 && a < P) for (int k = 0; k < Q1; k++) if (PL[a * Q1 + k] == b) { got = a * Q1 + k; break; }
            if (got >= 0 && !inS[got] && cnt[got] == 0) setFlag(got, 1); }
        if (g) fclose(g);
        fprintf(stderr, "start from INFLAGS: %d flags\n", nS); }
    int *perm = malloc(sizeof(int) * NF); for (int i = 0; i < NF; i++) perm[i] = i;
    for (int i = NF - 1; i > 0; i--) { int r = rndi(i + 1), t = perm[i]; perm[i] = perm[r]; perm[r] = t; }
    for (int i = 0; i < NF; i++) { int g = perm[i]; if (!inS[g] && cnt[g] == 0) setFlag(g, 1); }
    free(perm);
    nfq = 0; localSearch();
    bestN = nS; memcpy(bestS, Sl, sizeof(int) * nS);
    fprintf(stderr, "greedy maximal: %d flags\n", nS);

    double t0 = now(), lastrep = 0; long it = 0, nacc = 0;
    for (;;) {
        double el = now() - t0; if (el >= secs) break;
        it++;
        int nOld = nS;
        logging = 1; nlog = 0;
        perturb();
        localSearch();
        logging = 0;
        int nNew = nS;
        if (nNew > bestN) { bestN = nNew; memcpy(bestS, Sl, sizeof(int) * nS); fprintf(stderr, "best %d at it %ld t=%.1f\n", bestN, it, el); }
        int acc = 1;
        if (nNew < nOld) { int d = nOld - nNew, ds = bestN - nNew; if (ds < 1) ds = 1;
            acc = rndu() < 1.0 / (1.0 + (double)d * ds); }
        if (acc) nacc++;
        else for (int i = nlog - 1; i >= 0; i--) setFlag(logF[i], logT[i] ? 0 : 1);
        nlog = 0; nfq = 0; ndirty = 0;
        if (it % 100 == 0) {   /* periodic full (1,2)-swap sweep over the solution */
            for (int i = 0; i < nS; i++) pushDirty(Sl[i]);
            localSearch();
            if (nS > bestN) { bestN = nS; memcpy(bestS, Sl, sizeof(int) * nS); fprintf(stderr, "best %d (sweep) at it %ld\n", bestN, it); }
        }
        if (now() - lastrep > 10) { lastrep = now(); fprintf(stderr, "it %ld t %.0f cur %d best %d accepted %ld\n", it, el, nS, bestN, nacc); }
    }
    FILE *o = fopen(argv[4], "w"); if (!o) return 2;
    for (int i = 0; i < bestN; i++) { int ff = bestS[i]; fprintf(o, "%d %d\n", ff / Q1, PL[ff]); }
    fclose(o);
    fprintf(stderr, "final best %d (iterations %ld, accepted %ld)\n", bestN, it, nacc);
    printf("%d\n", bestN);
    return 0;
}
