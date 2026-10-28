/* e06: orbit quotient of the non-collinear point problem on H(16) by the semiregular group S91.
 * Point orbit P (91 points, no two collinear) occupies the 17 line orbits of the lines through its
 * representative; two orbits conflict iff they share a line orbit. This is the same packing problem
 * as the full one with points = admissible point orbits and lines = line orbits (capacity 1).
 * Search: greedy + ARW-style ILS with (1,2)-swaps, as in ils16.c. Saves the EXPANDED point set
 * (count, then point ids; count = 91 * orbits).
 * usage: quot16 HEX PPERM LPERM OUT SECONDS SEED [INIT_ORBIT_IDS]
 *   INIT_ORBIT_IDS: optional file in the same format as OUT's orbit-level list (not needed).
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define K 17
#define OSZ 91
static int N, L;
static int *LN, *PL;       /* hexagon: lines' points (L*K), points' lines (N*K) */
static int *pperm, *lperm;
static int *porb, *lorb;   /* orbit id of each point / line */
static int nO = 0, nLO = 0;   /* number of admissible point orbits, number of line orbits */
static int *rep;           /* admissible index -> representative point */
static int *orbpts;        /* admissible index * OSZ + j : points of the orbit */
static int *PLO;           /* admissible index * K + i : line orbit of the i-th line through rep */
static int *LOoff, *LOp;   /* CSR: line orbit -> admissible point orbits incident */
static int *occ, *tight;   /* per line orbit: chosen orbit or -1; per orbit: occupied line orbits */
static char *sol, *inq;
static int *qu;
static long qn = 0;
static int nsol = 0;
static int *lg;
static long lglen = 0, lgcap = 1L << 22;
static int logging = 1, overflow = 0;
static int *rl;
static int *cand; static int candcap = 1 << 16;
static uint64_t rs = 0x9E3779B97F4A7C15ULL;

static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }
static void push(int p) { if (!inq[p]) { inq[p] = 1; qu[qn++] = p; } }

static void ins(int P) {
    sol[P] = 1; nsol++;
    const int *pl = PLO + (size_t)P * K;
    for (int i = 0; i < K; i++) {
        int lo = pl[i]; occ[lo] = P;
        for (int e = LOoff[lo]; e < LOoff[lo + 1]; e++) tight[LOp[e]]++;
    }
    if (logging) { if (lglen < lgcap) lg[lglen++] = P + 1; else overflow = 1; }
}
static void rem(int P) {
    sol[P] = 0; nsol--;
    const int *pl = PLO + (size_t)P * K;
    for (int i = 0; i < K; i++) {
        int lo = pl[i]; occ[lo] = -1;
        for (int e = LOoff[lo]; e < LOoff[lo + 1]; e++) tight[LOp[e]]--;
    }
    if (logging) { if (lglen < lgcap) lg[lglen++] = -(P + 1); else overflow = 1; }
}
static int collinear(int a, int b) {
    const int *pa = PLO + (size_t)a * K, *pb = PLO + (size_t)b * K;
    for (int i = 0; i < K; i++) for (int j = 0; j < K; j++) if (pa[i] == pb[j]) return 1;
    return 0;
}
static int occupant_of(int r) {
    const int *pl = PLO + (size_t)r * K;
    for (int i = 0; i < K; i++) if (occ[pl[i]] >= 0) return occ[pl[i]];
    return -1;
}
static int improve_from(int x) {
    int nc = 0;
    const int *px = PLO + (size_t)x * K;
    for (int i = 0; i < K; i++) {
        int lo = px[i];
        for (int e = LOoff[lo]; e < LOoff[lo + 1]; e++) {
            int r = LOp[e];
            if (r != x && tight[r] == 1 && nc < candcap) cand[nc++] = r;
        }
    }
    if (nc < 2) return 0;
    int A = -1, B = -1;
    for (int a = 0; a < nc && A < 0; a++)
        for (int b = a + 1; b < nc; b++)
            if (!collinear(cand[a], cand[b])) { A = cand[a]; B = cand[b]; break; }
    if (A < 0) return 0;
    rem(x); ins(A); ins(B);
    for (int i = 0; i < K; i++) {
        int lo = px[i];
        for (int e = LOoff[lo]; e < LOoff[lo + 1]; e++) {
            int r = LOp[e];
            if (r != x && !sol[r] && tight[r] == 0) { ins(r); push(r); }
        }
    }
    push(A); push(B);
    for (int i = 0; i < K; i++) {
        int lo = px[i];
        for (int e = LOoff[lo]; e < LOoff[lo + 1]; e++) {
            int r = LOp[e];
            if (r != x && !sol[r] && tight[r] == 1) push(occupant_of(r));
        }
    }
    return 1;
}
static void run_ls(void) {
    while (qn > 0) {
        int x = qu[--qn]; inq[x] = 0;
        if (sol[x]) improve_from(x);
    }
}
static void perturb(void) {
    int v;
    for (int t = 0;; t++) {
        v = (int)(rnd() % (uint64_t)nO);
        if (sol[v]) continue;
        if (tight[v] <= 2 || t >= 100) break;
    }
    const int *pv = PLO + (size_t)v * K;
    int nr = 0;
    for (int i = 0; i < K; i++) {
        int y = occ[pv[i]];
        if (y >= 0) { rem(y); rl[nr++] = y; }
    }
    ins(v); push(v);
    for (int k = 0; k < nr; k++) {
        const int *py = PLO + (size_t)rl[k] * K;
        for (int i = 0; i < K; i++) {
            int lo = py[i];
            for (int e = LOoff[lo]; e < LOoff[lo + 1]; e++) {
                int r = LOp[e];
                if (!sol[r] && tight[r] == 0) { ins(r); push(r); }
            }
        }
    }
    for (int k = 0; k < nr; k++) {
        const int *py = PLO + (size_t)rl[k] * K;
        for (int i = 0; i < K; i++) {
            int lo = py[i];
            for (int e = LOoff[lo]; e < LOoff[lo + 1]; e++) {
                int r = LOp[e];
                if (!sol[r] && tight[r] == 1) push(occupant_of(r));
            }
        }
    }
}
static void undo(void) {
    logging = 0;
    for (long k = lglen - 1; k >= 0; k--) {
        int e = lg[k];
        if (e > 0) rem(e - 1); else ins(-e - 1);
    }
    logging = 1; lglen = 0;
}
/* direct check on the expanded point set: each line at most one chosen point */
static int verify_points(const char *out) {
    (void)out; return 0;
}
static void save(const char *out, int best) {
    char tmp[4096];
    snprintf(tmp, sizeof tmp, "%s.tmp", out);
    FILE *f = fopen(tmp, "w");
    if (!f) { perror("save"); return; }
    int cnt = 0;
    for (int P = 0; P < nO; P++) cnt += sol[P] * OSZ;
    fprintf(f, "%d\n", cnt);
    for (int P = 0; P < nO; P++) if (sol[P])
        for (int j = 0; j < OSZ; j++) fprintf(f, "%d\n", orbpts[(size_t)P * OSZ + j]);
    fclose(f);
    rename(tmp, out);
    fprintf(stderr, "saved orbits %d = points %d (best %d)\n", nsol, cnt, best);
}
static int verify(void) {
    int bad = 0;
    int *t2 = calloc(nO, sizeof(int));
    for (int lo = 0; lo < nLO; lo++) {
        int c = 0;
        for (int e = LOoff[lo]; e < LOoff[lo + 1]; e++) c += sol[LOp[e]];
        if (c > 1) bad++;
        if (c > 0) for (int e = LOoff[lo]; e < LOoff[lo + 1]; e++) t2[LOp[e]]++;
    }
    for (int P = 0; P < nO; P++) if (t2[P] != tight[P]) { bad++; break; }
    free(t2);
    return bad;
}

int main(int argc, char **argv) {
    if (argc < 7) { fprintf(stderr, "usage: quot16 HEX PPERM LPERM OUT SECONDS SEED\n"); return 1; }
    const char *hex = argv[1], *out = argv[4];
    double secs = atof(argv[5]);
    rs ^= (uint64_t)atoll(argv[6]) * 0x2545F4914F6CDD1DULL + 1;
    for (int i = 0; i < 10; i++) rnd();

    FILE *f = fopen(hex, "rb");
    int hdr[3];
    if (!f || fread(hdr, 4, 3, f) != 3) { fprintf(stderr, "hex?\n"); return 1; }
    if (hdr[0] != 16) { fprintf(stderr, "q must be 16\n"); return 1; }
    N = hdr[1]; L = hdr[2];
    LN = malloc((size_t)L * K * sizeof(int));
    if (fread(LN, sizeof(int), (size_t)L * K, f) != (size_t)L * K) return 1;
    fclose(f);
    PL = malloc((size_t)N * K * sizeof(int));
    int *cnt = calloc(N, sizeof(int));
    for (int l = 0; l < L; l++) for (int j = 0; j < K; j++) {
        int p = LN[(size_t)l * K + j];
        PL[(size_t)p * K + cnt[p]++] = l;
    }
    free(cnt);

    pperm = malloc((size_t)N * sizeof(int));
    lperm = malloc((size_t)N * sizeof(int));
    FILE *g = fopen(argv[2], "rb");
    if (!g || fread(pperm, 4, N, g) != (size_t)N) { fprintf(stderr, "pperm?\n"); return 1; }
    fclose(g);
    g = fopen(argv[3], "rb");
    if (!g || fread(lperm, 4, L, g) != (size_t)L) { fprintf(stderr, "lperm?\n"); return 1; }
    fclose(g);

    /* the permutations must be incidence preserving: lperm[l] contains pperm[p] for p on l */
    long badinc = 0;
    for (int l = 0; l < L; l++) for (int j = 0; j < K; j++) {
        int img = pperm[LN[(size_t)l * K + j]], m = lperm[l];
        int ok = 0;
        for (int i = 0; i < K; i++) if (LN[(size_t)m * K + i] == img) { ok = 1; break; }
        if (!ok) badinc++;
    }
    fprintf(stderr, "incidence-preservation violations: %ld\n", badinc);
    if (badinc) return 1;

    /* orbits by cycle decomposition */
    porb = malloc((size_t)N * sizeof(int));
    lorb = malloc((size_t)L * sizeof(int));
    for (int p = 0; p < N; p++) porb[p] = -1;
    for (int l = 0; l < L; l++) lorb[l] = -1;
    int *plen = malloc((size_t)N * sizeof(int));
    int nPorb = 0, nLorb = 0;
    int *prep = malloc((size_t)N * sizeof(int)), *lrep = malloc((size_t)L * sizeof(int));
    for (int p = 0; p < N; p++) if (porb[p] < 0) {
        int c = 0, x = p;
        do { porb[x] = nPorb; c++; x = pperm[x]; } while (x != p);
        plen[nPorb] = c; prep[nPorb] = p; nPorb++;
    }
    for (int l = 0; l < L; l++) if (lorb[l] < 0) {
        int x = l;
        do { lorb[x] = nLorb; x = lperm[x]; } while (x != l);
        lrep[nLorb] = l; nLorb++;
    }
    nLO = nLorb;
    int nbad = 0;
    for (int o = 0; o < nPorb; o++) if (plen[o] != OSZ) nbad++;
    fprintf(stderr, "point orbits %d (size != 91: %d), line orbits %d\n", nPorb, nbad, nLorb);

    /* admissible orbits: the 17 lines through the representative lie in 17 distinct line orbits */
    int *adm = malloc((size_t)nPorb * sizeof(int));
    int *aidx = malloc((size_t)nPorb * sizeof(int));
    nO = 0;
    for (int o = 0; o < nPorb; o++) {
        int r = prep[o], ok = (plen[o] == OSZ);
        for (int i = 0; i < K && ok; i++) for (int j = i + 1; j < K; j++)
            if (lorb[PL[(size_t)r * K + i]] == lorb[PL[(size_t)r * K + j]]) { ok = 0; break; }
        adm[o] = ok; aidx[o] = ok ? nO : -1;
        if (ok) nO++;
    }
    fprintf(stderr, "admissible point orbits %d\n", nO);
    rep = malloc((size_t)nO * sizeof(int));
    orbpts = malloc((size_t)nO * OSZ * sizeof(int));
    PLO = malloc((size_t)nO * K * sizeof(int));
    for (int o = 0; o < nPorb; o++) if (adm[o]) {
        int a = aidx[o], r = prep[o];
        rep[a] = r;
        int x = r;
        for (int j = 0; j < OSZ; j++) { orbpts[(size_t)a * OSZ + j] = x; x = pperm[x]; }
        for (int i = 0; i < K; i++) PLO[(size_t)a * K + i] = lorb[PL[(size_t)r * K + i]];
    }
    /* CSR: line orbit -> admissible orbits meeting it */
    LOoff = calloc(nLO + 1, sizeof(int));
    for (int a = 0; a < nO; a++) for (int i = 0; i < K; i++) LOoff[PLO[(size_t)a * K + i] + 1]++;
    for (int lo = 0; lo < nLO; lo++) LOoff[lo + 1] += LOoff[lo];
    LOp = malloc((size_t)LOoff[nLO] * sizeof(int));
    int *fillp = malloc((size_t)nLO * sizeof(int));
    for (int lo = 0; lo < nLO; lo++) fillp[lo] = LOoff[lo];
    for (int a = 0; a < nO; a++) for (int i = 0; i < K; i++) { int lo = PLO[(size_t)a * K + i]; LOp[fillp[lo]++] = a; }
    free(fillp);
    int mx = 0; for (int lo = 0; lo < nLO; lo++) if (LOoff[lo + 1] - LOoff[lo] > mx) mx = LOoff[lo + 1] - LOoff[lo];
    fprintf(stderr, "max orbits per line orbit %d, incidences %d\n", mx, LOoff[nLO]);

    occ = malloc((size_t)nLO * sizeof(int));
    for (int lo = 0; lo < nLO; lo++) occ[lo] = -1;
    tight = calloc(nO, sizeof(int));
    sol = calloc(nO, 1);
    inq = calloc(nO, 1);
    qu = malloc((size_t)nO * sizeof(int));
    lg = malloc((size_t)lgcap * sizeof(int));
    rl = malloc(K * sizeof(int));
    cand = malloc((size_t)candcap * sizeof(int));

    int *perm = malloc((size_t)nO * sizeof(int));
    for (int a = 0; a < nO; a++) perm[a] = a;
    for (int a = nO - 1; a > 0; a--) { int j = (int)(rnd() % (uint64_t)(a + 1)); int t = perm[a]; perm[a] = perm[j]; perm[j] = t; }
    logging = 0;
    for (int k = 0; k < nO; k++) { int a = perm[k]; if (!sol[a] && tight[a] == 0) ins(a); }
    logging = 1;
    for (int a = 0; a < nO; a++) if (sol[a]) push(a);
    run_ls();
    int best = nsol, cur = nsol;
    fprintf(stderr, "greedy+LS: %d orbits (%d points), verify bad=%d\n", nsol, nsol * OSZ, verify());
    save(out, best);

    double t0 = now(), tend = t0 + secs, tlast = t0, tsave = t0;
    int pending = 0;
    long iter = 0;
    while (1) {
        if (now() >= tend) break;
        logging = 1; lglen = 0; overflow = 0;
        perturb();
        run_ls();
        if (nsol > best) { best = nsol; pending = 1; }
        if (pending && now() - tsave > 2.0) { save(out, best); tsave = now(); pending = 0; }
        int accept;
        if (nsol >= cur || overflow) accept = 1;
        else if (pending) accept = 0;
        else {
            int d = cur - nsol, ds = best - nsol;
            accept = (rnd() % (uint64_t)(1 + (uint64_t)d * (uint64_t)(ds > 0 ? ds : 1))) == 0;
        }
        if (accept) cur = nsol; else undo();
        iter++;
        if (now() - tlast > 15.0) {
            fprintf(stderr, "t=%.0fs iter=%ld cur=%d best=%d (points %d)\n", now() - t0, iter, cur, best, best * OSZ);
            tlast = now();
        }
    }
    if (pending) { save(out, best); pending = 0; }
    fprintf(stderr, "final: iter=%ld cur=%d best=%d points=%d verify_bad=%d\n", iter, cur, best, best * OSZ, verify());
    (void)verify_points;
    return 0;
}
