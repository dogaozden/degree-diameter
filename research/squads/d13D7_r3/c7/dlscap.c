/* dlscov.c (squad round 3, card c7): the round-2 DLS-MC clique search (dls_coset.c) with a coverage objective.
   Every distinct maximal clique K of the coset graph with |K| >= KMIN (K contains 0) is scored by
     F(K) = 11|K| + 122 - cov(K),   cov(K) = #{d in E : n_d . K = F_11}
   where E = the 122 projective n = (n_s,n_b,n_c,n_f) with 8 n_s^2 + 4 n_b n_f - n_c^2 = 0 (mod 11).  F is the size of
   the set R = (lines of K, e4 dropped) + (one point at infinity per direction d with n_d.K != F_11), see c7/README-free
   notes in c7/common.py.  Best cliques by F are written to OUTPREFIX_bestF.txt (offsets "0 b c s f", record() format).
   usage: dlscov SEED PD CPU_SEC KMIN OUTPREFIX
   (the original DLS-MC description follows)
*/
/* dls_coset.c: DLS-MC (Pullan & Hoos 2006, dynamic local search for maximum clique) on the coset graph
   G = Cay(F_11^4, {v : D(v) is a non-square mod 11}),  D(s,b,c,f) = s^2 + 3c^2 + 8bf  (mod 11).
   G is vertex-transitive, so WLOG the clique contains 0 = (0,0,0,0); the search runs on the induced subgraph on
   N(0) (6710 vertices), and a clique of size k there is a clique of size k+1 in G.

   Clique state: m[i] = number of clique members not adjacent to i (for i outside the clique), +128 for clique members.
   So N_I(C) = {i : m[i] == 0} (addable) and N_L(C) = {i : m[i] == 1} (one swap).  Adding/removing a vertex x updates
   m by one row of the non-adjacency matrix NA (byte matrix), which is vectorised.

   usage: dls_coset SEED PD CPU_SEC TARGET OUT_OFFSETS [START_OFFSETS]
     SEED          rng seed
     PD            penalty delay: PD=1 means no penalties and a random-vertex perturbation; PD>1 means penalties
                   and a restart from the last added vertex
     CPU_SEC       stop after this much CPU time (clock())
     TARGET        stop when a clique of this size (counting 0) is reached
     OUT_OFFSETS   rewritten on every improvement: '#' header, then lines "0 b c s f" (a = 0), one per clique vertex,
                   including the line "0 0 0 0 0"
     START_OFFSETS optional file of offsets "a b c e f"; each gives (s,b,c,f) with s = (2a+e) mod 11 and is used as the
                   start clique (its non-adjacent members are skipped)
*/
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>
#include <limits.h>

#define NV 14641

static int U;                       /* |N(0)| */
static int xs[NV], idx_of[NV], isS[NV];
static int dig[NV][4];
static uint8_t *NA;                 /* NA[i*U+j] = 1 iff i != j and i,j not adjacent */
static uint8_t *m;                  /* miss count (+128 if in clique) */
static int *pen, *cl, *remst, *c0mark, *Ilist, *Llist;
static int csz = 0, lastAdded = -1, pstamp = 0, c0stamp = 0, bestU = 0;
static long long steps = 0;
static int ndist_best = 0; static long long ndist_new = 0;
static uint64_t rs = 1;
static const char *outpath = NULL;
static uint64_t *zob = NULL;                 /* zobrist keys per universe vertex */
static uint64_t *hset = NULL; static size_t hcap = 0, hcount = 0;
static int hset_insert(uint64_t h) {          /* returns 1 if new */
    if (h == 0) h = 1;
    if (hcount * 2 >= hcap) {                 /* grow */
        size_t ncap = hcap ? hcap * 2 : (1u << 16);
        uint64_t *nt = calloc(ncap, sizeof(uint64_t));
        for (size_t i = 0; i < hcap; i++) if (hset[i]) {
            size_t j = (size_t)(hset[i] & (ncap - 1));
            while (nt[j]) j = (j + 1) & (ncap - 1);
            nt[j] = hset[i];
        }
        free(hset); hset = nt; hcap = ncap;
    }
    size_t j = (size_t)(h & (hcap - 1));
    while (hset[j]) { if (hset[j] == h) return 0; j = (j + 1) & (hcap - 1); }
    hset[j] = h; hcount++;
    return 1;
}
static const int isNS[11] = {0, 0, 1, 0, 0, 0, 1, 1, 1, 0, 1};   /* non-squares 2,6,7,8,10 */

static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static double cpu(void) { return (double)clock() / CLOCKS_PER_SEC; }

/* ---- coverage objective (card c7) ---- */
#define NDIR 122
static int ndir = 0, KMIN = 27, CAP = 1000;
static int dirN[NDIR][4];
static void init_dirs(void) {
    for (int n = 1; n < 14641; n++) {
        int v[4] = {n % 11, (n / 11) % 11, (n / 121) % 11, n / 1331};
        int i = 0; while (i < 4 && v[i] == 0) i++;
        if (i == 4 || v[i] != 1) continue;                 /* projective representative: first nonzero = 1 */
        if ((8 * v[0] * v[0] + 4 * v[1] * v[3] - v[2] * v[2]) % 11 != 0) continue;
        if (ndir >= NDIR) { fprintf(stderr, "too many directions\n"); exit(2); }
        for (int k = 0; k < 4; k++) dirN[ndir][k] = v[k];
        ndir++;
    }
    if (ndir != NDIR) { fprintf(stderr, "found %d directions, expected 122\n", ndir); exit(2); }
}
/* xsNV: NV-indices x = s + 11 b + 121 c + 1331 f of the clique members (vertex 0 included) */
static int covOf(const int *xsNV, int k) {
    int cov = 0;
    for (int d = 0; d < ndir; d++) {
        int mask = 0;
        for (int t = 0; t < k; t++) {
            int x = xsNV[t];
            int r = (dirN[d][0] * (x % 11) + dirN[d][1] * ((x / 11) % 11) + dirN[d][2] * ((x / 121) % 11)
                     + dirN[d][3] * (x / 1331)) % 11;
            mask |= 1 << r;
        }
        cov += (mask == 2047);
    }
    return cov;
}
#define TOPN 64
static int topF[TOPN], topK[TOPN], topCov[TOPN], topSet[TOPN][32];
static int ntop = 0;
static int histk[34][NDIR + 1];
static int bestFall = -1;
static void topInsert(int F, int k, int cov, const int *xsNV) {
    /* keep the TOPN best cliques by F (distinct by construction: called once per distinct clique) */
    int pos;
    if (ntop < TOPN) pos = ntop++;
    else {
        pos = 0; for (int i = 1; i < TOPN; i++) if (topF[i] < topF[pos]) pos = i;
        if (topF[pos] >= F) return;
    }
    topF[pos] = F; topK[pos] = k; topCov[pos] = cov;
    for (int t = 0; t < k && t < 32; t++) topSet[pos][t] = xsNV[t];
}
/* ---- sub-clique optimisation (card c7): best F over subsets S of a maximal clique with |S| >= SMIN ---- */
static int SMIN = 26;
static uint32_t MM[NDIR][11];
static int bestSub = -1000000;
static int bestSubSet[32], bestSubK = 0;
static int subFhist[400];
static uint64_t mix64(uint64_t z) { z += 0x9E3779B97F4A7C15ULL; z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ULL;
    z = (z ^ (z >> 27)) * 0x94D049BB133111EBULL; return z ^ (z >> 31); }
#define STOP 256
static uint64_t *subhs = NULL; static size_t subcap = 0, subcount = 0;
static int subhs_insert(uint64_t h) {
    if (!h) h = 1;
    if (subcount * 2 >= subcap) {
        size_t ncap = subcap ? subcap * 2 : (1u << 16);
        uint64_t *nt = calloc(ncap, sizeof(uint64_t));
        for (size_t i = 0; i < subcap; i++) if (subhs[i]) { size_t j = (size_t)(subhs[i] & (ncap - 1));
            while (nt[j]) j = (j + 1) & (ncap - 1); nt[j] = subhs[i]; }
        free(subhs); subhs = nt; subcap = ncap;
    }
    size_t j = (size_t)(h & (subcap - 1));
    while (subhs[j]) { if (subhs[j] == h) return 0; j = (j + 1) & (subcap - 1); }
    subhs[j] = h; subcount++;
    return 1;
}
static int covMask(uint32_t S) {
    int cov = 0;
    for (int d = 0; d < ndir; d++) {
        int ok = 1;
        for (int z = 0; z < 11; z++) if (!(S & MM[d][z])) { ok = 0; break; }
        cov += ok;
    }
    return cov;
}
/* members: NV-indices (vertex 0 included), k <= 32 */
static void subopt_clique(const int *mem, int k) {
    for (int d = 0; d < ndir; d++) {
        for (int z = 0; z < 11; z++) MM[d][z] = 0;
        for (int i = 0; i < k; i++) {
            int x = mem[i];
            int r = (dirN[d][0] * (x % 11) + dirN[d][1] * ((x / 11) % 11) + dirN[d][2] * ((x / 121) % 11)
                     + dirN[d][3] * (x / 1331)) % 11;
            MM[d][r] |= (1u << i);
        }
    }
    uint32_t full = (k >= 32) ? 0xffffffffu : ((1u << k) - 1);
    int localBest = -1000000;
    for (int r = 0; r <= k - SMIN; r++) {
        uint32_t J = (r == 0) ? 0 : ((1u << r) - 1);
        for (;;) {
            uint32_t S = full & ~J;
            int size = k - r;
            int cov = covMask(S);
            int F = 11 * size + 122 - cov;
            if (F > localBest) localBest = F;
            if (F >= bestSub && F >= 390) {
                if (F > bestSub) { bestSub = F; }
                /* dedupe by the (sorted) member set */
                uint64_t h = 0;
                for (int i = 0; i < k; i++) if (S & (1u << i)) h ^= mix64((uint64_t)mem[i] + 7);
                if (subhs_insert(h) && F >= bestSub) {
                    /* keep it (also used for the top list) */
                    if (F == bestSub) { bestSubK = 0; for (int i = 0; i < k; i++) if (S & (1u << i)) bestSubSet[bestSubK++] = mem[i]; }
                    if (F > 0) { int b = F; (void)b; }
                    if (F == bestSub) {
                        char path[1024]; snprintf(path, sizeof path, "%s_bestsub.txt", outpath);
                        FILE *g = fopen(path, "w");
                        if (g) { fprintf(g, "# sub-clique F %d size %d cov %d (|I| = %d)\n", F, size, cov, 122 - cov);
                            for (int t = 0; t < bestSubK; t++) { int x = bestSubSet[t];
                                fprintf(g, "0 %d %d %d %d\n", (x / 11) % 11, (x / 121) % 11, x % 11, x / 1331); }
                            fclose(g); }
                        printf("new best sub-clique F %d (size %d, cov %d) cpu %.1f\n", F, size, cov, cpu());
                        fflush(stdout);
                    }
                    if (F >= 0 && F < 400) subFhist[F]++;
                }
            }
            if (r == 0) break;
            uint32_t c = J & -J, rr = J + c;
            if (rr == 0) break;
            J = (((rr ^ J) >> 2) / c) | rr;
            if (J > full) break;
        }
    }
    if (localBest >= 0 && localBest < 400) subFhist[localBest < 0 ? 0 : localBest] += 0;
}
static void write_top(const char *prefix) {
    char path[1024]; snprintf(path, sizeof path, "%s_top.txt", prefix);
    FILE *f = fopen(path, "w"); if (!f) return;
    for (int i = 0; i < ntop; i++) {
        fprintf(f, "# rank %d F %d k %d cov %d\n", i, topF[i], topK[i], topCov[i]);
        for (int t = 0; t < topK[i]; t++) { int x = topSet[i][t];
            fprintf(f, "0 %d %d %d %d\n", (x / 11) % 11, (x / 121) % 11, x % 11, x / 1331); }
    }
    fclose(f);
}


static inline void add_v(int v) {
    const uint8_t *row = NA + (size_t)v * U;
    for (int w = 0; w < U; w++) m[w] += row[w];
    m[v] += 128;
    cl[csz++] = v;
}

static inline void rem_idx(int t) {
    int v = cl[t];
    cl[t] = cl[--csz];
    const uint8_t *row = NA + (size_t)v * U;
    for (int w = 0; w < U; w++) m[w] -= row[w];
    m[v] -= 128;
}

/* difference code of two coordinate codes x, y (digitwise mod 11) */
static int csub(int x, int y) {
    int r = 0, p = 1;
    for (int k = 0; k < 4; k++) { r += (((x % 11) - (y % 11) + 11) % 11) * p; p *= 11; x /= 11; y /= 11; }
    return r;
}

static void record(void) {
    bestU = csz;
    int k = csz + 1;
    int *set = malloc(sizeof(int) * k);
    set[0] = 0;
    for (int t = 0; t < csz; t++) set[t + 1] = xs[cl[t]];
    int bad = 0;
    for (int i = 0; i < k; i++)
        for (int j = i + 1; j < k; j++)
            if (!isS[csub(set[i], set[j])]) bad++;
    FILE *f = fopen(outpath, "w");
    fprintf(f, "# DLS-MC coset clique, size %d (incl. 0 = (0,0,0,0)); formula check bad=%d\n", k, bad);
    for (int t = 0; t < k; t++) {
        int x = set[t];
        fprintf(f, "0 %d %d %d %d\n", (x / 11) % 11, (x / 121) % 11, x % 11, x / 1331);
    }
    fclose(f);
    printf("best %d (total %d) steps %lld cpu %.1f formula-bad %d\n", csz, k, steps, cpu(), bad);
    fflush(stdout);
    free(set);
}

/* expansion: add members of N_I(C), minimum penalty first, random ties */
static void expand(void) {
    for (;;) {
        if (csz + 1 >= CAP) return;
        int ni = 0;
        for (int w = 0; w < U; w++) { Ilist[ni] = w; ni += (m[w] == 0); }
        if (ni == 0) return;
        int best = INT_MAX, pick = -1, cnt = 0;
        for (int t = 0; t < ni; t++) {
            int v = Ilist[t], p = pen[v];
            if (p < best) { best = p; pick = v; cnt = 1; }
            else if (p == best && (rnd() % (uint64_t)(++cnt)) == 0) pick = v;
        }
        add_v(pick);
        lastAdded = pick;
        steps++;
        if (csz > bestU) record();
    }
}

/* plateau: swap moves (N_L vertex in, its unique non-neighbour out) while N_I is empty, until C and C0 are disjoint.
   A vertex removed during this plateau phase may not re-enter during it (tabu). */
static void plateau(void) {
    pstamp++;
    int c0 = ++c0stamp;
    for (int t = 0; t < csz; t++) c0mark[cl[t]] = c0;
    int c0cnt = csz;
    while (c0cnt > 0) {
        int ni = 0, nl = 0;
        for (int w = 0; w < U; w++) {
            uint8_t mm = m[w];
            Ilist[ni] = w; ni += (mm == 0);
            Llist[nl] = w; nl += (mm == 1);
        }
        if (ni > 0) break;
        int best = INT_MAX, pick = -1, cnt = 0;
        for (int t = 0; t < nl; t++) {
            int v = Llist[t];
            if (remst[v] == pstamp) continue;
            int p = pen[v];
            if (p < best) { best = p; pick = v; cnt = 1; }
            else if (p == best && (rnd() % (uint64_t)(++cnt)) == 0) pick = v;
        }
        if (pick < 0) break;
        const uint8_t *row = NA + (size_t)pick * U;
        int idx = -1;
        for (int t = 0; t < csz; t++) if (row[cl[t]]) { idx = t; break; }
        if (idx < 0) { fprintf(stderr, "internal error: no non-neighbour\n"); exit(2); }
        int u = cl[idx];
        rem_idx(idx);
        remst[u] = pstamp;
        if (c0mark[u] == c0) c0cnt--;
        add_v(pick);
        lastAdded = pick;
        steps++;
    }
}

int main(int argc, char **argv) {
    if (argc < 6) { fprintf(stderr, "usage: dlscov SEED PD CPU_SEC KMIN OUTPREFIX [START_OFFSETS]\n"); return 1; }
    uint64_t seed = strtoull(argv[1], NULL, 10);
    int pd = atoi(argv[2]);
    double cpulim = atof(argv[3]);
    KMIN = atoi(argv[4]);
    if (getenv("SMIN")) SMIN = atoi(getenv("SMIN"));
    if (getenv("CAP")) CAP = atoi(getenv("CAP"));
    if (SMIN < KMIN) { }
    int target = 1000;
    char outbuf[1024]; snprintf(outbuf, sizeof outbuf, "%s_last.txt", argv[5]); outpath = strdup(outbuf);
    const char *startpath = argc > 6 ? argv[6] : NULL;
    if (pd < 1) pd = 1;
    rs = seed * 0x9E3779B97F4A7C15ULL + 0x2545F4914F6CDD1DULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 20; i++) rnd();
    init_dirs();

    /* universe: N(0) = {x != 0 : D(x) non-square} */
    for (int x = 1; x < NV; x++) {
        int s = x % 11, b = (x / 11) % 11, c = (x / 121) % 11, f = x / 1331;
        isS[x] = isNS[(s * s + 3 * c * c + 8 * b * f) % 11];
    }
    isS[0] = 0;
    U = 0;
    for (int x = 0; x < NV; x++) idx_of[x] = -1;
    for (int x = 1; x < NV; x++) if (isS[x]) { idx_of[x] = U; xs[U++] = x; }
    for (int i = 0; i < U; i++) {
        int x = xs[i];
        dig[i][0] = x % 11; dig[i][1] = (x / 11) % 11; dig[i][2] = (x / 121) % 11; dig[i][3] = x / 1331;
    }
    NA = calloc((size_t)U * U, 1);
    for (int i = 0; i < U; i++)
        for (int j = i + 1; j < U; j++) {
            int r = 0, p = 1;
            for (int k = 0; k < 4; k++) { r += ((dig[i][k] - dig[j][k] + 11) % 11) * p; p *= 11; }
            if (!isS[r]) { NA[(size_t)i * U + j] = 1; NA[(size_t)j * U + i] = 1; }
        }
    int deg0 = 0;
    for (int j = 0; j < U; j++) if (j != 0 && !NA[j]) deg0++;
    printf("universe N(0): %d vertices, degree of vertex 0 inside: %d (expect 3069)\n", U, deg0);

    zob = calloc(U, sizeof(uint64_t));
    for (int i = 0; i < U; i++) zob[i] = rnd() | 1;
    m = calloc(U, 1);
    pen = calloc(U, sizeof(int));
    cl = calloc(U, sizeof(int));
    remst = calloc(U, sizeof(int));
    c0mark = calloc(U, sizeof(int));
    Ilist = calloc(U, sizeof(int));
    Llist = calloc(U, sizeof(int));

    if (startpath) {
        FILE *g = fopen(startpath, "r");
        if (!g) { fprintf(stderr, "cannot open %s\n", startpath); return 1; }
        char line[256];
        while (fgets(line, sizeof line, g)) {
            if (line[0] == '#') continue;
            int a, b, c, e, f;
            if (sscanf(line, "%d %d %d %d %d", &a, &b, &c, &e, &f) != 5) continue;
            int s = (((2 * a + e) % 11) + 11) % 11;
            b = ((b % 11) + 11) % 11; c = ((c % 11) + 11) % 11; f = ((f % 11) + 11) % 11;
            int x = s + 11 * b + 121 * c + 1331 * f;
            if (x == 0) continue;
            int i = idx_of[x];
            if (i < 0 || (m[i] & 128) || m[i] != 0) { fprintf(stderr, "seed vertex skipped\n"); continue; }
            add_v(i);
            lastAdded = i;
        }
        fclose(g);
        bestU = csz;
        printf("start clique from %s: %d vertices (+0)\n", startpath, csz + 1);
        if (csz > 0) record();
    } else {
        int i = (int)(rnd() % (uint64_t)U);
        add_v(i);
        lastAdded = i;
    }

    clock_t t0 = clock();
    long long iters = 0, npu = 0;
    for (;;) {
        if (cpu() - (double)t0 / CLOCKS_PER_SEC >= cpulim) break;
        if (bestU + 1 >= target) break;
        expand();
        for (;;) {                       /* plateau, then expand again while N_I is non-empty */
            if (csz + 1 >= CAP) break;
            plateau();
            int ni = 0;
            for (int w = 0; w < U; w++) ni += (m[w] == 0);
            if (ni == 0) break;
            expand();
        }
        iters++;
        if (csz + 1 >= KMIN) {
            uint64_t h = 0;
            for (int t = 0; t < csz; t++) h ^= zob[cl[t]];
            if (hset_insert(h)) {
                if (csz + 1 > ndist_best) ndist_best = csz + 1; ndist_new++;
                int k = csz + 1, xsNV[32];
                if (k <= 32) {
                    xsNV[0] = 0;
                    for (int t = 0; t < csz; t++) xsNV[t + 1] = xs[cl[t]];
                    int cov = covOf(xsNV, k);
                    int F = 11 * k + 122 - cov;
                    histk[k][cov]++;
                    if (F > bestFall) {
                        bestFall = F;
                        char path[1024]; snprintf(path, sizeof path, "%s_bestF.txt", outpath);
                        FILE *g = fopen(path, "w");
                        if (g) { fprintf(g, "# F %d k %d cov %d (|I| = %d)\n", F, k, cov, 122 - cov);
                            for (int t = 0; t < k; t++) { int x = xsNV[t];
                                fprintf(g, "0 %d %d %d %d\n", (x / 11) % 11, (x / 121) % 11, x % 11, x / 1331); }
                            fclose(g); }
                        printf("new best F %d (k %d, cov %d) after %lld cliques, cpu %.1f\n", F, k, cov, ndist_new, cpu());
                        fflush(stdout);
                    }
                    topInsert(F, k, cov, xsNV);
                    if (k >= SMIN) subopt_clique(xsNV, k);
                }
            }
        }
        for (int t = 0; t < csz; t++) pen[cl[t]]++;
        npu++;
        if (npu % (long long)pd == 0)
            for (int w = 0; w < U; w++) if (pen[w] > 0) pen[w]--;
        if (pd > 1) {
            /* restart from the last added vertex */
            for (int t = 0; t < csz;) { if (cl[t] != lastAdded) rem_idx(t); else t++; }
        } else {
            /* add a random non-member and drop its non-neighbours */
            int v;
            do { v = (int)(rnd() % (uint64_t)U); } while (m[v] & 128);
            const uint8_t *row = NA + (size_t)v * U;
            for (int t = 0; t < csz;) { if (row[cl[t]]) rem_idx(t); else t++; }
            add_v(v);
            lastAdded = v;
            steps++;
        }
        if (iters % 200000 == 0) {
            printf("iters %lld steps %lld cpu %.1f cur %d best %d\n", iters, steps, cpu(), csz + 1, bestU + 1);
            fflush(stdout);
        }
    }
    printf("distinct maximal cliques of total size >= %d: %lld (max size seen %d)\n", KMIN, ndist_new, ndist_best);
    write_top(argv[5]);
    {
        char path[1024]; snprintf(path, sizeof path, "%s_hist.txt", argv[5]);
        FILE *h = fopen(path, "w");
        if (h) { for (int kk = 0; kk < 34; kk++) for (int c = 0; c <= NDIR; c++) if (histk[kk][c])
            fprintf(h, "k %d cov %d count %d\n", kk, c, histk[kk][c]); fclose(h); }
        printf("bestF overall %d; top list written to %s_top.txt\n", bestFall, argv[5]);
    }
    printf("FINISHED seed %llu pd %d: best total %d, iters %lld, steps %lld, cpu %.1f s\n",
           (unsigned long long)seed, pd, bestU + 1, iters, steps, cpu());
    fflush(stdout);
    return 0;
}
