/* symrepair.c, card c2 of squad d16D8-r3: symrepair (copied from d16D8/symrepair.c, kept as symrepair_orig.c) plus
   C-equivariant matching moves next to the repair moves.

   Targeted repair search for C-INVARIANT Z_k-lifts. Edge class = orbit id: all edges of an orbit keep one voltage, so
   the semiregular group C acts on the lift. SRCFILE lists one point and one line per C-orbit (symbase.py); the uncovered
   count U over those sources is the objective. For a C-invariant design of order r the count over all base vertices is
   r * U, so a design with U = 0 is VALID once `baselift eval FILE D` (all sources) confirms it.

   Moves, one type drawn per step with probabilities PMIX = p_repair,p_align,p_swap,p_random:
     0 repair : the original move. An uncovered (s,y,g) gives a walk s -> y of length <= D; one edge orbit on it gets a
                voltage change delta (as in symrepair).
     1 align  : one matching orbit {(g^t p0, g^t l0)} becomes {(g^t p0, g^(t+a) l0)}, a in 1..r-1, i.e. the line ends of
                the orbit are mapped by ln^a. Voltage unchanged.
     2 swap   : two point orbits p1, p2 of the same matching exchange their line orbits: the edges of p1 become
                (g^t p1, g^(t+b1) l2) and those of p2 become (g^t p2, g^(t+b2) l1), where l1, l2 are the current lines of
                p1, p2 and b1, b2 are random in Z_r. Each orbit keeps its voltage.
     3 random : a random edge orbit gets a random new voltage.
   Align and swap change only line endpoints inside one matching, so orbit membership, voltages and orbit lists stay the
   same; the adjacency is rebuilt after every candidate. Each candidate is scored by U (exact over the orbit sources, the
   same as symrepair). The best of K candidates of the drawn type is accepted by the Metropolis rule exp(-(U' - U)/T),
   with T geometric from T0 to T1 over SECS.

   symbase.py numbers the classes flags first (F = norb - 2M of them), then matching 0 (M classes), then matching 1 (M
   classes), M = N/r. GROUP is a text file "N r", then pt[0..N-1] and ln[0..N-1]: the generator's permutations of points
   and lines (the same data as hex/sym_qQ_rR.json). At start the program checks that each matching class is an orbit
   {(g^t p0, g^t l0)} and that each matching is a bijection of the points onto the lines; it exits otherwise.

   Usage:  symrepair BASE D SECS SEED OUT     (SECS = 0: only the uncovered count over SRCFILE)
   env: SRCFILE (required), GROUP (required when p_align or p_swap > 0), PMIX (default 0.6,0.15,0.15,0.1; "1,0,0,0" is
        plain repair), K (candidates per step, default 1), T0 (default 1.0), T1 (default 0.1), NODES (DFS budget per
        repair move, default 100000). The NSRC/EPOCH active-set branch of symrepair was dead code (act_all = 1) and is
        not kept. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <time.h>
typedef uint64_t u64;

typedef struct { int s, y, g; } Trip;
typedef struct { int type, a, b, c, d; } Cand;   /* type 0: a = edge, b = new voltage of its orbit;
                                                    type 1: a = class, b = shift a;
                                                    type 2: a = class1, b = shift1, c = class2, d = shift2;
                                                    type 3: a = class, b = new voltage */

static int V, k, E, P, Dm, NP;                  /* NP = number of points, V = 2 NP */
static int *ex, *ey, *ec, *ecls, *px, *py;      /* edges; px/py: adjacency slot of the edge at its two ends */
static int norb, *ooff, *olist;
static int *off, *nb, *sh, *eid, *sg;           /* CSR adjacency: nb = neighbour, sh = sheet shift x->nb, sg = +1 at ex, -1 at ey */
static u64 HI[64], LO[64];
static uint64_t rs = 88172645463325252ULL;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline int rndi(int n) { return (int)(rnd() % (uint64_t)n); }
static inline double unif(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) { struct timespec ts; clock_gettime(CLOCK_MONOTONIC, &ts); return ts.tv_sec + 1e-9 * ts.tv_nsec; }

static int GR = 0, GM = 0, GF = 0, *gpt = NULL, *gln = NULL;  /* group order r, matchings per type M, first matching class */

static void setup_masks(void) {
    P = 64 / k;
    for (int c = 0; c < k; c++) {
        HI[c] = LO[c] = 0;
        for (int i = 0; i < P * k; i++) { if (i % k >= c) HI[c] |= 1ULL << i; else LO[c] |= 1ULL << i; }
    }
}
static inline u64 rot(u64 x, int c) {
    if (!c) return x;
    return ((x << c) & HI[c]) | ((x >> (k - c)) & LO[c]);
}

/* adjacency from the current endpoints and voltages (buffers allocated once; degrees never change under our moves) */
static void build_adj(void) {
    static int *fill = NULL;
    if (!off) {
        off = malloc(sizeof(int) * (V + 1)); fill = malloc(sizeof(int) * V);
        nb = malloc(sizeof(int) * 2 * E); sh = malloc(sizeof(int) * 2 * E);
        eid = malloc(sizeof(int) * 2 * E); sg = malloc(sizeof(int) * 2 * E);
    }
    memset(off, 0, sizeof(int) * (V + 1));
    for (int e = 0; e < E; e++) { off[ex[e] + 1]++; off[ey[e] + 1]++; }
    for (int x = 0; x < V; x++) off[x + 1] += off[x];
    memset(fill, 0, sizeof(int) * V);
    for (int e = 0; e < E; e++) {
        int x = ex[e], y = ey[e], c = ec[e];
        int j = off[x] + fill[x]++;
        nb[j] = y; sh[j] = c; eid[j] = e; sg[j] = 1; px[e] = j;
        j = off[y] + fill[y]++;
        nb[j] = x; sh[j] = (k - c) % k; eid[j] = e; sg[j] = -1; py[e] = j;
    }
}
static void read_base(const char *fn) {
    FILE *f = fopen(fn, "r"); if (!f) { fprintf(stderr, "cannot open %s\n", fn); exit(1); }
    if (fscanf(f, "%d %d %d", &V, &k, &E) != 3) { fprintf(stderr, "bad header\n"); exit(1); }
    if (k < 1 || k > 64 || (V & 1)) { fprintf(stderr, "need 1 <= k <= 64 and V = 2 NP\n"); exit(1); }
    ex = malloc(sizeof(int) * E); ey = malloc(sizeof(int) * E); ec = malloc(sizeof(int) * E); ecls = malloc(sizeof(int) * E);
    px = malloc(sizeof(int) * E); py = malloc(sizeof(int) * E);
    for (int e = 0; e < E; e++) {
        if (fscanf(f, "%d %d %d %d", &ex[e], &ey[e], &ec[e], &ecls[e]) != 4) { fprintf(stderr, "short base file at edge %d\n", e); exit(1); }
        if (ex[e] < 0 || ex[e] >= V || ey[e] < 0 || ey[e] >= V || ec[e] < 0 || ec[e] >= k) { fprintf(stderr, "bad edge %d\n", e); exit(1); }
    }
    fclose(f);
    NP = V / 2;
    for (int e = 0; e < E; e++) if (ex[e] >= NP || ey[e] < NP) { fprintf(stderr, "edge %d is not point-line\n", e); exit(1); }
    setup_masks(); build_adj();
}
static void write_base(const char *fn) {
    char tmpn[1024]; snprintf(tmpn, sizeof tmpn, "%s.tmp", fn);
    FILE *f = fopen(tmpn, "w"); fprintf(f, "%d %d %d\n", V, k, E);
    for (int e = 0; e < E; e++) fprintf(f, "%d %d %d %d\n", ex[e], ey[e], ec[e], ecls[e]);
    fclose(f); rename(tmpn, fn);
}
static void build_orbits(void) {
    norb = 0; for (int e = 0; e < E; e++) if (ecls[e] + 1 > norb) norb = ecls[e] + 1;
    ooff = calloc(norb + 1, sizeof(int)); olist = malloc(sizeof(int) * E);
    for (int e = 0; e < E; e++) ooff[ecls[e] + 1]++;
    for (int o = 0; o < norb; o++) ooff[o + 1] += ooff[o];
    int *fill = calloc(norb, sizeof(int));
    for (int e = 0; e < E; e++) olist[ooff[ecls[e]] + fill[ecls[e]]++] = e;
    for (int e = 0; e < E; e++) if (ec[e] != ec[olist[ooff[ecls[e]]]]) { fprintf(stderr, "orbit %d not constant\n", ecls[e]); exit(1); }
    free(fill);
}
/* the edge of orbit o whose point end is x (orbit o has one edge per point of its point orbit) */
static int class_edge_at(int o, int x) {
    for (int i = ooff[o]; i < ooff[o + 1]; i++) if (ex[olist[i]] == x) return olist[i];
    fprintf(stderr, "internal: class %d has no edge at point %d\n", o, x); exit(2);
}
static void read_group(const char *fn) {
    FILE *f = fopen(fn, "r"); if (!f) { fprintf(stderr, "cannot open GROUP %s\n", fn); exit(1); }
    int gn = 0;
    if (fscanf(f, "%d %d", &gn, &GR) != 2 || gn != NP) { fprintf(stderr, "GROUP: header must be 'N r' with N = %d\n", NP); exit(1); }
    gpt = malloc(sizeof(int) * NP); gln = malloc(sizeof(int) * NP);
    for (int i = 0; i < NP; i++) if (fscanf(f, "%d", &gpt[i]) != 1) { fprintf(stderr, "GROUP: short file\n"); exit(1); }
    for (int i = 0; i < NP; i++) if (fscanf(f, "%d", &gln[i]) != 1) { fprintf(stderr, "GROUP: short file\n"); exit(1); }
    fclose(f);
    if (GR < 2 || NP % GR) { fprintf(stderr, "GROUP: r must be >= 2 and divide N\n"); exit(1); }
    for (int w = 0; w < 2; w++) {                       /* both are permutations of order dividing r */
        int *perm = w ? gln : gpt;
        char *seen = calloc(NP, 1);
        for (int i = 0; i < NP; i++) {
            if (perm[i] < 0 || perm[i] >= NP || seen[perm[i]]) { fprintf(stderr, "GROUP: not a permutation\n"); exit(1); }
            seen[perm[i]] = 1;
        }
        free(seen);
        for (int i = 0; i < NP; i++) { int x = i; for (int t = 0; t < GR; t++) x = perm[x]; if (x != i) { fprintf(stderr, "GROUP: order does not divide r\n"); exit(1); } }
    }
    GM = NP / GR; GF = norb - 2 * GM;
    if (GF < 0) { fprintf(stderr, "GROUP: fewer classes than two matchings\n"); exit(1); }
    for (int o = GF; o < norb; o++) {                   /* each matching class is {(g^t p0, g^t l0)} */
        if (ooff[o + 1] - ooff[o] != GR) { fprintf(stderr, "GROUP: matching class %d has %d edges\n", o, ooff[o + 1] - ooff[o]); exit(1); }
        int e0 = olist[ooff[o]], x = ex[e0], l = ey[e0] - NP;
        for (int t = 0; t < GR; t++) {
            int e = class_edge_at(o, x);
            if (ey[e] - NP != l) { fprintf(stderr, "GROUP: matching class %d is not a C-orbit\n", o); exit(1); }
            x = gpt[x]; l = gln[l];
        }
    }
    for (int kk = 0; kk < 2; kk++) {                    /* each matching is a bijection points -> lines */
        int *cp = calloc(NP, sizeof(int)), *cl = calloc(NP, sizeof(int));
        for (int o = GF + kk * GM; o < GF + (kk + 1) * GM; o++)
            for (int i = ooff[o]; i < ooff[o + 1]; i++) { cp[ex[olist[i]]]++; cl[ey[olist[i]] - NP]++; }
        for (int i = 0; i < NP; i++) if (cp[i] != 1 || cl[i] != 1) { fprintf(stderr, "GROUP: matching %d is not a bijection\n", kk); exit(1); }
        free(cp); free(cl);
    }
    fprintf(stderr, "GROUP ok: r=%d, point orbits %d, flag classes %d, matching classes %d+%d\n", GR, GM, GF, GM, GM);
}

/* ---- undo log for one candidate ---- */
#define ULOG 8192
static int ul_e[ULOG], ul_ey[ULOG], ul_ec[ULOG], nul = 0;
static void ulog(int e) {
    if (nul >= ULOG) { fprintf(stderr, "undo log full\n"); exit(2); }
    ul_e[nul] = e; ul_ey[nul] = ey[e]; ul_ec[nul] = ec[e]; nul++;
}
static void undo_all(void) {
    for (int i = nul - 1; i >= 0; i--) { ey[ul_e[i]] = ul_ey[i]; ec[ul_e[i]] = ul_ec[i]; }
    nul = 0; build_adj();
}
static inline int lpow(int l, int s) { while (s-- > 0) l = gln[l]; return l; }

/* ---- lift BFS: uncovered count over a batch of sources, optionally recording the uncovered triples ---- */
static u64 *Ra, *Fa, *Xa;
static Trip *LA, *LB, *LW;
static long nA, nB, nW, LCAP;

static long bfs_batch(const int *src, int ns, Trip *L, long *cnt) {
    u64 *R = Ra, *F = Fa, *X = Xa;
    memset(R, 0, sizeof(u64) * V); memset(F, 0, sizeof(u64) * V);
    for (int i = 0; i < ns; i++) { R[src[i]] |= 1ULL << (i * k); F[src[i]] |= 1ULL << (i * k); }
    for (int d = 1; d <= Dm; d++) {
        for (int x = 0; x < V; x++) {
            u64 acc = 0;
            for (int j = off[x]; j < off[x + 1]; j++) { u64 f = F[nb[j]]; if (f) acc |= rot(f, (k - sh[j]) % k); }
            X[x] = acc & ~R[x];
        }
        for (int x = 0; x < V; x++) R[x] |= X[x];
        u64 *tp = F; F = X; X = tp;
    }
    u64 full = (ns * k >= 64) ? ~0ULL : ((1ULL << (ns * k)) - 1);
    long miss = 0;
    for (int x = 0; x < V; x++) {
        u64 mm = full & ~R[x];
        if (!mm) continue;
        miss += __builtin_popcountll(mm);
        if (L) while (mm) {
            int b = __builtin_ctzll(mm); mm &= mm - 1;
            if (*cnt < LCAP) { L[*cnt].s = src[b / k]; L[*cnt].y = x; L[*cnt].g = b % k; (*cnt)++; }
        }
    }
    return miss;
}
static long eval_set(const int *S, int n, Trip *L, long *cnt) {
    long tot = 0; *cnt = 0;
    for (int b = 0; b < n; b += P) {
        int ns = n - b < P ? n - b : P;
        tot += bfs_batch(S + b, ns, L, cnt);
    }
    return tot;
}

/* ---- walk search: non-backtracking walks of length <= Dm from s to tgt ---- */
#define MAXDEP 12
#define MAXFOUND 256
static int tgt, *distT, *qbuf;
static int wE[MAXDEP], wS[MAXDEP];
static int FE[MAXFOUND][MAXDEP], FS[MAXFOUND][MAXDEP], FL[MAXFOUND], FSIG[MAXFOUND], nfound;
static long nodes_left, NODES;

static void dfs(int x, int depth, int lastE) {
    if (--nodes_left < 0 || nfound >= MAXFOUND) return;
    if (depth > 0 && x == tgt) {
        long s = 0;
        for (int i = 0; i < depth; i++) s += (long)wS[i] * ec[wE[i]];
        int n = nfound++;
        FL[n] = depth; FSIG[n] = (int)(((s % k) + k) % k);
        for (int i = 0; i < depth; i++) { FE[n][i] = wE[i]; FS[n][i] = wS[i]; }
    }
    if (depth == Dm) return;
    int lo = off[x], deg = off[x + 1] - lo;
    int ord[128];
    for (int t = 0; t < deg; t++) ord[t] = lo + t;
    for (int t = deg - 1; t > 0; t--) { int r = rndi(t + 1), tmp = ord[t]; ord[t] = ord[r]; ord[r] = tmp; }
    for (int t = 0; t < deg; t++) {
        int j = ord[t], e = eid[j], y = nb[j];
        if (e == lastE || depth + 1 + distT[y] > Dm) continue;
        int rep = 0;
        for (int i = 0; i < depth; i++) if (wE[i] == e) { rep = 1; break; }
        if (rep) continue;
        wE[depth] = e; wS[depth] = sg[j];
        dfs(y, depth + 1, e);
        if (nodes_left < 0 || nfound >= MAXFOUND) return;
    }
}
static void dist_to(int t) {
    for (int x = 0; x < V; x++) distT[x] = 1 << 20;
    int h = 0, tl = 0; distT[t] = 0; qbuf[tl++] = t;
    while (h < tl) {
        int x = qbuf[h++];
        for (int j = off[x]; j < off[x + 1]; j++) { int y = nb[j]; if (distT[y] > distT[x] + 1) { distT[y] = distT[x] + 1; qbuf[tl++] = y; } }
    }
}
/* repair move for uncovered (s, y, g): returns 1 and the edge and its new voltage (of the whole orbit of the edge) */
static int make_move(int s, int y, int g, int *oe, int *onv) {
    tgt = y; dist_to(y);
    if (distT[s] > Dm) return 0;
    nodes_left = NODES; nfound = 0;
    dfs(s, 0, -1);
    if (!nfound) return 0;
    int w = rndi(nfound), p = rndi(FL[w]);
    int e = FE[w][p];
    int delta = ((g - FSIG[w]) % k + k) % k;          /* the walk reaches sheet FSIG[w]; needs +delta */
    int nO = 0; for (int i = 0; i < FL[w]; i++) if (ecls[FE[w][i]] == ecls[e]) nO += FS[w][i];
    nO = ((nO % k) + k) % k; if (!nO) return 0;
    int dv = -1; for (int t = 0; t < k; t++) if ((nO * t) % k == delta) { dv = t; break; }
    if (dv < 0) return 0;
    int nv = (ec[e] + dv) % k;
    if (nv == ec[e]) return 0;
    *oe = e; *onv = nv;
    return 1;
}

/* ---- candidate moves ---- */
static void apply_cand(const Cand *C) {
    nul = 0;
    if (C->type == 0 || C->type == 3) {
        int o = (C->type == 0) ? ecls[C->a] : C->a;
        for (int i = ooff[o]; i < ooff[o + 1]; i++) { int e = olist[i]; ulog(e); ec[e] = C->b; }
    } else if (C->type == 1) {
        for (int i = ooff[C->a]; i < ooff[C->a + 1]; i++) { int e = olist[i]; ulog(e); ey[e] = NP + lpow(ey[e] - NP, C->b); }
    } else {                                            /* type 2: swap the line orbits of two point orbits */
        int o1 = C->a, o2 = C->c;
        int x1 = ex[olist[ooff[o1]]], x2 = ex[olist[ooff[o2]]];
        for (int t = 0; t < GR; t++) {
            int e1 = class_edge_at(o1, x1), e2 = class_edge_at(o2, x2);
            int l1 = ey[e1] - NP, l2 = ey[e2] - NP;
            ulog(e1); ulog(e2);
            ey[e1] = NP + lpow(l2, C->b);
            ey[e2] = NP + lpow(l1, C->d);
            x1 = gpt[x1]; x2 = gpt[x2];
        }
    }
    build_adj();
}
static int gen_cand(Cand *C, int type, const Trip *L, long nL) {
    C->type = type;
    if (type == 0) {
        if (nL <= 0) return 0;
        Trip tr = L[rndi((int)nL)];
        int e, nv;
        if (!make_move(tr.s, tr.y, tr.g, &e, &nv)) return 0;
        C->a = e; C->b = nv; return 1;
    }
    if (type == 3) {
        int o = rndi(norb), cur = ec[olist[ooff[o]]], nv = rndi(k);
        if (nv == cur) return 0;
        C->a = o; C->b = nv; return 1;
    }
    if (type == 1) {
        C->a = GF + rndi(2 * GM); C->b = 1 + rndi(GR - 1); return 1;
    }
    {                                                   /* type 2: two distinct point orbits of one matching */
        int base = GF + rndi(2) * GM;
        int o1 = base + rndi(GM), o2 = base + rndi(GM - 1);
        if (o2 >= o1) o2++;
        C->a = o1; C->b = rndi(GR); C->c = o2; C->d = rndi(GR); return 1;
    }
}
static int pick_type(const double *cum, const double *pm) {
    double u = unif();
    int last = 0;
    for (int t = 0; t < 4; t++) if (pm[t] > 0) last = t;
    for (int t = 0; t < 4; t++) if (pm[t] > 0 && u < cum[t]) return t;
    return last;
}

int main(int argc, char **argv) {
    if (argc < 6) { fprintf(stderr, "usage: symrepair BASE D SECS SEED OUT\n"); return 1; }
    read_base(argv[1]);
    Dm = atoi(argv[2]);
    if (Dm > MAXDEP - 1) { fprintf(stderr, "D too large\n"); return 1; }
    double secs = atof(argv[3]);
    rs ^= (uint64_t)atoll(argv[4]) * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 10; i++) rnd();
    const char *out = argv[5];
    int K = getenv("K") ? atoi(getenv("K")) : 1;
    double T0 = getenv("T0") ? atof(getenv("T0")) : 1.0, T1 = getenv("T1") ? atof(getenv("T1")) : 0.1;
    NODES = getenv("NODES") ? atol(getenv("NODES")) : 100000;
    double pm[4] = {0.6, 0.15, 0.15, 0.1};
    if (getenv("PMIX") && sscanf(getenv("PMIX"), "%lf,%lf,%lf,%lf", &pm[0], &pm[1], &pm[2], &pm[3]) != 4) { fprintf(stderr, "PMIX needs 4 numbers\n"); return 1; }
    double psum = pm[0] + pm[1] + pm[2] + pm[3], cum[4], acc = 0;
    if (psum <= 0) { fprintf(stderr, "PMIX must not be all zero\n"); return 1; }
    for (int t = 0; t < 4; t++) { acc += pm[t] / psum; cum[t] = acc; }

    Ra = malloc(sizeof(u64) * V); Fa = malloc(sizeof(u64) * V); Xa = malloc(sizeof(u64) * V);
    distT = malloc(sizeof(int) * V); qbuf = malloc(sizeof(int) * V);
    LCAP = 3000000;
    LA = malloc(sizeof(Trip) * LCAP); LB = malloc(sizeof(Trip) * LCAP); LW = malloc(sizeof(Trip) * LCAP);
    int *allS = malloc(sizeof(int) * V); int NS = 0;
    { const char *sf = getenv("SRCFILE"); if (!sf) { fprintf(stderr, "SRCFILE required\n"); return 1; }
      FILE *f = fopen(sf, "r"); if (!f) { fprintf(stderr, "cannot open SRCFILE\n"); return 1; }
      int x; while (NS < V && fscanf(f, "%d", &x) == 1) allS[NS++] = x; fclose(f); }
    build_orbits();
    if (getenv("GROUP")) read_group(getenv("GROUP"));
    else if (pm[1] > 0 || pm[2] > 0) { fprintf(stderr, "GROUP required for align/swap moves\n"); return 1; }

    double t0 = now();
    long U_full = eval_set(allS, NS, LA, &nA);
    long best = U_full;
    if (secs <= 0) {
        printf("V=%d k=%d E=%d D=%d lift_vertices=%lld sources=%d uncovered=%ld time=%.2fs%s\n", V, k, E, Dm,
               (long long)V * k, NS, U_full, now() - t0, U_full == 0 ? " VALID(all orbit sources)" : "");
        return 0;
    }
    write_base(out);
    fprintf(stderr, "start U=%ld (k=%d, P=%d, PMIX=%.2f,%.2f,%.2f,%.2f K=%d NODES=%ld T0=%.2f T1=%.2f)\n", U_full, k, P,
            pm[0] / psum, pm[1] / psum, pm[2] / psum, pm[3] / psum, K, NODES, T0, T1);

    long Ucur = U_full, steps = 0, accs = 0;
    long nprop[4] = {0, 0, 0, 0}, nacc[4] = {0, 0, 0, 0};
    double tlast = t0;
    while (best > 0 && nA > 0 && now() - t0 < secs) {
        double tn = now();
        double T = T0 * pow(T1 / T0, (tn - t0) / secs);
        int type = pick_type(cum, pm);
        long bestU = -1; Cand bestC = {0, 0, 0, 0, 0};
        for (int c = 0; c < K; c++) {
            Cand C;
            if (!gen_cand(&C, type, LA, nA)) continue;
            nprop[type]++;
            apply_cand(&C);
            long Uc = eval_set(allS, NS, LW, &nW);
            undo_all();
            if (bestU < 0 || Uc < bestU) {
                bestU = Uc; bestC = C;
                Trip *tmp = LB; LB = LW; LW = tmp; nB = nW;
            }
        }
        steps++;
        if (bestU >= 0) {
            double u = unif() + 1e-300;
            if ((double)bestU <= (double)Ucur - T * log(u)) {       /* Metropolis: accept with prob exp(-(bestU-Ucur)/T) */
                apply_cand(&bestC); nacc[bestC.type]++; accs++;
                Ucur = bestU;
                Trip *tmp = LA; LA = LB; LB = tmp; nA = nB;
                if (Ucur < best) { best = Ucur; write_base(out); }
            }
        }
        if (tn - tlast > 10) {
            tlast = tn;
            fprintf(stderr, "t=%.0f steps=%ld acc=%ld T=%.3f U=%ld best=%ld prop=%ld/%ld/%ld/%ld acc=%ld/%ld/%ld/%ld\n",
                    tn - t0, steps, accs, T, Ucur, best, nprop[0], nprop[1], nprop[2], nprop[3], nacc[0], nacc[1], nacc[2], nacc[3]);
        }
    }
    printf("RESULT V=%d k=%d D=%d best=%ld steps=%ld acc=%ld secs=%.0f out=%s prop=%ld/%ld/%ld/%ld accby=%ld/%ld/%ld/%ld%s\n",
           V, k, Dm, best, steps, accs, now() - t0, out, nprop[0], nprop[1], nprop[2], nprop[3],
           nacc[0], nacc[1], nacc[2], nacc[3], best == 0 ? " (orbit-source U = 0: run baselift eval to confirm)" : "");
    return 0;
}
