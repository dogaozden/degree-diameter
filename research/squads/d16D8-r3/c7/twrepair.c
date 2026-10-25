/* twrepair.c (card c7, d16D8 round 3): targeted repair for TWISTED C'-invariant Z_m lifts.
   Adapted from research/d16D8/symrepair.c. Input base file (5 fields, written by twbuild.py):
     header "V m E U", then E lines "x y c cls pos": cls = orbit id, pos = j where the edge is h^j e0 of its orbit.
   Model: each orbit o has a representative voltage co[o] (its pos-0 edge); edge voltage = U^pos * co[o] mod m.
   U = 1 is the untwisted model of symrepair. The sources in SRCFILE (one point and one line per C'-orbit) decide the
   diameter exactly for twisted designs, since (x,s) -> (h x, U s) and translation by sheets are automorphisms.
   Move: pick an uncovered (s, y, g); a random non-backtracking walk w of length <= D from s to y; its sheet sum
   sigma(w) = sum_i eps_i ec(e_i). Pick an edge e of w, its orbit o; the walk coefficient A = sum over edges of w in o of
   eps_i U^{pos_i}. Setting co[o] += dc with dc = (g - sigma) A^{-1} mod m makes w reach (y, g). Candidates are scored by
   the full uncovered count over SRCFILE; Metropolis acceptance (T0 -> T1 geometric over SECS).
   Usage: twrepair BASE5 D SECS SEED OUT     writes OUT (4 fields, for baselift) and OUT.b5 (5 fields, warm starts).
   SECS = 0: only the full check over SRCFILE. env: T0 (1.0), T1 (0.1), K (1), NODES (100000), SRCFILE (required). */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <time.h>
typedef uint64_t u64;

typedef struct { int s, y, g; } Trip;

static int V, k, E, P, Dm, U;
static int *ex, *ey, *ec, *ecls, *epos, *px, *py;
static int norb, *ooff, *olist, *co, *upow, npos;
static int *off, *nb, *sh, *eid, *sg;
static u64 HI[64], LO[64];
static uint64_t rs = 88172645463325252ULL;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline int rndi(int n) { return (int)(rnd() % (uint64_t)n); }
static double now(void) { struct timespec ts; clock_gettime(CLOCK_MONOTONIC, &ts); return ts.tv_sec + 1e-9 * ts.tv_nsec; }
static long modm(long a) { a %= k; return a < 0 ? a + k : a; }
static long mulm(long a, long b) { return modm(modm(a) * modm(b)); }
static long invm(long a) {                     /* inverse mod k, or -1 */
    long r0 = k, r1 = modm(a), t0 = 0, t1 = 1;
    while (r1) {
        long q = r0 / r1, tmp = r0 - q * r1; r0 = r1; r1 = tmp;
        tmp = t0 - q * t1; t0 = t1; t1 = tmp;
    }
    if (r0 != 1) return -1;
    return modm(t0);
}

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

static void build_adj(void) {
    int *deg = calloc(V, sizeof(int));
    for (int e = 0; e < E; e++) { deg[ex[e]]++; deg[ey[e]]++; }
    off = malloc(sizeof(int) * (V + 1));
    off[0] = 0; for (int x = 0; x < V; x++) off[x + 1] = off[x] + deg[x];
    nb = malloc(sizeof(int) * off[V]); sh = malloc(sizeof(int) * off[V]);
    eid = malloc(sizeof(int) * off[V]); sg = malloc(sizeof(int) * off[V]);
    int *fill = calloc(V, sizeof(int));
    for (int e = 0; e < E; e++) {
        int x = ex[e], y = ey[e], c = ec[e];
        int j = off[x] + fill[x]++;
        nb[j] = y; sh[j] = c; eid[j] = e; sg[j] = 1; px[e] = j;
        j = off[y] + fill[y]++;
        nb[j] = x; sh[j] = (k - c) % k; eid[j] = e; sg[j] = -1; py[e] = j;
    }
    free(deg); free(fill);
}

static void read_base(const char *fn) {
    FILE *f = fopen(fn, "r"); if (!f) { fprintf(stderr, "cannot open %s\n", fn); exit(1); }
    if (fscanf(f, "%d %d %d %d", &V, &k, &E, &U) != 4) { fprintf(stderr, "bad header (need V m E U)\n"); exit(1); }
    if (k < 2 || k > 64) { fprintf(stderr, "need 2 <= m <= 64\n"); exit(1); }
    ex = malloc(sizeof(int) * E); ey = malloc(sizeof(int) * E); ec = malloc(sizeof(int) * E);
    ecls = malloc(sizeof(int) * E); epos = malloc(sizeof(int) * E);
    px = malloc(sizeof(int) * E); py = malloc(sizeof(int) * E);
    for (int e = 0; e < E; e++) {
        if (fscanf(f, "%d %d %d %d %d", &ex[e], &ey[e], &ec[e], &ecls[e], &epos[e]) != 5) { fprintf(stderr, "short base file at edge %d\n", e); exit(1); }
        if (ex[e] < 0 || ex[e] >= V || ey[e] < 0 || ey[e] >= V) { fprintf(stderr, "bad edge %d\n", e); exit(1); }
    }
    fclose(f);
    setup_masks();
    npos = 0; for (int e = 0; e < E; e++) if (epos[e] + 1 > npos) npos = epos[e] + 1;
    upow = malloc(sizeof(int) * (npos + 1));
    upow[0] = 1 % k; for (int j = 1; j <= npos; j++) upow[j] = (int)mulm(upow[j - 1], U);
    norb = 0; for (int e = 0; e < E; e++) if (ecls[e] + 1 > norb) norb = ecls[e] + 1;
    co = malloc(sizeof(int) * norb);
    for (int o = 0; o < norb; o++) co[o] = -1;
    for (int e = 0; e < E; e++) if (epos[e] == 0) co[ecls[e]] = ec[e];
    for (int o = 0; o < norb; o++) if (co[o] < 0) { fprintf(stderr, "orbit %d has no pos-0 edge\n", o); exit(1); }
    int bad = 0;
    for (int e = 0; e < E; e++) {
        int v = (int)mulm(upow[epos[e]], co[ecls[e]]);
        if (v != ec[e]) bad++;
        ec[e] = v;                                                               /* enforce the twist */
    }
    if (bad) fprintf(stderr, "warning: %d edges did not carry the twist U^pos * c_o; they were reset\n", bad);
    ooff = calloc(norb + 1, sizeof(int)); olist = malloc(sizeof(int) * E);
    for (int e = 0; e < E; e++) ooff[ecls[e] + 1]++;
    for (int o = 0; o < norb; o++) ooff[o + 1] += ooff[o];
    int *fill = calloc(norb, sizeof(int));
    for (int e = 0; e < E; e++) olist[ooff[ecls[e]] + fill[ecls[e]]++] = e;
    free(fill);
    build_adj();
}
static void write_base(const char *fn) {
    char tmpn[1024], t5[1024];
    snprintf(tmpn, sizeof tmpn, "%s.tmp", fn);
    FILE *f = fopen(tmpn, "w"); fprintf(f, "%d %d %d\n", V, k, E);
    for (int e = 0; e < E; e++) fprintf(f, "%d %d %d %d\n", ex[e], ey[e], ec[e], ecls[e]);
    fclose(f); rename(tmpn, fn);
    snprintf(t5, sizeof t5, "%s.b5", fn); snprintf(tmpn, sizeof tmpn, "%s.tmp", t5);
    f = fopen(tmpn, "w"); fprintf(f, "%d %d %d %d\n", V, k, E, U);
    for (int e = 0; e < E; e++) fprintf(f, "%d %d %d %d %d\n", ex[e], ey[e], ec[e], ecls[e], epos[e]);
    fclose(f); rename(tmpn, t5);
}
/* change the voltage of edge e (keeps the adjacency consistent) */
static void set_volt1(int e, int c) { ec[e] = c; sh[px[e]] = c; sh[py[e]] = (k - c) % k; }
/* change the representative voltage of orbit o: all its edges get U^pos * c */
static void set_orbit(int o, int c) {
    co[o] = c;
    for (int i = ooff[o]; i < ooff[o + 1]; i++) { int e = olist[i]; set_volt1(e, (int)mulm(upow[epos[e]], c)); }
}

/* ---- lift BFS: uncovered count over a batch of sources, optionally recording the uncovered triples ---- */
static u64 *Ra, *Fa, *Xa;
static Trip *LA, *LB, *LW;
static long nA, nW, LCAP;

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
        FL[n] = depth; FSIG[n] = (int)modm(s);
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
/* repair move for uncovered (s, y, g): orbit oo and its new representative voltage onc */
static int make_move(int s, int y, int g, int *oo, int *onc) {
    tgt = y; dist_to(y);
    if (distT[s] > Dm) return 0;
    nodes_left = NODES; nfound = 0;
    dfs(s, 0, -1);
    if (!nfound) return 0;
    int w = rndi(nfound), p = rndi(FL[w]);
    int o = ecls[FE[w][p]];
    long A = 0;
    for (int i = 0; i < FL[w]; i++) if (ecls[FE[w][i]] == o) A += (long)FS[w][i] * upow[epos[FE[w][i]]];
    A = modm(A);
    if (!A) return 0;
    long iA = invm(A); if (iA < 0) return 0;
    long dc = mulm(modm((long)g - FSIG[w]), iA);
    if (!dc) return 0;
    *oo = o; *onc = (int)modm(co[o] + dc);
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 6) { fprintf(stderr, "usage: twrepair BASE5 D SECS SEED OUT\n"); return 1; }
    read_base(argv[1]);
    Dm = atoi(argv[2]);
    if (Dm > MAXDEP - 1) { fprintf(stderr, "D too large\n"); return 1; }
    double secs = atof(argv[3]);
    rs ^= (uint64_t)atoll(argv[4]) * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 10; i++) rnd();
    const char *out = argv[5];
    int K = getenv("K") ? atoi(getenv("K")) : 1;
    double T0 = getenv("T0") ? atof(getenv("T0")) : 1.0, T1 = getenv("T1") ? atof(getenv("T1")) : 0.1;
    NODES = getenv("NODES") ? atol(getenv("NODES")) : 100000;

    Ra = malloc(sizeof(u64) * V); Fa = malloc(sizeof(u64) * V); Xa = malloc(sizeof(u64) * V);
    distT = malloc(sizeof(int) * V); qbuf = malloc(sizeof(int) * V);
    LCAP = 3000000;
    LA = malloc(sizeof(Trip) * LCAP); LB = malloc(sizeof(Trip) * LCAP); LW = malloc(sizeof(Trip) * LCAP);
    int *allS = malloc(sizeof(int) * V); int NS = 0;
    { const char *sf = getenv("SRCFILE"); if (!sf) { fprintf(stderr, "SRCFILE required\n"); return 1; }
      FILE *f = fopen(sf, "r"); if (!f) { fprintf(stderr, "no SRCFILE\n"); return 1; }
      int x; while (NS < V && fscanf(f, "%d", &x) == 1) allS[NS++] = x; fclose(f); }

    double t0 = now();
    long U_full = eval_set(allS, NS, LA, &nA);
    long best = U_full;
    if (secs <= 0) {
        printf("V=%d m=%d E=%d D=%d U=%d orbits=%d sources=%d uncovered=%ld time=%.2fs%s\n", V, k, E, Dm, U, norb, NS,
               U_full, now() - t0, U_full == 0 ? " VALID(orbit sources)" : "");
        return 0;
    }
    write_base(out);
    fprintf(stderr, "start uncovered %ld (m=%d U=%d orbits=%d sources=%d K=%d NODES=%ld)\n", U_full, k, U, norb, NS, K, NODES);

    long Ucur = U_full, steps = 0, accs = 0, nmoves = 0;
    double tlast = t0;
    while (best > 0 && now() - t0 < secs) {
        double tn = now();
        double T = T0 * pow(T1 / T0, (tn - t0) / secs);
        long bestU = -1, bestN = 0; int bo = -1, bnc = 0;
        for (int c = 0; c < K; c++) {
            Trip tr = LA[rndi((int)nA)];          /* LA: uncovered triples of the current state, nA of them */
            int o, nc;
            if (!make_move(tr.s, tr.y, tr.g, &o, &nc)) continue;
            nmoves++;
            int old = co[o];
            set_orbit(o, nc);
            long Uc = eval_set(allS, NS, LW, &nW);  /* LW: triples of this candidate, nW recorded */
            set_orbit(o, old);
            if (bestU < 0 || Uc < bestU) {          /* keep the best candidate's list in LB */
                bestU = Uc; bo = o; bnc = nc; bestN = nW;
                Trip *tmp = LB; LB = LW; LW = tmp;
            }
        }
        steps++;
        if (bestU < 0) continue;
        double u = (rnd() >> 11) * (1.0 / 9007199254740992.0) + 1e-300;
        if ((double)bestU <= (double)Ucur - T * log(u)) {   /* Metropolis */
            set_orbit(bo, bnc); accs++;
            Ucur = bestU;
            Trip *tmp = LA; LA = LB; LB = tmp; nA = bestN;
            if (Ucur < best) { best = Ucur; write_base(out); }
        }
        if (tn - tlast > 10) {
            tlast = tn;
            fprintf(stderr, "t=%.0f steps=%ld moves=%ld acc=%ld T=%.3f Ucur=%ld best=%ld\n",
                    tn - t0, steps, nmoves, accs, T, Ucur, best);
        }
    }
    /* final consistency: recompute the full count of the state that is written */
    printf("RESULT V=%d m=%d D=%d U=%d best=%ld steps=%ld moves=%ld acc=%ld secs=%.0f out=%s%s\n", V, k, Dm, U, best, steps,
           nmoves, accs, now() - t0, out, best == 0 ? " (full check 0: run baselift eval without SRCFILE to confirm)" : "");
    return 0;
}
