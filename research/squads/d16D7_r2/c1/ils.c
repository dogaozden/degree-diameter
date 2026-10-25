/* c1/ils.c: Andrade-Resende-Werneck iterated local search (ARW 2012) for maximum independent set.

   usage: ils GRAPH SEED OUT CPU_SECONDS RNG [R=2] [T=4] [PK=0.02] [SELECT=0] [W=0]
     GRAPH   ogscore format: "M E", then per vertex "idx rep deg nbrs..."
     SEED    one vertex index per line, an independent set (start point)
     OUT     best independent set found, one index per line, ascending
     R       revert to the basin best when basinBest - curN >= R
     T       number of random candidates sampled for each forced insertion
     PK      each extra forced vertex has probability PK (k = 1, 2, 3, 4 with decreasing odds)
     SELECT  0: among the sampled candidates take min tightness, ties to the oldest;
             1: take the oldest only (ARW-style age rule)
     W       if > 0: after W iterations without improving the basin best, restart from the empty
             set (R alternates between R and R+1 over restarts); the global best is kept

   State: inS, solution array with positions, tau[v] = number of solution neighbours,
   xs[v] = XOR of the solution neighbours' ids (so a 1-tight vertex's unique neighbour is xs[v]),
   a free list {v not in S : tau[v]=0} kept exact, and a FIFO queue of solution vertices whose
   1-tight neighbourhood may have changed (the only places a new (1,2)-swap can appear).
   Adjacency is a bit matrix (O(1) test) plus CSR lists built from it.
   Each perturbation + local search is journaled, so a rejected move is undone exactly.
*/
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

static int M, E, W;
static uint64_t *bits;
static int *adjStart, *deg, *adj;

static uint64_t rs = 1;
static inline uint64_t rnd64(void) {
    uint64_t x = rs;
    x ^= x >> 12; x ^= x << 25; x ^= x >> 27;
    rs = x;
    return x * 2685821657736338717ULL;
}
static inline uint32_t rndn(uint32_t n) { return (uint32_t)(((rnd64() >> 32) * (uint64_t)n) >> 32); }
static inline double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static inline int isAdj(int u, int v) { return (int)((bits[(size_t)u * W + (v >> 6)] >> (v & 63)) & 1ULL); }

static char *inS, *inQ;
static int *tau, *xs;
static int *solArr, *solPos, solN;
static int *freeArr, *freePos, freeN;
static int *cq, cqHead, cqN;
static int *jr;
static size_t jn, jcap;
static long long *stamp;
static long long iter = 0;
static int *rbSol, rbN;          /* best of the current basin (acceptance and revert target) */
static char *rbIn;
static int *gbSol, gbN;          /* global best over all basins */
static int *Lbuf;
static int noPush = 0, journaling = 0;
static int Rdrop = 2, Rbase = 2, Tsel = 4, selMode = 0;
static double pk_ = 0.1;
static long long Wst = 0, lastImpr = 0;
static int nrest = 0;

static double cpu(void) { return (double)clock() / CLOCKS_PER_SEC; }

static inline void freeAdd(int v) { freePos[v] = freeN; freeArr[freeN++] = v; }
static inline void freeDel(int v) {
    int p = freePos[v], last = freeArr[--freeN];
    freeArr[p] = last; freePos[last] = p; freePos[v] = -1;
}
static inline void cpush(int x) {
    if (inQ[x]) return;
    inQ[x] = 1;
    int t = cqHead + cqN; if (t >= M) t -= M;
    cq[t] = x; cqN++;
}
static inline int cpop(void) {
    int x = cq[cqHead]; cqHead++; if (cqHead == M) cqHead = 0;
    cqN--; inQ[x] = 0;
    return x;
}
static inline void jpush(int code) {
    if (jn == jcap) {
        jcap = jcap ? 2 * jcap : (1u << 16);
        jr = realloc(jr, jcap * sizeof(int));
        if (!jr) { fprintf(stderr, "out of memory (journal)\n"); exit(3); }
    }
    jr[jn++] = code;
}

/* insert free vertex v (tau[v]==0, not in S) */
static void addV(int v) {
    if (freePos[v] >= 0) freeDel(v);
    inS[v] = 1; solPos[v] = solN; solArr[solN++] = v;
    const int *a = adj + adjStart[v];
    int d = deg[v];
    for (int i = 0; i < d; i++) {
        int u = a[i];
        tau[u]++; xs[u] ^= v;
        if (!inS[u] && tau[u] == 1) freeDel(u);      /* was free, now 1-tight with unique neighbour v */
    }
    if (!noPush) cpush(v);
    if (journaling) jpush(v << 1);
}

/* remove solution vertex v; v itself becomes free (it has no solution neighbours) */
static void remV(int v) {
    inS[v] = 0;
    int p = solPos[v], last = solArr[--solN];
    solArr[p] = last; solPos[last] = p; solPos[v] = -1;
    freeAdd(v);
    const int *a = adj + adjStart[v];
    int d = deg[v];
    for (int i = 0; i < d; i++) {
        int u = a[i];
        tau[u]--; xs[u] ^= v;
        if (!inS[u]) {
            if (tau[u] == 0) freeAdd(u);
            else if (tau[u] == 1 && !noPush) cpush(xs[u]);
        }
    }
    if (journaling) { jpush((v << 1) | 1); stamp[v] = iter; }
}

/* (1,2)-swaps and free insertions until the solution is locally optimal */
static void localSearch(void) {
    for (;;) {
        while (freeN > 0) {
            int v = freeArr[rndn((uint32_t)freeN)];
            addV(v);
        }
        if (cqN == 0) break;
        int x = cpop();
        if (!inS[x]) continue;
        int nl = 0;
        const int *a = adj + adjStart[x];
        int d = deg[x];
        for (int i = 0; i < d; i++) {
            int u = a[i];
            if (!inS[u] && tau[u] == 1) Lbuf[nl++] = u;
        }
        if (nl < 2) continue;
        for (int i = nl - 1; i > 0; i--) {
            int j = (int)rndn((uint32_t)(i + 1));
            int t = Lbuf[i]; Lbuf[i] = Lbuf[j]; Lbuf[j] = t;
        }
        int fa = -1, fb = -1;
        for (int i = 0; i < nl && fa < 0; i++)
            for (int j = i + 1; j < nl; j++)
                if (!isAdj(Lbuf[i], Lbuf[j])) { fa = Lbuf[i]; fb = Lbuf[j]; break; }
        if (fa < 0) continue;
        remV(x);
        addV(fa);
        addV(fb);
    }
}

/* force in one or more non-solution vertices, removing their solution neighbours */
static void perturb(void) {
    int k = 1;
    while (k < 4 && rnd01() < pk_) k++;
    for (int t = 0; t < k; t++) {
        int best = -1;
        for (int s = 0; s < Tsel; s++) {
            int v;
            do { v = (int)rndn((uint32_t)M); } while (inS[v]);
            if (best < 0) { best = v; continue; }
            if (selMode == 0) {
                if (tau[v] < tau[best] || (tau[v] == tau[best] && stamp[v] < stamp[best])) best = v;
            } else {
                if (stamp[v] < stamp[best]) best = v;
            }
        }
        const int *a = adj + adjStart[best];
        int d = deg[best];
        for (int i = 0; i < d; i++) if (inS[a[i]]) remV(a[i]);
        addV(best);
    }
}

/* undo everything journaled since the last checkpoint (exact inverse, in reverse order) */
static void undoJournal(void) {
    int saveJ = journaling;
    journaling = 0;
    noPush = 1;
    for (size_t i = jn; i-- > 0;) {
        int c = jr[i], v = c >> 1;
        if (c & 1) addV(v); else remV(v);
    }
    noPush = 0;
    journaling = saveJ;
    while (cqN) cpop();
    jn = 0;
}

static void saveRun(void) {
    for (int i = 0; i < rbN; i++) rbIn[rbSol[i]] = 0;
    rbN = solN;
    memcpy(rbSol, solArr, sizeof(int) * (size_t)solN);
    for (int i = 0; i < rbN; i++) rbIn[rbSol[i]] = 1;
}

static void saveGlobal(void) {
    gbN = solN;
    memcpy(gbSol, solArr, sizeof(int) * (size_t)solN);
}

/* move the current solution to the basin best by a set difference (rbSol is a local optimum) */
static void revertToRun(void) {
    noPush = 1;
    for (int i = solN - 1; i >= 0; i--) {
        int v = solArr[i];
        if (!rbIn[v]) remV(v);
    }
    for (int i = 0; i < rbN; i++) {
        int v = rbSol[i];
        if (!inS[v]) addV(v);
    }
    noPush = 0;
    while (cqN) cpop();
    jn = 0;
}

/* empty the solution and rebuild a fresh greedy local optimum (a new basin) */
static void restartFromEmpty(void) {
    noPush = 1;
    for (int i = solN - 1; i >= 0; i--) remV(solArr[i]);
    noPush = 0;
    while (cqN) cpop();
    jn = 0;
    for (int i = 0; i < rbN; i++) rbIn[rbSol[i]] = 0;
    rbN = 0;
    localSearch();
    saveRun();
}

static int isLocalOpt(void) {
    if (freeN) return 0;
    for (int x = 0; x < M; x++) {
        if (!inS[x]) continue;
        int nl = 0;
        for (int i = 0; i < deg[x]; i++) {
            int u = adj[adjStart[x] + i];
            if (!inS[u] && tau[u] == 1) Lbuf[nl++] = u;
        }
        for (int a = 0; a < nl; a++)
            for (int b = a + 1; b < nl; b++)
                if (!isAdj(Lbuf[a], Lbuf[b])) return 0;
    }
    return 1;
}

static void checkState(const char *where) {
    int cnt = 0;
    for (int v = 0; v < M; v++) {
        int c = 0, x = 0;
        for (int i = 0; i < deg[v]; i++) { int u = adj[adjStart[v] + i]; if (inS[u]) { c++; x ^= u; } }
        if (c != tau[v] || x != xs[v]) { fprintf(stderr, "CHECK %s: tau/xs mismatch v=%d c=%d tau=%d\n", where, v, c, tau[v]); exit(2); }
        if (inS[v] && c) { fprintf(stderr, "CHECK %s: not independent v=%d\n", where, v); exit(2); }
        if ((inS[v] != 0) != (solPos[v] >= 0)) { fprintf(stderr, "CHECK %s: solPos v=%d\n", where, v); exit(2); }
        if (inS[v] && solArr[solPos[v]] != v) { fprintf(stderr, "CHECK %s: solArr v=%d\n", where, v); exit(2); }
        int isFree = (!inS[v] && tau[v] == 0);
        if (isFree != (freePos[v] >= 0)) { fprintf(stderr, "CHECK %s: free list v=%d\n", where, v); exit(2); }
        if (inS[v]) cnt++;
    }
    if (cnt != solN) { fprintf(stderr, "CHECK %s: solN\n", where); exit(2); }
}

static void die(const char *msg) { fprintf(stderr, "%s\n", msg); exit(1); }

int main(int argc, char **argv) {
    if (argc < 6) {
        fprintf(stderr, "usage: ils GRAPH SEED OUT CPU_SECONDS RNG [R T PK SELECT]\n");
        return 1;
    }
    const char *gpath = argv[1], *spath = argv[2], *opath = argv[3];
    double limit = atof(argv[4]);
    rs = 0x9E3779B97F4A7C15ULL ^ (strtoull(argv[5], NULL, 10) * 0xD1B54A32D192ED03ULL);
    if (rs == 0) rs = 1;
    for (int i = 0; i < 10; i++) rnd64();
    if (argc > 6) Rdrop = atoi(argv[6]);
    if (argc > 7) Tsel = atoi(argv[7]);
    if (argc > 8) pk_ = atof(argv[8]);
    if (argc > 9) selMode = atoi(argv[9]);
    if (argc > 10) Wst = atoll(argv[10]);
    Rbase = Rdrop;

    /* graph */
    FILE *fp = fopen(gpath, "r");
    if (!fp) { perror(gpath); return 1; }
    if (fscanf(fp, "%d %d", &M, &E) != 2) die("bad header");
    W = (M + 63) / 64;
    bits = calloc((size_t)M * W, sizeof(uint64_t));
    if (!bits) die("out of memory");
    for (int li = 0; li < M; li++) {
        int idx, rep, d;
        if (fscanf(fp, "%d %d %d", &idx, &rep, &d) != 3 || idx < 0 || idx >= M) die("bad vertex line");
        for (int j = 0; j < d; j++) {
            int x;
            if (fscanf(fp, "%d", &x) != 1 || x < 0 || x >= M || x == idx) die("bad neighbour");
            bits[(size_t)idx * W + (x >> 6)] |= 1ULL << (x & 63);
            bits[(size_t)x * W + (idx >> 6)] |= 1ULL << (idx & 63);
        }
    }
    fclose(fp);
    deg = calloc(M, sizeof(int));
    adjStart = calloc(M, sizeof(int));
    size_t tot = 0;
    for (int v = 0; v < M; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += __builtin_popcountll(bits[(size_t)v * W + w]);
        deg[v] = c; adjStart[v] = (int)tot; tot += (size_t)c;
    }
    adj = malloc((tot ? tot : 1) * sizeof(int));
    for (int v = 0; v < M; v++) {
        size_t p = (size_t)adjStart[v];
        for (int w = 0; w < W; w++) {
            uint64_t b = bits[(size_t)v * W + w];
            while (b) { int t = __builtin_ctzll(b); adj[p++] = w * 64 + t; b &= b - 1; }
        }
    }
    printf("graph M=%d E_header=%d E_closure=%zu\n", M, E, tot / 2);

    /* seed */
    int *seed = malloc((size_t)M * sizeof(int));
    int ns = 0;
    FILE *sp = fopen(spath, "r");
    if (!sp) { perror(spath); return 1; }
    char line[256];
    while (fgets(line, sizeof line, sp)) {
        if (line[0] == '#' || line[0] == '\n') continue;
        char *e;
        long v = strtol(line, &e, 10);
        if (e == line) continue;
        if (v < 0 || v >= M) die("seed index out of range");
        seed[ns++] = (int)v;
    }
    fclose(sp);

    /* state */
    inS = calloc(M, 1); inQ = calloc(M, 1);
    tau = calloc(M, sizeof(int)); xs = calloc(M, sizeof(int));
    solArr = malloc((size_t)M * sizeof(int)); solPos = malloc((size_t)M * sizeof(int));
    freeArr = malloc((size_t)M * sizeof(int)); freePos = malloc((size_t)M * sizeof(int));
    cq = malloc((size_t)M * sizeof(int));
    stamp = calloc(M, sizeof(long long));
    rbSol = malloc((size_t)M * sizeof(int)); rbIn = calloc(M, 1);
    gbSol = malloc((size_t)M * sizeof(int)); Lbuf = malloc((size_t)M * sizeof(int));
    if (!inS || !inQ || !rbIn || !tau || !xs || !solArr || !solPos || !freeArr || !freePos || !cq || !stamp || !rbSol || !gbSol || !Lbuf)
        die("out of memory");
    for (int v = 0; v < M; v++) { solPos[v] = -1; freePos[v] = -1; }
    freeN = 0;
    for (int v = 0; v < M; v++) freeAdd(v);
    solN = 0; cqHead = 0; cqN = 0;

    for (int i = 0; i < ns; i++) {
        int v = seed[i];
        if (inS[v]) die("seed has a duplicate");
        if (tau[v] != 0) die("seed is not independent");
        addV(v);
    }
    printf("seed size=%d\n", ns);
    localSearch();
    saveRun();
    saveGlobal();
    printf("after initial local search size=%d\n", rbN);
    fflush(stdout);

    /* iterated local search; optional restarts from empty after Wst iterations without a basin improvement */
    double nextLog = 5.0;
    long long nacc = 0, nworse = 0, nrev = 0;
    lastImpr = 0;
    for (iter = 1;; iter++) {
        if ((iter & 511) == 0) {
            double t = cpu();
            if (t >= limit) break;
            if (t >= nextLog) {
                printf("t=%.1f iter=%lld cur=%d basin=%d global=%d restarts=%d accepted=%lld worse_acc=%lld reverts=%lld\n",
                       t, (long long)iter, solN, rbN, gbN, nrest, nacc, nworse, nrev);
                fflush(stdout);
                nextLog += 5.0;
            }
        }
        int before = solN;
        jn = 0;
        journaling = 1;
        perturb();
        localSearch();
        journaling = 0;
        int after = solN;
        int accept;
        if (after >= before) accept = 1;
        else {
            int d = before - after, ds = rbN - after;
            accept = rnd01() < 1.0 / (1.0 + (double)d * (double)ds);
            if (accept) nworse++;
        }
#ifdef CHECK
        if (!isLocalOpt()) { fprintf(stderr, "CHECK: not a local optimum at iter %lld\n", (long long)iter); exit(2); }
        if ((iter % 97) == 0) checkState("after LS");
#endif
        if (accept) {
            nacc++;
            if (after > rbN) {
                saveRun();
                lastImpr = iter;
                if (after > gbN) {
                    saveGlobal();
                    printf("NEW BEST t=%.2f iter=%lld size=%d basin=%d\n", cpu(), (long long)iter, gbN, nrest);
                    fflush(stdout);
                }
            }
        } else {
            undoJournal();
#ifdef CHECK
            if ((iter % 97) == 0) checkState("after undo");
            if (solN != before) { fprintf(stderr, "CHECK: undo size mismatch\n"); exit(2); }
#endif
        }
        if (rbN - solN >= Rdrop) { revertToRun(); nrev++; }
#ifdef CHECK
        if ((iter % 97) == 0) checkState("after accept/revert");
#endif
        if (Wst > 0 && iter - lastImpr >= Wst) {
            printf("BASIN %d end t=%.2f iter=%lld basin_best=%d global=%d\n", nrest, cpu(), (long long)iter, rbN, gbN);
            fflush(stdout);
            nrest++;
            Rdrop = (nrest % 2) ? Rbase : Rbase + 1;
            restartFromEmpty();
            lastImpr = iter;
#ifdef CHECK
            checkState("after restart");
            if (!isLocalOpt()) { fprintf(stderr, "CHECK: restart not a local optimum\n"); exit(2); }
#endif
        }
    }
    jn = 0;
    printf("done: iters=%lld global=%d restarts=%d accepted=%lld worse_acc=%lld reverts=%lld cpu=%.1f\n",
           (long long)iter, gbN, nrest, nacc, nworse, nrev, cpu());

    /* verify and write the global best */
    for (int i = 0; i < gbN; i++)
        for (int j = i + 1; j < gbN; j++)
            if (isAdj(gbSol[i], gbSol[j])) { fprintf(stderr, "INTERNAL: best not independent\n"); return 4; }
    char *gin = calloc(M, 1);
    for (int i = 0; i < gbN; i++) gin[gbSol[i]] = 1;
    FILE *op = fopen(opath, "w");
    if (!op) { perror(opath); return 1; }
    int written = 0;
    for (int v = 0; v < M; v++) if (gin[v]) { fprintf(op, "%d\n", v); written++; }
    fclose(op);
    printf("wrote %d vertices to %s\n", written, opath);
    return 0;
}
