/* dmhub.c: hub vertices on the doubled-matching (DM) Z6-lift of W(q) (research/d10D7/DM_D5.md).
 *
 * DM lift: base W(q) incidence graph (N points, N lines) + a bijection sigma (point -> line) whose edges are doubled
 * with voltages mv0, mv1 (1 and 4); flag voltages in {0,3}. 6*2N vertices, degree q+3, diameter 5 (the 4,800 graph
 * at q = 7).  Freeing a point p deletes the 12 lift edges (p,h)-(sigma(p),h+mv) and adds H "line-side" hubs adjacent
 * to the whole fibre (p,*) and H "point-side" hubs adjacent to the fibre (sigma(p),*): +2H vertices per freed point,
 * degrees stay <= q+3 for H <= 2.  A hub joined to a whole fibre reaches everything within 1 + 4.
 *
 * The program anneals sigma (swaps) and nu (flag flips) to make the hub graph have diameter <= 5.  Cost = number of
 * pairs (s, t) with d(s, t) > 5, over sources s = (v, 0) and the hubs (the graph keeps the Z6 symmetry, so these
 * sources suffice), computed exactly by bit-parallel BFS.  Writes the final graph as an edge list (first line n).
 *
 * usage: dmhub GQBIN SOLIN OUTPREFIX   env: FREE="p1 p2 ..." (freed points) or NFREE=k (random collinear set on a
 *   line), H (hubs per side per freed point, default 2), SEED, ITERS, SECS, T0, T1, FOCUS (prob. that a sigma move
 *   touches the focus set), PNU (prob. of a nu move), PFREE (allow sigma(p) of freed p to move: 0/1)
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <time.h>

static int q, N, Q1, M = 6;
static int *pts;            /* line l -> Q1 points */
static int *lof;            /* point p -> Q1 lines */
static int *hv;             /* flag (l,k) voltage */
static int *sig, *sinv, *mv0, *mv1;
static int nfree, freep[64], isfree[4096];
static int H = 2;
static int nhg = 0, hgA[4096], hgB[4096];   /* hub graph edges: line-side hub index, point-side hub index (0..H*nfree-1) */
static uint64_t rs = 88172645463325252ULL;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static double urand(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

/* graph */
static int nV, nE, *eu, *ev, *st, *adj, *deg;
static uint64_t *vis, *fr, *nx;

static void build(void) {
    nE = 0;
    for (int l = 0; l < N; l++) for (int k = 0; k < Q1; k++) {
        int p = pts[l * Q1 + k], g = hv[l * Q1 + k];
        for (int h = 0; h < M; h++) { eu[nE] = p * M + h; ev[nE] = (N + l) * M + (h + g) % M; nE++; }
    }
    for (int p = 0; p < N; p++) if (!isfree[p]) for (int h = 0; h < M; h++) {
        eu[nE] = p * M + h; ev[nE] = (N + sig[p]) * M + (h + mv0[p]) % M; nE++;
        eu[nE] = p * M + h; ev[nE] = (N + sig[p]) * M + (h + mv1[p]) % M; nE++;
    }
    int hub = 2 * N * M;
    for (int i = 0; i < nfree; i++) {
        int p = freep[i], l = N + sig[p];
        for (int t = 0; t < H; t++) { for (int h = 0; h < M; h++) { eu[nE] = hub; ev[nE] = p * M + h; nE++; } hub++; }
        for (int t = 0; t < H; t++) { for (int h = 0; h < M; h++) { eu[nE] = hub; ev[nE] = l * M + h; nE++; } hub++; }
    }
    nV = hub;
    for (int e = 0; e < nhg; e++) {   /* line-side hub (i,s) = base + i*2H + s, point-side hub (j,t) = base + j*2H + H + t */
        int a = hgA[e], b = hgB[e], base = 2 * N * M;
        eu[nE] = base + (a / H) * 2 * H + a % H; ev[nE] = base + (b / H) * 2 * H + H + b % H; nE++;
    }
    memset(deg, 0, sizeof(int) * nV);
    for (int i = 0; i < nE; i++) { deg[eu[i]]++; deg[ev[i]]++; }
    st[0] = 0; for (int i = 0; i < nV; i++) st[i + 1] = st[i] + deg[i];
    memset(deg, 0, sizeof(int) * nV);
    for (int i = 0; i < nE; i++) { adj[st[eu[i]] + deg[eu[i]]++] = ev[i]; adj[st[ev[i]] + deg[ev[i]]++] = eu[i]; }
}

/* number of (source, target) pairs at distance > D, sources = (v,0) for all base v, and all hubs */
static int D = 5;
static int nbadrec = 0, badS[4096], badT[4096];
static long cost_eval(long *perside) {
    nbadrec = 0;
    static int *src = NULL; static int ns = 0;
    if (!src) src = malloc(sizeof(int) * (2 * N + 1024));
    ns = 0; for (int v = 0; v < 2 * N; v++) src[ns++] = v * M; for (int x = 2 * N * M; x < nV; x++) src[ns++] = x;
    long bad = 0; if (perside) perside[0] = perside[1] = perside[2] = 0;
    for (int b = 0; b < ns; b += 64) {
        int nb = ns - b < 64 ? ns - b : 64; uint64_t full = nb == 64 ? ~0ULL : ((1ULL << nb) - 1);
        memset(vis, 0, 8L * nV); memset(fr, 0, 8L * nV);
        for (int k = 0; k < nb; k++) { vis[src[b + k]] |= 1ULL << k; fr[src[b + k]] |= 1ULL << k; }
        for (int lev = 0; lev < D; lev++) {
            for (int x = 0; x < nV; x++) { uint64_t a = 0; for (int i = st[x]; i < st[x + 1]; i++) a |= fr[adj[i]]; nx[x] = a & ~vis[x]; }
            for (int x = 0; x < nV; x++) vis[x] |= nx[x];
            uint64_t *t = fr; fr = nx; nx = t;
        }
        for (int x = 0; x < nV; x++) { uint64_t miss = full & ~vis[x]; if (miss) { int c = __builtin_popcountll(miss); bad += c;
            if (nbadrec < 4096 && x < 2 * N * M) { int k = __builtin_ctzll(miss); if (src[b + k] < 2 * N * M) { badS[nbadrec] = src[b + k] / M; badT[nbadrec] = x / M; nbadrec++; } }
            if (perside) for (int k = 0; k < nb; k++) if (miss >> k & 1) { int s = src[b + k]; perside[s >= 2 * N * M ? 2 : (s / M >= N)] ++; } } }
    }
    return bad;
}

static void write_edges(const char *fn) {
    FILE *f = fopen(fn, "w"); fprintf(f, "%d\n", nV); for (int i = 0; i < nE; i++) fprintf(f, "%d %d\n", eu[i], ev[i]); fclose(f);
}
static void write_sol(const char *fn, long c) {
    FILE *f = fopen(fn, "w");
    fprintf(f, "dmhub q %d H %d nfree %d cost %ld\nfree", q, H, nfree, c);
    for (int i = 0; i < nfree; i++) fprintf(f, " %d", freep[i]);
    fprintf(f, "\nsigma"); for (int p = 0; p < N; p++) fprintf(f, " %d", sig[p]);
    fprintf(f, "\nmv0"); for (int p = 0; p < N; p++) fprintf(f, " %d", mv0[p]);
    fprintf(f, "\nmv1"); for (int p = 0; p < N; p++) fprintf(f, " %d", mv1[p]);
    fprintf(f, "\nnu"); for (int i = 0; i < N * Q1; i++) fprintf(f, " %d", hv[i]);
    fprintf(f, "\nhubgraph"); for (int e = 0; e < nhg; e++) fprintf(f, " %d %d", hgA[e], hgB[e]);
    fprintf(f, "\n"); fclose(f);
}

/* coverage cost (theory for collinear freed points, concurrent freed lines): opposite points u of a freed p need
 * a coset-1 walk of length 4 avoiding freed jumps: p-L-x-sigma(x)-u (x ~ p) or p-w-sinv(w)-n-u (n = sigma(u));
 * opposite lines m of a freed line l need l-y-M-sinv(M)-m (M ~ l) or l-y-sigma(y)-z-sigma(z) = m. */
static int *isfreeL, *mark, stamp = 0;
static int **pperp, *npperp, **popp, *npopp, **lperp, *nlperp, **lopp, *nlopp;
static char hubadj[64][64]; static int usehubadj = 0;   /* group adjacency: line-side hubs of i ~ point-side hubs of j */
static int nunc = 0, uncI[1 << 16], uncT[1 << 16];   /* uncovered: freed index i (+nfree for line side), target */
static long cover_cost(void) {
    long tot = 0; nunc = 0;
    for (int i = 0; i < nfree; i++) {
        int p = freep[i]; stamp++;
        for (int a = 0; a < npperp[i]; a++) { int x = pperp[i][a]; if (isfree[x]) continue; int l = sig[x]; for (int k = 0; k < Q1; k++) mark[pts[l * Q1 + k]] = stamp; }
        for (int a = 0; a < Q1; a++) { int w = lof[p * Q1 + a]; if (isfreeL[w]) continue; int z = sinv[w];
            for (int b = 0; b < Q1; b++) { int u = sinv[lof[z * Q1 + b]]; if (!isfree[u]) mark[u] = stamp; } }
        if (usehubadj) for (int j = 0; j < nfree; j++) if (hubadj[i][j]) { int lj = sig[freep[j]]; for (int k = 0; k < Q1; k++) mark[pts[lj * Q1 + k]] = stamp; }
        for (int a = 0; a < npopp[i]; a++) if (mark[popp[i][a]] != stamp) { tot++; if (nunc < (1 << 16)) { uncI[nunc] = i; uncT[nunc++] = popp[i][a]; } }
        int l = sig[p]; stamp++;
        for (int a = 0; a < nlperp[i]; a++) { int M2 = lperp[i][a]; if (isfreeL[M2]) continue; int y = sinv[M2]; for (int k = 0; k < Q1; k++) mark[N + lof[y * Q1 + k]] = stamp; }
        for (int a = 0; a < Q1; a++) { int y = pts[l * Q1 + a]; if (isfree[y]) continue; int ly = sig[y];
            for (int b = 0; b < Q1; b++) { int z = pts[ly * Q1 + b]; if (!isfree[z]) mark[N + sig[z]] = stamp; } }
        if (usehubadj) for (int j = 0; j < nfree; j++) if (hubadj[j][i]) { int pj = freep[j]; for (int k = 0; k < Q1; k++) mark[N + lof[pj * Q1 + k]] = stamp; }
        for (int a = 0; a < nlopp[i]; a++) if (mark[N + lopp[i][a]] != stamp) { tot++; if (nunc < (1 << 16)) { uncI[nunc] = nfree + i; uncT[nunc++] = lopp[i][a]; } }
    }
    return tot;
}

/* exact hub-graph cost (HGDIST=1): nodes 0..K-1 line-side hubs, K..2K-1 point-side hubs; edges: hub-graph edges
 * (weight 1) and lift shortcuts: twins 2, collinear freed points 4 (line side), concurrent freed lines 4 (point side),
 * line-side hub of i to point-side hub of j weight 3 when p_i lies on l_j.  Same-side pairs must be within 4. */
static int hgK; static char (*hgA2)[256]; static char (*hgColl)[64], (*hgConc)[64], (*hgOn)[64], (*hgReq)[64];
static long hg_dist_cost(void) {
    int K = hgK, n = 2 * K; static int adjn[512][256], adjw[512][256], deg2[512], dist[512];
    for (int x = 0; x < n; x++) deg2[x] = 0;
    #define ADDE(u, v, w) do { adjn[u][deg2[u]] = v; adjw[u][deg2[u]++] = w; adjn[v][deg2[v]] = u; adjw[v][deg2[v]++] = w; } while (0)
    for (int a = 0; a < K; a++) for (int b = 0; b < K; b++) {
        if (hgA2[a][b]) ADDE(a, K + b, 1);
        else if (hgOn[a / H][b / H]) ADDE(a, K + b, 3);
    }
    for (int a = 0; a < K; a++) for (int a2 = a + 1; a2 < K; a2++) {
        int i = a / H, j = a2 / H;
        if (i == j) { ADDE(a, a2, 2); ADDE(K + a, K + a2, 2); continue; }
        if (hgColl[i][j]) ADDE(a, a2, 4);
        if (hgConc[i][j]) ADDE(K + a, K + a2, 4);
    }
    long cst = 0;
    for (int s0 = 0; s0 < n; s0++) {
        for (int x = 0; x < n; x++) dist[x] = 99; dist[s0] = 0;
        for (int d = 0; d < 4; d++) for (int x = 0; x < n; x++) if (dist[x] == d)
            for (int e = 0; e < deg2[x]; e++) { int y = adjn[x][e], nd = d + adjw[x][e]; if (nd < dist[y]) dist[y] = nd; }
        int lo = s0 < K ? 0 : K;
        for (int y = lo; y < lo + K; y++) if (y > s0 && dist[y] > 4) cst++;
    }
    for (int i = 0; i < nfree; i++) for (int j = 0; j < nfree; j++) if (hgReq[i][j]) { int ok = 0;
        for (int s1 = 0; s1 < H && !ok; s1++) for (int t1 = 0; t1 < H; t1++) if (hgA2[i * H + s1][j * H + t1]) { ok = 1; break; } cst += 2 * !ok; }
    return cst;
}

static int collinear(int a, int b) { for (int i = 0; i < Q1; i++) for (int j = 0; j < Q1; j++) if (lof[a * Q1 + i] == lof[b * Q1 + j]) return 1; return 0; }

static void setup_flag(int i) {   /* (re)compute the perp / opposite lists of freed flag i */
    int p = freep[i], l = sig[p]; npperp[i] = npopp[i] = nlperp[i] = nlopp[i] = 0;
    for (int x = 0; x < N; x++) if (x != p) { if (collinear(x, p)) pperp[i][npperp[i]++] = x; else popp[i][npopp[i]++] = x; }
    for (int m2 = 0; m2 < N; m2++) if (m2 != l) { int conc = 0; for (int a = 0; a < Q1 && !conc; a++) for (int b = 0; b < Q1; b++) if (pts[l * Q1 + a] == pts[m2 * Q1 + b]) { conc = 1; break; }
        if (conc) lperp[i][nlperp[i]++] = m2; else lopp[i][nlopp[i]++] = m2; }
}
static void update_hg_rel(int i) {  /* refresh the lift shortcuts of flag i in the hub-distance model */
    if (!hgColl) return;
    for (int j = 0; j < nfree; j++) {
        int c = (i != j) && collinear(freep[i], freep[j]); hgColl[i][j] = hgColl[j][i] = c;
        int li = sig[freep[i]], lj = sig[freep[j]], cc2 = 0;
        for (int x = 0; x < Q1 && !cc2; x++) for (int y = 0; y < Q1; y++) if (pts[li * Q1 + x] == pts[lj * Q1 + y]) { cc2 = 1; break; }
        hgConc[i][j] = hgConc[j][i] = (i != j) && cc2;
        hgOn[i][j] = 0; hgOn[j][i] = 0;
        for (int x = 0; x < Q1; x++) { if (pts[sig[freep[j]] * Q1 + x] == freep[i]) hgOn[i][j] = 1; if (pts[sig[freep[i]] * Q1 + x] == freep[j]) hgOn[j][i] = 1; }
    }
}
static int hg_noreq = 0;
static void hub_graph_block(void) {
    /* hub graph: same-side hubs of non-collinear freed points (non-concurrent freed lines) need a common neighbour */
    if (nfree >= 2 && !getenv("NOHUBG")) {
        int K = H * nfree, spare = Q1 + 2 - M;
        static char A2[256][256], needA[256][256], needB[256][256]; memset(A2, 0, sizeof A2);
        long nneed = 0;
        for (int a = 0; a < K; a++) for (int a2 = 0; a2 < K; a2++) {
            int i = a / H, j = a2 / H; needA[a][a2] = needB[a][a2] = 0; if (i == j) continue;
            if (!collinear(freep[i], freep[j])) { needA[a][a2] = 1; nneed++; }
            int li = sig[freep[i]], lj = sig[freep[j]], conc = 0;
            for (int x = 0; x < Q1 && !conc; x++) for (int y = 0; y < Q1; y++) if (pts[li * Q1 + x] == pts[lj * Q1 + y]) { conc = 1; break; }
            if (!conc) { needB[a][a2] = 1; nneed++; }
        }
        int dA[256] = {0}, dB[256] = {0};
        /* pair (a, a2) of line-side hubs is fine if they share a point-side neighbour, or one of them is adjacent to a
           point-side hub of a freed line through the other's freed point (z - (l_j, h) - (p, h') - z', length 4).
           Same for point-side hubs with the roles swapped. on[i][j] = freed point i lies on freed line j. */
        /* coverage holes that a hub edge can patch: point u opposite freed p_i, uncovered, on freed line l_j -> an edge
           between the line-side hubs of i and the point-side hubs of j; line m opposite l_i through freed p_j -> an edge
           between the point-side hubs of i and the line-side hubs of j.  req[i][j] = 1 (line-side i, point-side j). */
        static char req[64][64]; memset(req, 0, sizeof req); long nreq = 0, unpatch = 0;
        if (!hg_noreq) cover_cost(); else nunc = 0;
        for (int r = 0; r < nunc; r++) { int i = uncI[r], t = uncT[r], got = 0;
            if (i < nfree) { for (int j = 0; j < nfree; j++) for (int x = 0; x < Q1; x++) if (pts[sig[freep[j]] * Q1 + x] == t) { if (!req[i][j]) nreq++; req[i][j] = 1; got = 1; } }
            else { i -= nfree; for (int j = 0; j < nfree; j++) for (int x = 0; x < Q1; x++) if (pts[t * Q1 + x] == freep[j]) { if (!req[j][i]) nreq++; req[j][i] = 1; got = 1; } }
            if (!got) unpatch++; }
        printf("coverage holes %d: %ld group edges required, %ld holes not patchable by hub edges\n", nunc, nreq, unpatch);
        static char on[64][64]; for (int i = 0; i < nfree; i++) for (int j = 0; j < nfree; j++) { on[i][j] = 0;
            for (int x = 0; x < Q1; x++) if (pts[sig[freep[j]] * Q1 + x] == freep[i]) on[i][j] = 1; }
        #define HGCOST() ({ long cst = 0; for (int a = 0; a < K; a++) for (int a2 = a + 1; a2 < K; a2++) { \
            if (needA[a][a2]) { int ok = 0; for (int b = 0; b < K && !ok; b++) { if (A2[a][b] && A2[a2][b]) ok = 1; \
                    else if (A2[a][b] && on[a2 / H][b / H]) ok = 1; else if (A2[a2][b] && on[a / H][b / H]) ok = 1; } cst += !ok; } \
            if (needB[a][a2]) { int ok = 0; for (int b = 0; b < K && !ok; b++) { if (A2[b][a] && A2[b][a2]) ok = 1; \
                    else if (A2[b][a] && on[b / H][a2 / H]) ok = 1; else if (A2[b][a2] && on[b / H][a / H]) ok = 1; } cst += !ok; } } \
            for (int i = 0; i < nfree; i++) for (int j = 0; j < nfree; j++) if (req[i][j]) { int ok = 0; \
                for (int s1 = 0; s1 < H && !ok; s1++) for (int t1 = 0; t1 < H; t1++) if (A2[i * H + s1][j * H + t1]) { ok = 1; break; } cst += 2 * !ok; } cst; })
        static char coll2[64][64], conc2[64][64];
        for (int i = 0; i < nfree; i++) for (int j = 0; j < nfree; j++) { coll2[i][j] = i != j && collinear(freep[i], freep[j]); int li = sig[freep[i]], lj = sig[freep[j]], cc2 = 0;
            for (int x = 0; x < Q1 && !cc2; x++) for (int y = 0; y < Q1; y++) if (pts[li * Q1 + x] == pts[lj * Q1 + y]) { cc2 = 1; break; } conc2[i][j] = i != j && cc2; }
        hgK = K; hgA2 = A2; hgColl = coll2; hgConc = conc2; hgOn = on; hgReq = req;
        int hgdist = getenv("HGDIST") ? atoi(getenv("HGDIST")) : 0;
        #define HGC() (hgdist ? hg_dist_cost() : HGCOST())
        long hc = HGC(), hbest = hc; static char Abest[256][256]; memcpy(Abest, A2, sizeof A2);
        if (getenv("HUBG_IN")) {   /* load the hub graph of an earlier dmhub solution instead of annealing one */
            FILE *g = fopen(getenv("HUBG_IN"), "r"); char w[64]; memset(A2, 0, sizeof A2);
            while (g && fscanf(g, "%63s", w) == 1) if (!strcmp(w, "hubgraph")) { int a, b; while (fscanf(g, "%d %d", &a, &b) == 2) A2[a][b] = 1; break; }
            if (g) fclose(g); hc = hbest = HGC(); memcpy(Abest, A2, sizeof A2);
        }
        long hgit = getenv("HUBG_IN") ? 0 : (getenv("HGIT") ? atol(getenv("HGIT")) : 400000);
        for (long it = 0; it < hgit && hc > 0; it++) {
            int a = rnd() % K, b = rnd() % K; double T = 1.0 * pow(0.01, (double)it / hgit);
            if (A2[a][b]) { A2[a][b] = 0; dA[a]--; dB[b]--; }
            else { if (dA[a] >= spare || dB[b] >= spare) { /* swap out a random edge of the full end */
                    int a3 = a, b3 = b; if (dA[a] >= spare) { do b3 = rnd() % K; while (!A2[a][b3]); A2[a][b3] = 0; dA[a]--; dB[b3]--; }
                    if (dB[b] >= spare) { do a3 = rnd() % K; while (!A2[a3][b]); A2[a3][b] = 0; dA[a3]--; dB[b]--; } }
                A2[a][b] = 1; dA[a]++; dB[b]++; }
            long h2 = HGC();
            if (h2 <= hc || urand() < exp(-(h2 - hc) / T)) { hc = h2; if (hc < hbest) { hbest = hc; memcpy(Abest, A2, sizeof A2); } }
            else { memcpy(A2, Abest, sizeof A2); hc = hbest; for (int x = 0; x < K; x++) { dA[x] = dB[x] = 0; } for (int x = 0; x < K; x++) for (int y = 0; y < K; y++) if (A2[x][y]) { dA[x]++; dB[y]++; } }
        }
        memcpy(A2, Abest, sizeof A2);
        if (getenv("HGFILL") && !getenv("HUBG_IN")) {   /* use the remaining spare degree: random extra hub edges (more coverage routes, never longer distances) */
            int da[256] = {0}, db[256] = {0}; for (int a = 0; a < K; a++) for (int b = 0; b < K; b++) if (A2[a][b]) { da[a]++; db[b]++; }
            for (int t = 0; t < 200000; t++) { int a = rnd() % K, b = rnd() % K; if (!A2[a][b] && da[a] < spare && db[b] < spare && a / H != b / H) { A2[a][b] = 1; da[a]++; db[b]++; } }
        }
        for (int a = 0; a < K; a++) for (int b = 0; b < K; b++) if (A2[a][b]) { hgA[nhg] = a; hgB[nhg] = b; nhg++; }
        if (getenv("PRINTHUBADJ")) { printf("HUBADJ"); static char seen[64][64]; memset(seen, 0, sizeof seen);
            for (int e = 0; e < nhg; e++) { int i = hgA[e] / H, j = hgB[e] / H; if (!seen[i][j]) { seen[i][j] = 1; printf(" %d:%d", i, j); } } printf("\n"); }
        printf("hub graph: %ld needed same-side pairs (ordered), uncovered %ld, %d hub-hub edges\n", nneed, hbest, nhg);
    }
}

int main(int argc, char **argv) {
    if (argc < 4) { fprintf(stderr, "usage: dmhub GQBIN SOLIN OUTPREFIX\n"); return 1; }
    if (getenv("SEED")) rs ^= strtoull(getenv("SEED"), 0, 10) * 0x9E3779B97F4A7C15ULL;
    for (int i = 0; i < 10; i++) rnd();
    if (getenv("H")) H = atoi(getenv("H"));
    FILE *f = fopen(argv[1], "rb"); int32_t hd[3]; if (!f || fread(hd, 4, 3, f) != 3) return 1;
    q = hd[0]; N = hd[1]; Q1 = q + 1;
    pts = malloc(sizeof(int) * N * Q1); { int32_t *t = malloc(4L * N * Q1); if (fread(t, 4, (size_t)N * Q1, f) != (size_t)N * Q1) return 1; for (int i = 0; i < N * Q1; i++) pts[i] = t[i]; free(t); }
    fclose(f);
    lof = malloc(sizeof(int) * N * Q1); { int *dg = calloc(N, sizeof(int)); for (int l = 0; l < N; l++) for (int k = 0; k < Q1; k++) { int p = pts[l * Q1 + k]; lof[p * Q1 + dg[p]++] = l; } free(dg); }
    /* solution (lift2 format: header, group line, sigma x J, mv x J, flag voltages) */
    f = fopen(argv[2], "r"); int qq, J, m, DD, cc; char g1[64]; int g2;
    if (fscanf(f, "%d %d %d %d %d %63s %d", &qq, &J, &m, &DD, &cc, g1, &g2) != 7 || J != 2 || m != 6) { fprintf(stderr, "bad sol\n"); return 1; }
    sig = malloc(sizeof(int) * N); sinv = malloc(sizeof(int) * N); mv0 = malloc(sizeof(int) * N); mv1 = malloc(sizeof(int) * N); hv = malloc(sizeof(int) * N * Q1);
    int *s2 = malloc(sizeof(int) * N);
    for (int p = 0; p < N; p++) if (fscanf(f, "%d", &sig[p]) != 1) return 1;
    for (int p = 0; p < N; p++) if (fscanf(f, "%d", &s2[p]) != 1 || s2[p] != sig[p]) { fprintf(stderr, "matchings differ\n"); return 1; }
    for (int p = 0; p < N; p++) if (fscanf(f, "%d", &mv0[p]) != 1) return 1;
    for (int p = 0; p < N; p++) if (fscanf(f, "%d", &mv1[p]) != 1) return 1;
    for (int i = 0; i < N * Q1; i++) if (fscanf(f, "%d", &hv[i]) != 1) return 1;
    fclose(f);
    for (int p = 0; p < N; p++) sinv[sig[p]] = p;
    /* freed points */
    nfree = 0;
    if (getenv("FREE")) { char *s = getenv("FREE"), *e; for (;;) { long x = strtol(s, &e, 10); if (e == s) break; freep[nfree++] = (int)x; s = e; } }
    else if (getenv("NFREE")) { int k = atoi(getenv("NFREE")); int l = rnd() % N; for (int i = 0; i < k && i < Q1; i++) freep[nfree++] = pts[l * Q1 + i]; }
    for (int i = 0; i < nfree; i++) isfree[freep[i]] = 1;
    if (getenv("FORCE")) {  /* "p:l p:l ...": set sigma(p) = l by a swap (to make p a flag with its own line) */
        char *s = getenv("FORCE"), *e;
        for (;;) { long p = strtol(s, &e, 10); if (e == s || *e != ':') break; s = e + 1; long l = strtol(s, &e, 10); s = e;
            int o = sinv[l], t = sig[p]; sig[p] = l; sig[o] = t; sinv[l] = p; sinv[t] = o; }
    }
    if (getenv("X0")) {     /* freed lines = lines through point X0 (pairwise concurrent): sigma(p_i) = i-th line on X0 */
        int x0 = atoi(getenv("X0"));
        for (int i = 0; i < nfree; i++) { int l = lof[x0 * Q1 + i], p = freep[i], o = sinv[l]; int t = sig[p]; sig[p] = l; sig[o] = t; sinv[l] = p; sinv[t] = o; }
    }
    /* focus set: points collinear with a freed point, and preimages of lines concurrent with a freed line */
    int *focus = malloc(sizeof(int) * N), nfoc = 0; char *inf = calloc(N, 1);
    for (int i = 0; i < nfree; i++) for (int x = 0; x < N; x++) if (!isfree[x] && !inf[x] && collinear(x, freep[i])) { inf[x] = 1; focus[nfoc++] = x; }
    /* line-side focus: lines concurrent with a freed line (re-read through sinv at move time) */
    int *lfoc = malloc(sizeof(int) * N), nlf = 0; char *inl = calloc(N, 1);
    for (int i = 0; i < nfree; i++) { int l = sig[freep[i]];
        for (int k = 0; k < Q1; k++) { int y = pts[l * Q1 + k]; for (int j = 0; j < Q1; j++) { int m2 = lof[y * Q1 + j]; if (m2 != l && !inl[m2]) { inl[m2] = 1; lfoc[nlf++] = m2; } } } }
    int maxE = N * Q1 * M + 2 * N * M + 2 * H * M * nfree + 16, maxV = 2 * N * M + 2 * H * nfree + 16;
    eu = malloc(sizeof(int) * maxE); ev = malloc(sizeof(int) * maxE); st = malloc(sizeof(int) * (maxV + 1)); adj = malloc(sizeof(int) * 2 * maxE); deg = malloc(sizeof(int) * maxV);
    vis = malloc(8L * maxV); fr = malloc(8L * maxV); nx = malloc(8L * maxV);
    isfreeL = calloc(N, sizeof(int)); mark = calloc(2 * N, sizeof(int));
    for (int i = 0; i < nfree; i++) isfreeL[sig[freep[i]]] = 1;
    pperp = malloc(sizeof(int *) * nfree); popp = malloc(sizeof(int *) * nfree); lperp = malloc(sizeof(int *) * nfree); lopp = malloc(sizeof(int *) * nfree);
    npperp = calloc(nfree, sizeof(int)); npopp = calloc(nfree, sizeof(int)); nlperp = calloc(nfree, sizeof(int)); nlopp = calloc(nfree, sizeof(int));
    for (int i = 0; i < nfree; i++) {
        int p = freep[i], l = sig[p]; pperp[i] = malloc(sizeof(int) * N); popp[i] = malloc(sizeof(int) * N); lperp[i] = malloc(sizeof(int) * N); lopp[i] = malloc(sizeof(int) * N);
        for (int x = 0; x < N; x++) if (x != p) { if (collinear(x, p)) pperp[i][npperp[i]++] = x; else popp[i][npopp[i]++] = x; }
        for (int m2 = 0; m2 < N; m2++) if (m2 != l) { int conc = 0; for (int a = 0; a < Q1 && !conc; a++) for (int b = 0; b < Q1; b++) if (pts[l * Q1 + a] == pts[m2 * Q1 + b]) { conc = 1; break; }
            if (conc) lperp[i][nlperp[i]++] = m2; else lopp[i][nlopp[i]++] = m2; }
    }
    if (getenv("HGFIRST")) { hg_noreq = 1; hub_graph_block(); usehubadj = 1; for (int e = 0; e < nhg; e++) hubadj[hgA[e] / H][hgB[e] / H] = 1; }
    long covit = getenv("COVIT") ? atol(getenv("COVIT")) : 0;
    double cT0 = getenv("CT0") ? atof(getenv("CT0")) : 0.5;
    if (covit) {
        /* joint mode (HGFIRST): cost = coverage (with hub routes) + HW * hub-distance cost; hub edges are rewired too */
        double phub = (usehubadj && getenv("PHUB")) ? atof(getenv("PHUB")) : 0.0; long HW = getenv("HW") ? atol(getenv("HW")) : 2;
        long hd = usehubadj ? hg_dist_cost() : 0;
        long cc = cover_cost() + HW * hd; printf("cover cost initial %ld (hub-distance part %ld)\n", cc, hd);
        int *bsig = malloc(sizeof(int) * N); long bcc = cc; memcpy(bsig, sig, sizeof(int) * N);
        static char bA2[256][256], sA2[256][256]; if (usehubadj) memcpy(bA2, hgA2, sizeof bA2);
        int Kh = hgK, spareh = Q1 + 2 - M;
        double pflag = getenv("PFLAG") ? atof(getenv("PFLAG")) : 0.0; long nflagacc = 0; int bfree[64]; memcpy(bfree, freep, sizeof(int) * nfree);
        double csecs = getenv("CSECS") ? atof(getenv("CSECS")) : 0; struct timespec ct0, ct1; clock_gettime(CLOCK_MONOTONIC, &ct0); double frac = 0;
        for (long it = 0; it < covit && cc > 0; it++) {
            if (csecs > 0) { if ((it & 4095) == 0) { clock_gettime(CLOCK_MONOTONIC, &ct1); frac = ((ct1.tv_sec - ct0.tv_sec) + 1e-9 * (ct1.tv_nsec - ct0.tv_nsec)) / csecs; } if (frac >= 1) break; }
            else frac = (double)it / covit;
            double T = cT0 * pow(0.02 / cT0, frac);
            int x, y;
            if (phub > 0 && urand() < phub) {   /* hub-graph move: toggle an edge, targeted at an uncovered target's patch */
                int a, b;
                if (nunc && urand() < 0.7) { int r = rnd() % nunc, i = uncI[r], t = uncT[r], js[64], nj = 0;
                    if (i < nfree) { for (int j = 0; j < nfree; j++) for (int k = 0; k < Q1; k++) if (pts[sig[freep[j]] * Q1 + k] == t) js[nj++] = j;
                        if (!nj) continue; int j = js[rnd() % nj]; a = i * H + rnd() % H; b = j * H + rnd() % H; }
                    else { i -= nfree; for (int j = 0; j < nfree; j++) for (int k = 0; k < Q1; k++) if (pts[t * Q1 + k] == freep[j]) js[nj++] = j;
                        if (!nj) continue; int j = js[rnd() % nj]; a = j * H + rnd() % H; b = i * H + rnd() % H; }
                    if (hgA2[a][b]) continue;
                } else { a = rnd() % Kh; b = rnd() % Kh; }
                memcpy(sA2, hgA2, sizeof sA2);
                if (hgA2[a][b]) hgA2[a][b] = 0;
                else { int da = 0, db = 0; for (int z = 0; z < Kh; z++) { da += hgA2[a][z]; db += hgA2[z][b]; }
                    if (da >= spareh) { int z; do z = rnd() % Kh; while (!hgA2[a][z]); hgA2[a][z] = 0; }
                    if (db >= spareh) { int z; do z = rnd() % Kh; while (!hgA2[z][b]); hgA2[z][b] = 0; }
                    hgA2[a][b] = 1; }
                memset(hubadj, 0, sizeof hubadj); for (int u = 0; u < Kh; u++) for (int v = 0; v < Kh; v++) if (hgA2[u][v]) hubadj[u / H][v / H] = 1;
                long hd2 = hg_dist_cost(), c2 = cover_cost() + HW * hd2;
                if (c2 <= cc || urand() < exp(-(c2 - cc) / T)) { cc = c2; hd = hd2; }
                else { memcpy(hgA2, sA2, sizeof sA2); memset(hubadj, 0, sizeof hubadj); for (int u = 0; u < Kh; u++) for (int v = 0; v < Kh; v++) if (hgA2[u][v]) hubadj[u / H][v / H] = 1; cover_cost(); }
                if (cc < bcc) { bcc = cc; memcpy(bsig, sig, sizeof(int) * N); memcpy(bA2, hgA2, sizeof bA2); memcpy(bfree, freep, sizeof(int) * nfree); }
                continue;
            }
            if (pflag > 0 && urand() < pflag) {   /* flag move: replace freed flag i by a random new flag (p2 on l2) */
                int i = rnd() % nfree, p = freep[i], l = sig[p], p2 = rnd() % N, l2 = lof[p2 * Q1 + rnd() % Q1];
                if (isfree[p2] || isfreeL[l2]) continue;
                int o = sinv[l2], t2 = sig[p2];
                isfree[p] = 0; isfreeL[l] = 0;
                sig[p2] = l2; sig[o] = t2; sinv[l2] = p2; sinv[t2] = o;
                freep[i] = p2; isfree[p2] = 1; isfreeL[l2] = 1; setup_flag(i); update_hg_rel(i);
                long hd2 = usehubadj ? hg_dist_cost() : 0, c2 = cover_cost() + HW * hd2;
                if (c2 <= cc || urand() < exp(-(c2 - cc) / T)) { cc = c2; hd = hd2; nflagacc++; }
                else { isfree[p2] = 0; isfreeL[l2] = 0; sig[o] = l2; sig[p2] = t2; sinv[l2] = o; sinv[t2] = p2;
                    freep[i] = p; isfree[p] = 1; isfreeL[l] = 1; setup_flag(i); update_hg_rel(i); cover_cost(); }
                if (cc < bcc) { bcc = cc; memcpy(bsig, sig, sizeof(int) * N); if (usehubadj) memcpy(bA2, hgA2, sizeof bA2); memcpy(bfree, freep, sizeof(int) * nfree); }
                continue;
            }
            if (nunc && urand() < 0.7) {   /* repair one uncovered target */
                int r = rnd() % nunc, i = uncI[r], t = uncT[r];
                if (i < nfree) {   /* point t opposite freed p_i: sigma(x) := a line through t, x ~ p_i */
                    do { x = pperp[i][rnd() % npperp[i]]; } while (isfree[x]);
                    y = sinv[lof[t * Q1 + rnd() % Q1]];
                } else {           /* line t opposite freed line: sinv(M) := a point on t, M ~ freed line */
                    i -= nfree; int M2; do { M2 = lperp[i][rnd() % nlperp[i]]; } while (isfreeL[M2]);
                    x = sinv[M2]; y = pts[t * Q1 + rnd() % Q1];
                }
                if (isfree[x] || isfree[y] || x == y) continue;
            } else {
                do { int i = rnd() % nfree; x = (rnd() & 1) ? pperp[i][rnd() % npperp[i]] : sinv[lperp[i][rnd() % nlperp[i]]]; } while (isfree[x]);
                do { y = rnd() % N; } while (y == x || isfree[y]);
            }
            int t = sig[x]; sig[x] = sig[y]; sig[y] = t; sinv[sig[x]] = x; sinv[sig[y]] = y;
            long c2 = cover_cost() + HW * hd;
            if (c2 <= cc || urand() < exp(-(c2 - cc) / T)) cc = c2;
            else { t = sig[x]; sig[x] = sig[y]; sig[y] = t; sinv[sig[x]] = x; sinv[sig[y]] = y; cover_cost(); }
            if (cc < bcc) { bcc = cc; memcpy(bsig, sig, sizeof(int) * N); if (usehubadj) memcpy(bA2, hgA2, sizeof bA2); memcpy(bfree, freep, sizeof(int) * nfree); }
            if (it % 100000 == 0) { printf("cover it %ld T %.3f cost %ld\n", it, T, cc); fflush(stdout); }
        }
        memcpy(sig, bsig, sizeof(int) * N); for (int p = 0; p < N; p++) sinv[sig[p]] = p;
        if (pflag > 0) { for (int i = 0; i < nfree; i++) { isfree[freep[i]] = 0; isfreeL[sig[freep[i]]] = 0; }   /* sig[] is already the best one */
            memcpy(freep, bfree, sizeof(int) * nfree); memset(isfreeL, 0, sizeof(int) * N); for (int x = 0; x < N; x++) isfree[x] = 0;
            for (int i = 0; i < nfree; i++) { isfree[freep[i]] = 1; isfreeL[sig[freep[i]]] = 1; } for (int i = 0; i < nfree; i++) { setup_flag(i); update_hg_rel(i); }
            printf("flag moves accepted %ld; flags now:", nflagacc); for (int i = 0; i < nfree; i++) printf(" %d:%d", freep[i], sig[freep[i]]); printf("\n"); }
        if (usehubadj) { memcpy(hgA2, bA2, sizeof bA2); memset(hubadj, 0, sizeof hubadj); nhg = 0;
            for (int u = 0; u < Kh; u++) for (int v = 0; v < Kh; v++) if (hgA2[u][v]) { hubadj[u / H][v / H] = 1; hgA[nhg] = u; hgB[nhg] = v; nhg++; }
            hd = hg_dist_cost(); printf("hub graph after joint annealing: %d edges, distance cost %ld\n", nhg, hd); }
        cc = cover_cost();
        printf("cover cost final %ld\n", cc);
        if (cc > 0 && getenv("REPAIR")) {   /* beam search over sequences of targeted sigma swaps (hub graph fixed) */
            int B = getenv("BEAM") ? atoi(getenv("BEAM")) : 60, depth = getenv("RDEPTH") ? atoi(getenv("RDEPTH")) : 3;
            int (*beam)[512] = malloc(sizeof(int[512]) * B * 2 + 16), (*nb)[512] = malloc(sizeof(int[512]) * B * 2 + 16);
            long *bc = malloc(sizeof(long) * (B + 1)), *nbc = malloc(sizeof(long) * (B * 2 + 16)); int nbeam = 1, nnb;
            memcpy(beam[0], sig, sizeof(int) * N); bc[0] = cc; long bestc = cc; int found = 0;
            /* visited states (64-bit hashes of sigma, open addressing) so the beam does not undo its own swaps */
            size_t HS = 1 << 22; uint64_t *vis2 = calloc(HS, 8);
            #define SIGHASH() ({ uint64_t h_ = 1469598103934665603ULL; for (int p_ = 0; p_ < N; p_++) { h_ ^= (uint64_t)sig[p_] + 0x9E3779B97F4A7C15ULL * (p_ + 1); h_ *= 1099511628211ULL; } h_ | 1; })
            #define VISIT(h) ({ size_t i_ = (h) & (HS - 1); int new_ = 1; while (vis2[i_]) { if (vis2[i_] == (h)) { new_ = 0; break; } i_ = (i_ + 1) & (HS - 1); } if (new_) vis2[i_] = (h); new_; })
            { uint64_t h0 = SIGHASH(); VISIT(h0); }
            for (int d = 0; d < depth && !found; d++) {
                nnb = 0;
                for (int s0 = 0; s0 < nbeam && !found; s0++) {
                    memcpy(sig, beam[s0], sizeof(int) * N); for (int p = 0; p < N; p++) sinv[sig[p]] = p;
                    cover_cost(); int nu0 = nunc, ui[64], ut[64]; for (int r = 0; r < nu0 && r < 64; r++) { ui[r] = uncI[r]; ut[r] = uncT[r]; }
                    for (int r = 0; r < nu0 && r < 64 && !found; r++) {
                        int i = ui[r], t = ut[r];
                        int xs[64], nx = 0, ys[64], ny = 0;
                        if (i < nfree) { for (int a = 0; a < npperp[i]; a++) if (!isfree[pperp[i][a]]) xs[nx++] = pperp[i][a]; for (int k = 0; k < Q1; k++) ys[ny++] = sinv[lof[t * Q1 + k]]; }
                        else { int ii = i - nfree; for (int a = 0; a < nlperp[ii] && nx < 64; a++) if (!isfreeL[lperp[ii][a]]) xs[nx++] = sinv[lperp[ii][a]]; for (int k = 0; k < Q1; k++) ys[ny++] = pts[t * Q1 + k]; }
                        for (int a = 0; a < nx && !found; a++) for (int b = 0; b < ny && !found; b++) {
                            int x = xs[a], y = ys[b]; if (x == y || isfree[x] || isfree[y]) continue;
                            int tt = sig[x]; sig[x] = sig[y]; sig[y] = tt; sinv[sig[x]] = x; sinv[sig[y]] = y;
                            uint64_t hh = SIGHASH();
                            if (!VISIT(hh)) { tt = sig[x]; sig[x] = sig[y]; sig[y] = tt; sinv[sig[x]] = x; sinv[sig[y]] = y; continue; }
                            long c2 = cover_cost();
                            if (c2 == 0) { found = 1; break; }
                            /* keep the B best children */
                            if (nnb < 2 * B) { memcpy(nb[nnb], sig, sizeof(int) * N); nbc[nnb++] = c2; }
                            else { int w = 0; for (int z = 1; z < nnb; z++) if (nbc[z] > nbc[w]) w = z; if (c2 < nbc[w] || (c2 == nbc[w] && (rnd() & 1))) { memcpy(nb[w], sig, sizeof(int) * N); nbc[w] = c2; } }
                            tt = sig[x]; sig[x] = sig[y]; sig[y] = tt; sinv[sig[x]] = x; sinv[sig[y]] = y;
                        }
                    }
                }
                if (found) break;
                /* select B best children as the next beam */
                for (int a = 0; a < nnb; a++) for (int b = a + 1; b < nnb; b++) if (nbc[b] < nbc[a]) { long tc = nbc[a]; nbc[a] = nbc[b]; nbc[b] = tc; int tmp[512]; memcpy(tmp, nb[a], sizeof(int) * N); memcpy(nb[a], nb[b], sizeof(int) * N); memcpy(nb[b], tmp, sizeof(int) * N); }
                nbeam = nnb < B ? nnb : B; for (int a = 0; a < nbeam; a++) { memcpy(beam[a], nb[a], sizeof(int) * N); bc[a] = nbc[a]; }
                if (nbeam && bc[0] < bestc) bestc = bc[0];
                printf("repair depth %d: beam %d, best child cost %ld\n", d + 1, nbeam, nbeam ? bc[0] : -1); fflush(stdout);
            }
            if (found) { for (int p = 0; p < N; p++) sinv[sig[p]] = p; cc = cover_cost(); printf("repair: cover cost %ld\n", cc); }
            else { memcpy(sig, bsig, sizeof(int) * N); for (int p = 0; p < N; p++) sinv[sig[p]] = p; cc = cover_cost(); printf("repair failed, best %ld\n", bestc); }
        }
        if (getenv("SHOWUNC")) for (int r = 0; r < nunc && r < 60; r++) printf("UNC %s freed#%d target %d\n", uncI[r] < nfree ? "pt" : "ln", uncI[r] % nfree, uncT[r]);
    }
    if (!getenv("HGFIRST")) hub_graph_block();
    build(); long per[3]; long c = cost_eval(per);
    printf("q %d N %d freed %d hubs/side %d -> n %d; initial cost %ld (point src %ld, line src %ld, hub src %ld); focus %d\n", q, N, nfree, H, nV, c, per[0], per[1], per[2], nfoc);
    fflush(stdout);
    long iters = getenv("ITERS") ? atol(getenv("ITERS")) : 2000; double secs = getenv("SECS") ? atof(getenv("SECS")) : 1e9;
    double T0 = getenv("T0") ? atof(getenv("T0")) : 2.0, T1 = getenv("T1") ? atof(getenv("T1")) : 0.05;
    double pfoc = getenv("FOCUS") ? atof(getenv("FOCUS")) : 0.8, pnu = getenv("PNU") ? atof(getenv("PNU")) : 0.3;
    int pfree = getenv("PFREE") ? atoi(getenv("PFREE")) : 0;
    double ptarg = getenv("PTARG") ? atof(getenv("PTARG")) : 0.8;
    long best = c; char fn[512];
    time_t t0 = time(0);
    for (long it = 0; it < iters && c > 0; it++) {
        if (difftime(time(0), t0) > secs) break;
        double T = T0 * pow(T1 / T0, (double)it / iters);
        if (urand() < pnu) {
            int fl = rnd() % (N * Q1);
            if (nbadrec && urand() < ptarg) {   /* a flag on a geodesic of a recorded bad pair (same colour, distance 4) */
                int r = rnd() % nbadrec, a = badS[r], b2 = badT[r];
                if (a < N && b2 < N) {          /* points: a - L - x - M - b2 with x collinear to both */
                    int cand[64], nc = 0;
                    for (int i = 0; i < Q1; i++) { int L = lof[a * Q1 + i]; for (int k = 0; k < Q1; k++) { int x = pts[L * Q1 + k]; if (x == a) continue;
                        for (int j = 0; j < Q1; j++) { int M2 = lof[x * Q1 + j]; if (M2 == L) continue; for (int t2 = 0; t2 < Q1; t2++) if (pts[M2 * Q1 + t2] == b2) {
                            int fA = -1, fB = -1, fC = -1, fD = -1;
                            for (int z = 0; z < Q1; z++) { if (pts[L * Q1 + z] == a) fA = L * Q1 + z; if (pts[L * Q1 + z] == x) fB = L * Q1 + z; if (pts[M2 * Q1 + z] == x) fC = M2 * Q1 + z; if (pts[M2 * Q1 + z] == b2) fD = M2 * Q1 + z; }
                            if (nc < 60) { cand[nc++] = fA; cand[nc++] = fB; cand[nc++] = fC; cand[nc++] = fD; } } } } }
                    if (nc) fl = cand[rnd() % nc];
                } else if (a >= N && b2 >= N) {  /* lines: a - y - X - z - b2 with X concurrent with both */
                    int la = a - N, lb = b2 - N, cand[64], nc = 0;
                    for (int i = 0; i < Q1; i++) { int y = pts[la * Q1 + i]; for (int j = 0; j < Q1; j++) { int X = lof[y * Q1 + j]; if (X == la) continue;
                        for (int k = 0; k < Q1; k++) { int z = pts[X * Q1 + k]; if (z == y) continue; for (int t2 = 0; t2 < Q1; t2++) if (lof[z * Q1 + t2] == lb) {
                            int fA = la * Q1 + i, fB = -1, fC = -1, fD = -1;
                            for (int w = 0; w < Q1; w++) { if (pts[X * Q1 + w] == y) fB = X * Q1 + w; if (pts[X * Q1 + w] == z) fC = X * Q1 + w; if (pts[lb * Q1 + w] == z) fD = lb * Q1 + w; }
                            if (nc < 60) { cand[nc++] = fA; cand[nc++] = fB; cand[nc++] = fC; cand[nc++] = fD; } } } } }
                    if (nc) fl = cand[rnd() % nc];
                }
            } hv[fl] = 3 - hv[fl]; build(); long c2 = cost_eval(NULL);
            if (c2 <= c || urand() < exp(-(c2 - c) / T)) c = c2; else hv[fl] = 3 - hv[fl];
        } else {
            int x, y;
            do { double r = urand();
                 if (r < pfoc / 2 && nfoc) x = focus[rnd() % nfoc];
                 else if (r < pfoc && nlf) x = sinv[lfoc[rnd() % nlf]];
                 else x = (int)(rnd() % N); } while (isfree[x] && !pfree);
            do { y = rnd() % N; } while (y == x || (isfree[y] && !pfree));
            int t = sig[x]; sig[x] = sig[y]; sig[y] = t; sinv[sig[x]] = x; sinv[sig[y]] = y;
            build(); long c2 = cost_eval(NULL);
            if (c2 <= c || urand() < exp(-(c2 - c) / T)) c = c2;
            else { t = sig[x]; sig[x] = sig[y]; sig[y] = t; sinv[sig[x]] = x; sinv[sig[y]] = y; }
        }
        if (c < best) { best = c; }
        if (it % 200 == 0) { printf("it %ld T %.3f cost %ld best %ld\n", it, T, c, best); fflush(stdout); }
    }
    build(); c = cost_eval(per);
    printf("cover cost %ld\n", cover_cost());
    if (getenv("DIAG")) {   /* list bad pairs: source base vertex, target base vertex, sheet, base distance class */
        int *dist = malloc(sizeof(int) * nV), *qq2 = malloc(sizeof(int) * nV); int shown = 0;
        for (int v = 0; v < 2 * N; v++) {
            for (int x = 0; x < nV; x++) dist[x] = -1; int hh = 0, tt = 0; dist[v * M] = 0; qq2[tt++] = v * M;
            while (hh < tt) { int x = qq2[hh++]; for (int i = st[x]; i < st[x + 1]; i++) { int y = adj[i]; if (dist[y] < 0) { dist[y] = dist[x] + 1; qq2[tt++] = y; } } }
            for (int x = 0; x < 2 * N * M; x++) if (dist[x] > D || dist[x] < 0) { int u = x / M, g = x % M;
                int fv = v < N ? isfree[v] : isfreeL[v - N], fu = u < N ? isfree[u] : isfreeL[u - N];
                int coll = (v < N && u < N) ? collinear(v, u) : -1;
                if (shown++ < 400) printf("BAD src %d%s -> tgt %d%s sheet %d dist %d coll %d\n", v, fv ? "*" : "", u, fu ? "*" : "", g, dist[x], coll); }
        }
    }
    printf("final cost %ld (point src %ld, line src %ld, hub src %ld) n %d\n", c, per[0], per[1], per[2], nV);
    snprintf(fn, sizeof fn, "%s.sol", argv[3]); write_sol(fn, c);
    snprintf(fn, sizeof fn, "%s.edges", argv[3]); write_edges(fn);
    return 0;
}
