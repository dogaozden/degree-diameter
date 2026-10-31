/* sdtabu2.c: sdtabu.c with a faster energy (same values) and TYPES as a list.  X = S^-1 S is inverse-closed, so
 * X X = {x y^-1} = {e} u {x y^-1, y x^-1 : x <> y}: only unordered pairs are multiplied (half the table lookups).
 * TYPES: comma list of f values, "x" for the EXT (non-split) records, e.g. TYPES=2,4,6,x.  ENERGYTEST=N compares
 * the two energies on N random sets and exits.  NOID=1 skips the beta = identity record in "all" mode.
 * ENDG=t (default 0 = off): at a state with energy <= t (at most once every SCANGAP = 25 steps) scan the whole
 * single-replacement neighbourhood and take its best move if that beats the current energy.
 * FAST=1 (default): candidates are drawn first (same random sequence) and evaluated grouped by the replaced item: the
 * coverage of X_keep X_keep (X_keep = S'^-1 S', S' = S without that item) is computed once per item and per step, and
 * a candidate only multiplies its new X entries (by X_keep and among themselves).  Same energies, same run as FAST=0.
 * FASTCHECK=1 compares every fast energy with the plain one.
 * Based on sdtabu.c: tabu search inside the self-dual (bipartite Cayley) family of sdk.c, for types too large to enumerate.
 * Same input as sdk (export_sd.g).  For a record r and type (f, m) the set is
 *   ALPHA: S = e + (f-1) psi-fixed elements + m psi-2-orbits;   EXT: S = {e, c^-1} + (m-1) further 2-orbits,
 * psi(x) = c^-1 beta(x)^-1.  Energy |G \ X X| (X = S^-1 S), which is 0 iff the Haar graph has diameter <= 5 (the
 * graph is a Cayley graph); every energy-0 set also gets the full three-condition check before it is reported.
 * Move: replace one chosen fixed element or one chosen orbit by an unused one; NB random candidate moves per step,
 * best non-tabu one taken (a move that beats the best energy so far is always allowed); removed items are tabu for
 * TEN steps; restart from a random set after STALL steps without improvement.
 * usage: sdtabu2 FILE.ht REC F M      or      sdtabu FILE.ht all   (every record and every type of valency K, SECS each)
 * env: K (default 6), SECS (per type, default 20), SEED, NB (default 48), TEN (default 12), STALL (default 300),
 *      MAXSOL (stop a type after this many solutions, default 5), EDGES (edge list of the first solution),
 *      DEEP=thr,secs (give a type secs more seconds if its best energy after SECS is <= thr), TYPES (as in sdk).
 * output: "SOL tag s_0 .. s_K-1", one "TABU rec .. f .. m .. best .. sols .. steps .. secs" line per type, "DONE".
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <stdint.h>

static int n, ninv, K = 6;
static uint16_t *mul; static int *inv;
#define MAXREC 4096
static int nrec, rkind[MAXREC], rp[MAXREC], rc[MAXREC], *rbeta[MAXREC];
static uint32_t *stA, *mk, *bst, *mkK; static uint32_t sA = 0, sM = 0;
static const char *edges_out; static int nsol = 0;
#define M(a,b) mul[(size_t)(a) * n + (b)]

static int rdint(FILE *f) { int x; if (fscanf(f, "%d", &x) != 1) { fprintf(stderr, "read error\n"); exit(1); } return x; }
static void load(const char *path) {
    FILE *f = fopen(path, "r"); if (!f) { perror(path); exit(1); }
    n = rdint(f); ninv = rdint(f);
    mul = malloc(sizeof(uint16_t) * n * n); inv = malloc(sizeof(int) * n);
    for (int i = 0; i < n * n; i++) mul[i] = rdint(f);
    for (int i = 0; i < n; i++) inv[i] = rdint(f);
    char w[32];
    while (fscanf(f, "%31s", w) == 1 && nrec < MAXREC) {
        if (!strcmp(w, "ALPHA")) { rkind[nrec] = 0; rp[nrec] = rdint(f); rc[nrec] = 0; }
        else if (!strcmp(w, "EXT")) { rkind[nrec] = 1; rp[nrec] = 0; rc[nrec] = rdint(f); }
        else { fprintf(stderr, "format: %s\n", w); exit(1); }
        rbeta[nrec] = malloc(sizeof(int) * n); for (int i = 0; i < n; i++) rbeta[nrec][i] = rdint(f);
        if (fscanf(f, "%31s", w) != 1 || strcmp(w, "CENT")) { fprintf(stderr, "format\n"); exit(1); }
        int k = rdint(f); for (int j = 0; j < k * n; j++) rdint(f);
        nrec++;
    }
    fclose(f);
    stA = calloc(n, sizeof(uint32_t)); mk = calloc(n, sizeof(uint32_t)); bst = calloc(n, sizeof(uint32_t)); mkK = calloc(n, sizeof(uint32_t));
}
static int pp_uncov(const int *S, int k, int left) {
    int X[256], nx = 0; sM++;
    for (int i = 0; i < k; i++) for (int j = 0; j < k; j++) {
        int x = left ? M(inv[S[i]], S[j]) : M(S[i], inv[S[j]]);
        if (mk[x] != sM) { mk[x] = sM; X[nx++] = x; } }
    sA++; int cov = 0;
    for (int i = 0; i < nx; i++) { const uint16_t *row = mul + (size_t)X[i] * n;
        for (int j = 0; j < nx; j++) { int z = row[X[j]]; if (stA[z] != sA) { stA[z] = sA; cov++; } } }
    return n - cov;
}
static int XI[256];
static int pp_uncov2(const int *S, int k) {     /* = pp_uncov(S, k, 1) */
    int X[256], nx = 0; sM++;
    for (int i = 0; i < k; i++) for (int j = 0; j < k; j++) {
        int x = M(inv[S[i]], S[j]);
        if (mk[x] != sM) { mk[x] = sM; X[nx++] = x; } }
    for (int t = 0; t < nx; t++) XI[t] = inv[X[t]];
    sA++; int cov = 1; stA[0] = sA;
    for (int i = 0; i < nx; i++) { const uint16_t *row = mul + (size_t)X[i] * n;
        for (int t = i + 1; t < nx; t++) { int z = row[XI[t]];
            if (stA[z] != sA) { stA[z] = sA; cov++; int zi = inv[z]; if (stA[zi] != sA) { stA[zi] = sA; cov++; } } } }
    return n - cov;
}
static int fullcheck(const int *S, int k) {
    for (int i = 0; i < k; i++) for (int j = i + 1; j < k; j++) if (S[i] == S[j]) return 0;
    if (pp_uncov(S, k, 1) || pp_uncov(S, k, 0)) return 0;
    int Y[256], ny = 0; sM++;
    for (int i = 0; i < k; i++) for (int j = 0; j < k; j++) { int x = M(S[i], inv[S[j]]); if (mk[x] != sM) { mk[x] = sM; Y[ny++] = x; } }
    char *yy = calloc(n, 1), *odd = calloc(n, 1);
    for (int i = 0; i < ny; i++) for (int j = 0; j < ny; j++) yy[M(Y[i], Y[j])] = 1;
    for (int z = 0; z < n; z++) if (yy[z]) for (int i = 0; i < k; i++) odd[M(z, S[i])] = 1;
    int ok = 1; for (int z = 0; z < n; z++) if (!odd[z]) ok = 0;
    free(yy); free(odd); return ok;
}
static uint64_t rs = 88172645463325252ULL;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }

static int *psi, *fl, nfl, (*ol)[2], nol, *orbof;
static void setup(int r) {
    int *be = rbeta[r], c = rc[r];
    for (int i = 0; i < n; i++) psi[i] = M(inv[c], inv[be[i]]);
    for (int i = 0; i < n; i++) if (psi[psi[i]] != i) { fprintf(stderr, "record %d: psi is not an involution\n", r); exit(1); }
    nfl = nol = 0;
    for (int i = 0; i < n; i++) {
        if (psi[i] == i) { orbof[i] = -1; if (i != 0) fl[nfl++] = i; }
        else if (i < psi[i]) { ol[nol][0] = i; ol[nol][1] = psi[i]; orbof[i] = orbof[psi[i]] = nol; nol++; }
    }
}

/* items: fixed elements are 0..nfl-1, orbits are nfl..nfl+nol-1 */
static int nf_, nm_, it[32], nit, fixed0, S[32];
static long long *tabu_until, step;
static int build(void) {
    int at = 0;
    if (fixed0 >= 0) { S[at++] = ol[fixed0][0]; S[at++] = ol[fixed0][1]; } else S[at++] = 0;
    for (int i = 0; i < nit; i++) { int x = it[i];
        if (x < nfl) S[at++] = fl[x]; else { S[at++] = ol[x - nfl][0]; S[at++] = ol[x - nfl][1]; } }
    return at;
}
static int used(int x) { for (int i = 0; i < nit; i++) if (it[i] == x) return 1; if (fixed0 >= 0 && x == nfl + fixed0) return 1; return 0; }
static int rand_item(int isfix) {
    for (int t = 0; t < 1000; t++) { int x = isfix ? (int)(rnd() % nfl) : nfl + (int)(rnd() % nol); if (!used(x)) return x; }
    return -1;
}
static void randomize(void) {
    nit = 0;
    for (int i = 0; i < nf_; i++) { int x = rand_item(1); it[nit++] = x; }
    for (int i = 0; i < nm_; i++) { int x = rand_item(0); it[nit++] = x; }
}

static uint32_t bS = 0, sK = 0;
static int XK[256], XKI[256], nxk, covbase, Sk[32], nsk, FAST = 1, FASTCHECK = 0; static long long nfastbad = 0;
static void base_for(int i) {                     /* coverage of X_keep X_keep, X_keep = S'^-1 S', S' = S minus item i */
    nsk = 0;
    if (fixed0 >= 0) { Sk[nsk++] = ol[fixed0][0]; Sk[nsk++] = ol[fixed0][1]; } else Sk[nsk++] = 0;
    for (int q = 0; q < nit; q++) if (q != i) { int x = it[q];
        if (x < nfl) Sk[nsk++] = fl[x]; else { Sk[nsk++] = ol[x - nfl][0]; Sk[nsk++] = ol[x - nfl][1]; } }
    sK++; nxk = 0;
    for (int a = 0; a < nsk; a++) for (int b = 0; b < nsk; b++) { int x = M(inv[Sk[a]], Sk[b]);
        if (mkK[x] != sK) { mkK[x] = sK; XK[nxk++] = x; } }
    for (int t = 0; t < nxk; t++) XKI[t] = inv[XK[t]];
    bS++; covbase = 1; bst[0] = bS;
    for (int a = 0; a < nxk; a++) { const uint16_t *row = mul + (size_t)XK[a] * n;
        for (int t = a + 1; t < nxk; t++) { int z = row[XKI[t]];
            if (bst[z] != bS) { bst[z] = bS; covbase++; int zi = inv[z]; if (bst[zi] != bS) { bst[zi] = bS; covbase++; } } } }
}
static int cand_energy(int x) {                   /* energy of S' + item x (after base_for) */
    int Nn[2], nn = 0, NX[128], NXI[128], nnx = 0;
    if (x < nfl) Nn[nn++] = fl[x]; else { Nn[nn++] = ol[x - nfl][0]; Nn[nn++] = ol[x - nfl][1]; }
    sM++;
    for (int u = 0; u < nn; u++) { int sv = Nn[u];
        for (int b = 0; b < nsk + nn; b++) { int bv = b < nsk ? Sk[b] : Nn[b - nsk];
            int x1 = M(inv[sv], bv), x2 = M(inv[bv], sv);
            if (mkK[x1] != sK && mk[x1] != sM) { mk[x1] = sM; NX[nnx++] = x1; }
            if (mkK[x2] != sK && mk[x2] != sM) { mk[x2] = sM; NX[nnx++] = x2; } } }
    for (int t = 0; t < nnx; t++) NXI[t] = inv[NX[t]];
    sA++; int cov = covbase;
    for (int a = 0; a < nnx; a++) { const uint16_t *row = mul + (size_t)NX[a] * n;
        for (int t = 0; t < nxk; t++) { int z = row[XKI[t]];
            if (bst[z] != bS && stA[z] != sA) { stA[z] = sA; cov++; int zi = inv[z]; if (bst[zi] != bS && stA[zi] != sA) { stA[zi] = sA; cov++; } } }
        for (int t = a + 1; t < nnx; t++) { int z = row[NXI[t]];
            if (bst[z] != bS && stA[z] != sA) { stA[z] = sA; cov++; int zi = inv[z]; if (bst[zi] != bS && stA[zi] != sA) { stA[zi] = sA; cov++; } } } }
    return n - cov;
}
static double deep_secs = 0; static int deep_thr = 0, ENDG = 0, SCANGAP = 25; static long long nscan = 0, nscanimp = 0;
static int full_scan(int *bi_out, int *bx_out) {   /* best single replacement over the whole neighbourhood */
    int be = 1 << 30;
    for (int i = 0; i < nit; i++) { int isfix = it[i] < nfl, lo = isfix ? 0 : nfl, hi = isfix ? nfl : nfl + nol;
        if (FAST) base_for(i);
        for (int x = lo; x < hi; x++) { if (used(x)) continue;
            int e2;
            if (FAST) e2 = cand_energy(x);
            else { int old = it[i]; it[i] = x; int kk = build(); e2 = pp_uncov2(S, kk); it[i] = old; }
            if (e2 < be) { be = e2; *bi_out = i; *bx_out = x; } } }
    return be;
}
/* card c6: compound moves and elite restarts (all off unless PAIRS / ELITE / PERT are set) */
static int PAIRS = 0, ELITE = 0, PERT = 0, PERT2 = 2;
static int elI[64][32], elE[64], elite_n = 0;
static int pI[256], pJ[256], pX[256], pY[256], pE[256];
static int pair_energy(int i, int j, int x, int y) {          /* energy of S with items i, j replaced by x, y */
    int oi = it[i], oj = it[j]; it[i] = x; it[j] = y;
    int kk = build(); int e2 = pp_uncov2(S, kk);
    it[i] = oi; it[j] = oj; return e2;
}
static void elite_insert(int e) {                              /* keep the ELITE lowest distinct states seen */
    if (ELITE <= 0) return;
    int srt[32];
    memcpy(srt, it, sizeof(int) * nit);
    for (int a = 1; a < nit; a++) { int v = srt[a], b = a - 1; while (b >= 0 && srt[b] > v) { srt[b + 1] = srt[b]; b--; } srt[b + 1] = v; }
    for (int q = 0; q < elite_n; q++) if (memcmp(elI[q], srt, sizeof(int) * nit) == 0) return;
    if (elite_n < ELITE) { memcpy(elI[elite_n], srt, sizeof(int) * nit); elE[elite_n] = e; elite_n++; return; }
    int w = 0; for (int q = 1; q < elite_n; q++) if (elE[q] > elE[w]) w = q;
    if (e < elE[w]) { memcpy(elI[w], srt, sizeof(int) * nit); elE[w] = e; }
}
static void elite_restart(void) {                              /* random elite state with PERT2 items replaced */
    int q = (int)(rnd() % elite_n);
    memcpy(it, elI[q], sizeof(int) * nit);
    for (int p = 0; p < PERT2; p++) { int i = (int)(rnd() % nit); int x = rand_item(it[i] < nfl); if (x >= 0) it[i] = x; }
}
static void run(int r, int f, int m, double secs, int NB, int TEN, int STALL, int MAXSOL) {
    setup(r);
    if (rkind[r]) { fixed0 = orbof[0]; nf_ = 0; nm_ = m - 1; } else { fixed0 = -1; nf_ = f - 1; nm_ = m; }
    char tag[96]; snprintf(tag, sizeof tag, "r%d_%s%d_f%d_m%d_tabu", r, rkind[r] ? "ext" : "alpha", rkind[r] ? rc[r] : rp[r], f, m);
    if (nf_ > nfl || nm_ > nol - (fixed0 >= 0) || (nf_ == 0 && nm_ == 0)) return;
    tabu_until = calloc(nfl + nol, sizeof(long long)); step = 0;
    clock_t c0 = clock(); int best = 1 << 30, sols = 0, restarts = 0;
    randomize(); int k = build(); int e = pp_uncov2(S, k), runbest = e; long long last_imp = 0;
    int extended = 0; long long last_scan = -1000000;
    elite_n = 0; elite_insert(e);
    for (;;) {
        double el = (double)(clock() - c0) / CLOCKS_PER_SEC;
        if (sols >= MAXSOL) break;
        if (el >= secs) { if (!extended && deep_secs > 0 && best <= deep_thr) { secs += deep_secs; extended = 1; } else break; }
        step++;
        int bi = -1, bx = -1, be = 1 << 30;
        int ci[256], cx[256], ce[256], nc = 0;
        for (int t = 0; t < NB && t < 256; t++) {
            int i = (int)(rnd() % nit), isfix = it[i] < nfl; int x = rand_item(isfix); if (x < 0) continue;
            ci[nc] = i; cx[nc] = x; nc++; }
        if (FAST) { for (int q = 0; q < nit; q++) { int any = 0;
                for (int c = 0; c < nc; c++) if (ci[c] == q) { if (!any) { base_for(q); any = 1; } ce[c] = cand_energy(cx[c]); } } }
        if (!FAST || FASTCHECK) for (int c = 0; c < nc; c++) {
            int old = it[ci[c]]; it[ci[c]] = cx[c]; int kk = build(); int e2 = pp_uncov2(S, kk); it[ci[c]] = old;
            if (FAST && e2 != ce[c]) nfastbad++;
            ce[c] = e2; }
        for (int c = 0; c < nc; c++) {
            if (tabu_until[cx[c]] > step && ce[c] >= best) continue;
            if (ce[c] < be) { be = ce[c]; bi = ci[c]; bx = cx[c]; }
        }
        if (ENDG && e <= ENDG && step - last_scan >= SCANGAP) { int si = -1, sx = -1; last_scan = step; nscan++;
            int se = full_scan(&si, &sx);
            if (si >= 0 && se < e && se < be) { be = se; bi = si; bx = sx; nscanimp++; } }
        int np = 0;                                    /* compound candidates: replace TWO items at once */
        if (PAIRS > 0 && nit >= 2) for (int t = 0; t < PAIRS && t < 256; t++) {
            int i = (int)(rnd() % nit), j = (int)(rnd() % (nit - 1)); if (j >= i) j++;
            int x = rand_item(it[i] < nfl), y = rand_item(it[j] < nfl);
            if (x < 0 || y < 0 || x == y) continue;
            pI[np] = i; pJ[np] = j; pX[np] = x; pY[np] = y; pE[np] = pair_energy(i, j, x, y); np++; }
        int bpair = -1;
        for (int c = 0; c < np; c++) {
            if ((tabu_until[pX[c]] > step || tabu_until[pY[c]] > step) && pE[c] >= best) continue;
            if (pE[c] < be) { be = pE[c]; bpair = c; bi = -1; }
        }
        if (bpair >= 0) {
            tabu_until[it[pI[bpair]]] = step + TEN; tabu_until[it[pJ[bpair]]] = step + TEN;
            it[pI[bpair]] = pX[bpair]; it[pJ[bpair]] = pY[bpair]; e = be;
        } else {
            if (bi < 0) continue;
            tabu_until[it[bi]] = step + TEN; it[bi] = bx; e = be;
        }
        if (e < runbest) { runbest = e; last_imp = step; }
        if (e < best) best = e;
        elite_insert(e);
        if (e == 0) { k = build();
            if (fullcheck(S, k)) { sols++; nsol++;
                printf("SOL %s", tag); for (int i = 0; i < k; i++) printf(" %d", S[i]); printf("\n"); fflush(stdout);
                if (edges_out && nsol == 1) { FILE *o = fopen(edges_out, "w"); fprintf(o, "%d\n", 2 * n);
                    for (int g = 0; g < n; g++) for (int i = 0; i < k; i++) fprintf(o, "%d %d\n", g, n + M(S[i], g));
                    fclose(o); } }
            else fprintf(stderr, "WARNING %s: energy 0 but the full check fails\n", tag);
            randomize(); k = build(); e = pp_uncov2(S, k); runbest = e; last_imp = step; restarts++; continue; }
        if (step - last_imp > STALL) {
            if (PERT && elite_n > 0) elite_restart(); else randomize();
            k = build(); e = pp_uncov2(S, k); runbest = e; last_imp = step; restarts++; }
    }
    printf("TABU rec %d %s %d f %d m %d best %d sols %d steps %lld restarts %d secs %.1f%s", r, rkind[r] ? "ext" : "alpha",
           rkind[r] ? rc[r] : rp[r], f, m, best, sols, step, restarts, (double)(clock() - c0) / CLOCKS_PER_SEC, extended ? " DEEP" : "");
    if (ENDG) printf(" scans %lld improving %lld", nscan, nscanimp);
    printf(" pairs %d elite %d pert %d", PAIRS, ELITE, PERT);
    if (FASTCHECK) printf(" fastcheck_mismatches %lld", nfastbad);
    printf("\n");
    fflush(stdout); free(tabu_until);
}

static int intype(const char *types, int f) {      /* is f in the comma list? */
    const char *p = types;
    while (*p) { if (*p >= '0' && *p <= '9') { int v = atoi(p); if (v == f) return 1; while (*p >= '0' && *p <= '9') p++; } else p++; }
    return 0;
}
int main(int argc, char **argv) {
    if (argc < 3) { fprintf(stderr, "usage: sdtabu2 FILE.ht REC F M | all\n"); return 2; }
    if (getenv("K")) K = atoi(getenv("K"));
    double secs = getenv("SECS") ? atof(getenv("SECS")) : 20;
    int NB = getenv("NB") ? atoi(getenv("NB")) : 48, TEN = getenv("TEN") ? atoi(getenv("TEN")) : 12;
    int STALL = getenv("STALL") ? atoi(getenv("STALL")) : 300, MAXSOL = getenv("MAXSOL") ? atoi(getenv("MAXSOL")) : 5;
    if (getenv("SEED")) { rs ^= (uint64_t)atoll(getenv("SEED")) * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 10; i++) rnd(); }
    edges_out = getenv("EDGES");
    if (getenv("ENDG")) ENDG = atoi(getenv("ENDG"));
    if (getenv("FAST")) FAST = atoi(getenv("FAST"));
    if (getenv("FASTCHECK")) FASTCHECK = atoi(getenv("FASTCHECK"));
    if (getenv("SCANGAP")) SCANGAP = atoi(getenv("SCANGAP"));
    if (getenv("PAIRS")) PAIRS = atoi(getenv("PAIRS"));          /* card c6: two-item candidates per step */
    if (getenv("ELITE")) ELITE = atoi(getenv("ELITE"));          /* card c6: elite pool size (<= 64) */
    if (getenv("PERT")) PERT = atoi(getenv("PERT"));             /* card c6: 1 = restart from perturbed elite */
    if (getenv("PERT2")) PERT2 = atoi(getenv("PERT2"));
    if (getenv("DEEP")) sscanf(getenv("DEEP"), "%d,%lf", &deep_thr, &deep_secs);   /* DEEP=thr,secs: extend a type whose best <= thr */
    load(argv[1]);
    psi = malloc(sizeof(int) * n); fl = malloc(sizeof(int) * n); ol = malloc(sizeof(int) * 2 * n); orbof = malloc(sizeof(int) * n);
    printf("GROUP %s n %d K %d records %d\n", argv[1], n, K, nrec);
    if (getenv("ENERGYTEST")) { int N = atoi(getenv("ENERGYTEST")), bad = 0, T[32];
        for (int t = 0; t < N; t++) { for (int i = 0; i < K; i++) T[i] = (int)(rnd() % n); if (pp_uncov(T, K, 1) != pp_uncov2(T, K)) bad++; }
        printf("ENERGYTEST %d sets, %d differ\n", N, bad); return 0; }
    if (!strcmp(argv[2], "all")) {
        const char *types = getenv("TYPES");
        for (int r = 0; r < nrec; r++) {
            if (rkind[r] == 0 && rp[r] != 1 && rp[r] != 2) continue;
            if (rkind[r] == 0 && rp[r] == 1 && getenv("NOID")) continue;    /* NOID: skip beta = identity */
            if (rkind[r] == 1) { if (K % 2 == 0 && (!types || strchr(types, 'x'))) run(r, 0, K / 2, secs, NB, TEN, STALL, MAXSOL); continue; }
            for (int f = (K % 2 ? 1 : 2); f <= K; f += 2) {
                if (types && !intype(types, f)) continue;
                run(r, f, (K - f) / 2, secs, NB, TEN, STALL, MAXSOL); }
        }
    } else run(atoi(argv[2]), atoi(argv[3]), atoi(argv[4]), secs, NB, TEN, STALL, MAXSOL);
    printf("DONE sols %d\n", nsol);
    return 0;
}
