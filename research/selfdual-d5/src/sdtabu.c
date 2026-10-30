/* sdtabu.c: tabu search inside the self-dual (bipartite Cayley) family of sdk.c, for types too large to enumerate.
 * Same input as sdk (export_sd.g).  For a record r and type (f, m) the set is
 *   ALPHA: S = e + (f-1) psi-fixed elements + m psi-2-orbits;   EXT: S = {e, c^-1} + (m-1) further 2-orbits,
 * psi(x) = c^-1 beta(x)^-1.  Energy |G \ X X| (X = S^-1 S), which is 0 iff the Haar graph has diameter <= 5 (the
 * graph is a Cayley graph); every energy-0 set also gets the full three-condition check before it is reported.
 * Move: replace one chosen fixed element or one chosen orbit by an unused one; NB random candidate moves per step,
 * best non-tabu one taken (a move that beats the best energy so far is always allowed); removed items are tabu for
 * TEN steps; restart from a random set after STALL steps without improvement.
 * usage: sdtabu FILE.ht REC F M      or      sdtabu FILE.ht all   (every record and every type of valency K, SECS each)
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
static uint32_t *stA, *mk; static uint32_t sA = 0, sM = 0;
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
    stA = calloc(n, sizeof(uint32_t)); mk = calloc(n, sizeof(uint32_t));
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

static double deep_secs = 0; static int deep_thr = 0;
static void run(int r, int f, int m, double secs, int NB, int TEN, int STALL, int MAXSOL) {
    setup(r);
    if (rkind[r]) { fixed0 = orbof[0]; nf_ = 0; nm_ = m - 1; } else { fixed0 = -1; nf_ = f - 1; nm_ = m; }
    char tag[96]; snprintf(tag, sizeof tag, "r%d_%s%d_f%d_m%d_tabu", r, rkind[r] ? "ext" : "alpha", rkind[r] ? rc[r] : rp[r], f, m);
    if (nf_ > nfl || nm_ > nol - (fixed0 >= 0) || (nf_ == 0 && nm_ == 0)) return;
    tabu_until = calloc(nfl + nol, sizeof(long long)); step = 0;
    clock_t c0 = clock(); int best = 1 << 30, sols = 0, restarts = 0;
    randomize(); int k = build(); int e = pp_uncov(S, k, 1), runbest = e; long long last_imp = 0;
    int extended = 0;
    for (;;) {
        double el = (double)(clock() - c0) / CLOCKS_PER_SEC;
        if (sols >= MAXSOL) break;
        if (el >= secs) { if (!extended && deep_secs > 0 && best <= deep_thr) { secs += deep_secs; extended = 1; } else break; }
        step++;
        int bi = -1, bx = -1, be = 1 << 30;
        for (int t = 0; t < NB; t++) {
            int i = (int)(rnd() % nit), isfix = it[i] < nfl; int x = rand_item(isfix); if (x < 0) continue;
            int old = it[i]; it[i] = x; int kk = build(); int e2 = pp_uncov(S, kk, 1); it[i] = old;
            if (tabu_until[x] > step && e2 >= best) continue;
            if (e2 < be) { be = e2; bi = i; bx = x; }
        }
        if (bi < 0) continue;
        tabu_until[it[bi]] = step + TEN; it[bi] = bx; e = be;
        if (e < runbest) { runbest = e; last_imp = step; }
        if (e < best) best = e;
        if (e == 0) { k = build();
            if (fullcheck(S, k)) { sols++; nsol++;
                printf("SOL %s", tag); for (int i = 0; i < k; i++) printf(" %d", S[i]); printf("\n"); fflush(stdout);
                if (edges_out && nsol == 1) { FILE *o = fopen(edges_out, "w"); fprintf(o, "%d\n", 2 * n);
                    for (int g = 0; g < n; g++) for (int i = 0; i < k; i++) fprintf(o, "%d %d\n", g, n + M(S[i], g));
                    fclose(o); } }
            else fprintf(stderr, "WARNING %s: energy 0 but the full check fails\n", tag);
            randomize(); k = build(); e = pp_uncov(S, k, 1); runbest = e; last_imp = step; restarts++; continue; }
        if (step - last_imp > STALL) { randomize(); k = build(); e = pp_uncov(S, k, 1); runbest = e; last_imp = step; restarts++; }
    }
    printf("TABU rec %d %s %d f %d m %d best %d sols %d steps %lld restarts %d secs %.1f%s\n", r, rkind[r] ? "ext" : "alpha",
           rkind[r] ? rc[r] : rp[r], f, m, best, sols, step, restarts, (double)(clock() - c0) / CLOCKS_PER_SEC, extended ? " DEEP" : "");
    fflush(stdout); free(tabu_until);
}

int main(int argc, char **argv) {
    if (argc < 3) { fprintf(stderr, "usage: sdtabu FILE.ht REC F M | all\n"); return 2; }
    if (getenv("K")) K = atoi(getenv("K"));
    double secs = getenv("SECS") ? atof(getenv("SECS")) : 20;
    int NB = getenv("NB") ? atoi(getenv("NB")) : 48, TEN = getenv("TEN") ? atoi(getenv("TEN")) : 12;
    int STALL = getenv("STALL") ? atoi(getenv("STALL")) : 300, MAXSOL = getenv("MAXSOL") ? atoi(getenv("MAXSOL")) : 5;
    if (getenv("SEED")) { rs ^= (uint64_t)atoll(getenv("SEED")) * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 10; i++) rnd(); }
    edges_out = getenv("EDGES");
    if (getenv("DEEP")) sscanf(getenv("DEEP"), "%d,%lf", &deep_thr, &deep_secs);   /* DEEP=thr,secs: extend a type whose best <= thr */
    load(argv[1]);
    psi = malloc(sizeof(int) * n); fl = malloc(sizeof(int) * n); ol = malloc(sizeof(int) * 2 * n); orbof = malloc(sizeof(int) * n);
    printf("GROUP %s n %d K %d records %d\n", argv[1], n, K, nrec);
    if (!strcmp(argv[2], "all")) {
        const char *types = getenv("TYPES");
        for (int r = 0; r < nrec; r++) {
            if (rkind[r] == 0 && rp[r] != 1 && rp[r] != 2) continue;
            if (rkind[r] == 1) { if (K % 2 == 0 && (!types || strchr(types, '0'))) run(r, 0, K / 2, secs, NB, TEN, STALL, MAXSOL); continue; }
            for (int f = (K % 2 ? 1 : 2); f <= K; f += 2) {
                if (types) { char b[4]; snprintf(b, sizeof b, "%d", f % 10); if (!strstr(types, b)) continue; }
                run(r, f, (K - f) / 2, secs, NB, TEN, STALL, MAXSOL); }
        }
    } else run(atoi(argv[2]), atoi(argv[3]), atoi(argv[4]), secs, NB, TEN, STALL, MAXSOL);
    printf("DONE sols %d\n", nsol);
    return 0;
}
