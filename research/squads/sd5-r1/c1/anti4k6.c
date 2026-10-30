/* anti4k6.c (squad sd5-r1, card c1): self-dual Haar graphs of valency 6 for psi(x) = beta(x)^-1, beta an
 * automorphism of order 4 (mode o4), plus an order-2 calibration mode (o2).
 *
 * H(G,S): A-g ~ B-h iff h g^-1 in S (A-g ~ B-sg).  If psi(S) = S, the map A-g -> B-beta(g), B-h -> A-beta(h) is an
 * automorphism of H(G,S) (it needs exactly psi(S) = S), so diameter <= 5 iff X X = G with X = S^-1 S (then Y Y = G
 * and Y Y S = G follow).  The checker still tests Y Y = G and the odd condition for every solution (fullcheck).
 *
 * Psi-orbit types of a valency-6 S (psi has orbits of size 1, 2, 4 for beta of order 4):
 *   A  {e, f} + one 4-orbit   (f psi-fixed; any S with a psi-fixed point is translated to contain e: S -> s0^-1 S
 *                              keeps psi' = inn(s0^-1) o beta with psi'^2 = psi^2, so the order is still 4)
 *   B  one 2-orbit + one 4-orbit, no psi-fixed point (no normalisation possible)
 *   X  (EXTRA=1, or always in mode o2) types without a 4-orbit: {e} + 5 fixed, {e} + 3 fixed + 1 pair,
 *      {e} + 1 fixed + 2 pairs, and 3 pairs with no fixed point.
 * Mode o2 uses the ALPHA 2 records (beta an involution) for calibration against sdk's K = 6 types.
 * Every set is tested exactly with the move-to-front fast rejection; for types A and B the exact |G \ XX| of each
 * failing set is also computed (best = minimum, the near-miss score).
 *
 * usage: anti4k6 FILE.ht o4|o2      (FILE from research/d75-raise/src/export.g)
 * env: EDGEDIR=dir (write the first MAXW solutions as edge lists dir/sol<k>.edges, vertex A-g = g, B-g = n+g),
 *      EXTRA=1 (mode o4: add the types without a 4-orbit), CAP=<evals> (cap for the X types, default 3000000),
 *      ALPHAMAX=<k> (only the first k records of the mode).
 * output: "ALPHA4 ..." / "PAT ..." lines, "SOL ..." per solution, "DONE ..." summary.  Exit 0.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

static int n, ninv;
static uint16_t *mul, *mulT;
static int *inv;
static int nal, alp[64]; static int *aperm[64];
#define M(a,b) mul[(size_t)(a) * n + (b)]

static uint32_t *stampA, *stampB, *mk; static uint32_t stA = 0, stB = 0, stM = 0;
static int *ordA, *ordB;
static long long evals = 0, npassA = 0, anomaly_yy = 0, anomaly_odd = 0;
static int nsol = 0, nwritten = 0; static const char *edgedir = NULL; static int MAXW = 12;
static int K = 6;

/* psi-orbits of the current record */
static int nF, *Fx; static int n2, (*O2)[2]; static int n4, (*O4)[4]; static int nother;

static int rdint(FILE *f) { int x; if (fscanf(f, "%d", &x) != 1) { fprintf(stderr, "read error\n"); exit(1); } return x; }

static void load(const char *path) {
    FILE *f = fopen(path, "r"); if (!f) { perror(path); exit(1); }
    n = rdint(f); ninv = rdint(f);
    mul = malloc(sizeof(uint16_t) * n * n); inv = malloc(sizeof(int) * n);
    for (int i = 0; i < n * n; i++) mul[i] = rdint(f);
    for (int i = 0; i < n; i++) inv[i] = rdint(f);
    mulT = malloc(sizeof(uint16_t) * n * n);
    for (int a = 0; a < n; a++) for (int b = 0; b < n; b++) mulT[(size_t)b * n + a] = mul[(size_t)a * n + b];
    char w[32];
    while (fscanf(f, "%31s", w) == 1) {
        if (!strcmp(w, "ALPHA")) {
            int p = rdint(f); alp[nal] = p; aperm[nal] = malloc(sizeof(int) * n);
            for (int i = 0; i < n; i++) aperm[nal][i] = rdint(f);
            if (fscanf(f, "%31s", w) != 1 || strcmp(w, "CENT")) { fprintf(stderr, "format\n"); exit(1); }
            int k = rdint(f); for (int j = 0; j < k * n; j++) rdint(f);   /* centralizer: not needed */
            nal++; if (nal >= 64) break;
        }
    }
    fclose(f);
    stampA = calloc(n, sizeof(uint32_t)); stampB = calloc(n, sizeof(uint32_t)); mk = calloc(n, sizeof(uint32_t));
    ordA = malloc(sizeof(int) * n); ordB = malloc(sizeof(int) * n);
    for (int i = 0; i < n; i++) ordA[i] = ordB[i] = i;
    for (int i = 0; i < n; i++) if (M(0, i) != i || M(i, 0) != i || M(i, inv[i]) != 0) { fprintf(stderr, "bad table\n"); exit(1); }
    Fx = malloc(sizeof(int) * n); O2 = malloc(sizeof(int) * 2 * n); O4 = malloc(sizeof(int) * 4 * n);
}

/* uncovered count of XX (left=1: X = S^-1 S) or YY (left=0: Y = S S^-1) */
static int xx_uncov(const int *S, int k, int left) {
    int X[64], nx = 0;
    stB++;
    for (int i = 0; i < k; i++) for (int j = 0; j < k; j++) {
        int x = left ? M(inv[S[i]], S[j]) : M(S[i], inv[S[j]]);
        if (stampB[x] != stB) { stampB[x] = stB; X[nx++] = x; }
    }
    stA++; int cov = 0;
    for (int i = 0; i < nx; i++) { const uint16_t *row = mul + (size_t)X[i] * n;
        for (int j = 0; j < nx; j++) { int z = row[X[j]]; if (stampA[z] != stA) { stampA[z] = stA; cov++; } } }
    return n - cov;
}
/* fast rejection: is every z in P P?  z in PP iff x^-1 z in P for some x in P.  Move-to-front target order. */
static int pp_full(const int *S, int k, int left, int *ord) {
    int X[64], nx = 0; stM++;
    for (int i = 0; i < k; i++) for (int j = 0; j < k; j++) {
        int x = left ? M(inv[S[i]], S[j]) : M(S[i], inv[S[j]]);
        if (mk[x] != stM) { mk[x] = stM; X[nx++] = x; }
    }
    int ix[64]; for (int i = 0; i < nx; i++) ix[i] = inv[X[i]];
    for (int t = 0; t < n; t++) { int z = ord[t], ok = 0; const uint16_t *col = mulT + (size_t)z * n;   /* col[y] = y z */
        for (int i = 0; i < nx; i++) if (mk[col[ix[i]]] == stM) { ok = 1; break; }
        if (!ok) { if (t) { int u = t / 2; ord[t] = ord[u]; ord[u] = z; } return 0; } }
    return 1;
}
/* 2: XX = G and YY = G;  1: XX = G, YY != G (cannot happen for self-dual S: anomaly);  0: XX != G */
static int fast_ok(const int *S, int k) {
    evals++;
    if (!pp_full(S, k, 1, ordA)) return 0;
    npassA++;
    return pp_full(S, k, 0, ordB) ? 2 : 1;
}
/* full check: XX = G, YY = G and Y Y S = G (A-B distance 5), distinct elements */
static int fullcheck(const int *S, int k) {
    for (int i = 0; i < k; i++) for (int j = i + 1; j < k; j++) if (S[i] == S[j]) return 0;
    if (xx_uncov(S, k, 1) || xx_uncov(S, k, 0)) return 0;
    int Y[64], ny = 0; stB++;
    for (int i = 0; i < k; i++) for (int j = 0; j < k; j++) { int x = M(S[i], inv[S[j]]); if (stampB[x] != stB) { stampB[x] = stB; Y[ny++] = x; } }
    char *yy = calloc(n, 1), *odd = calloc(n, 1);
    for (int i = 0; i < ny; i++) for (int j = 0; j < ny; j++) yy[M(Y[i], Y[j])] = 1;
    for (int z = 0; z < n; z++) if (yy[z]) for (int i = 0; i < k; i++) odd[M(z, S[i])] = 1;
    int ok = 1; for (int z = 0; z < n; z++) if (!odd[z]) ok = 0;
    free(yy); free(odd); return ok;
}

static int cur_rec; static char tagbuf[96];
static void report(const int *S, int k) {
    nsol++;
    printf("SOL %s", tagbuf); for (int i = 0; i < k; i++) printf(" %d", S[i]); printf("\n"); fflush(stdout);
    if (edgedir && nwritten < MAXW) {
        char path[1024]; snprintf(path, sizeof path, "%s/sol%d.edges", edgedir, nwritten); nwritten++;
        FILE *f = fopen(path, "w"); if (!f) return; fprintf(f, "%d\n", 2 * n);
        for (int g = 0; g < n; g++) for (int i = 0; i < k; i++) fprintf(f, "%d %d\n", g, n + M(S[i], g));
        fclose(f);
    }
}

/* ---- pattern enumeration ---- */
static int Sb[8], ns;
static int pf, pm2, pm4;           /* numbers of extra fixed points, 2-orbits, 4-orbits */
static int exact_on;               /* compute exact |G \ XX| for failing sets */
static long long capev, evalbase; static int capped;
static long long typesol; static int typebest;
static int gbest = 1 << 30; static int gbest_rec = -1;

static void leaf(void) {
    if (capped) return;
    if (evals - evalbase >= capev) { capped = 1; return; }
    int r = fast_ok(Sb, K);
    if (r == 2) { if (fullcheck(Sb, K)) { typesol++; report(Sb, K); } else anomaly_odd++; return; }
    if (r == 1) { anomaly_yy++; }
    if (exact_on) { int c = xx_uncov(Sb, K, 1); if (c < typebest) typebest = c; if (c < gbest) { gbest = c; gbest_rec = cur_rec; } }
}
static void choose_o4(int need, int start) {
    if (capped) return;
    if (need == 0) { leaf(); return; }
    for (int i = start; i < n4 && !capped; i++) { Sb[ns++] = O4[i][0]; Sb[ns++] = O4[i][1]; Sb[ns++] = O4[i][2]; Sb[ns++] = O4[i][3];
        choose_o4(need - 1, i + 1); ns -= 4; }
}
static void choose_o2(int need, int start) {
    if (need == 0) { choose_o4(pm4, 0); return; }
    for (int i = start; i < n2 && !capped; i++) { Sb[ns++] = O2[i][0]; Sb[ns++] = O2[i][1];
        choose_o2(need - 1, i + 1); ns -= 2; }
}
static void choose_fix(int need, int start) {
    if (need == 0) { choose_o2(pm2, 0); return; }
    for (int i = start; i < nF && !capped; i++) { Sb[ns++] = Fx[i]; choose_fix(need - 1, i + 1); ns--; }
}
/* eflag: e (index 0) is in S; then pf extra fixed points, pm2 pairs, pm4 quadruples fill S (size K) */
static void run_pattern(const char *name, int eflag, int pf_, int pm2_, int pm4_, int exact, long long cap) {
    pf = pf_; pm2 = pm2_; pm4 = pm4_; exact_on = exact; capev = cap; capped = 0; typebest = 1 << 30; typesol = 0;
    int size = eflag + pf + 2 * pm2 + 4 * pm4;
    if (size != K) { fprintf(stderr, "pattern %s has size %d\n", name, size); exit(1); }
    if (pf > nF || pm2 > n2 || pm4 > n4) { printf("PAT %s skipped (nF %d n2 %d n4 %d)\n", name, nF, n2, n4); return; }
    long long e0 = evals, p0 = npassA; clock_t c0 = clock(); evalbase = evals;
    snprintf(tagbuf, sizeof tagbuf, "%s_r%d", name, cur_rec);
    ns = 0; if (eflag) Sb[ns++] = 0;
    choose_fix(pf, 0);
    printf("PAT %s rec %d nF %d n2 %d n4 %d sets %lld passXX %lld best %d sols %lld%s secs %.2f\n", name, cur_rec, nF, n2, n4,
           evals - e0, npassA - p0, typebest, typesol, capped ? " CAPPED" : "", (double)(clock() - c0) / CLOCKS_PER_SEC);
    fflush(stdout);
}

/* psi = inv o beta for record a: orbits of size 1 (-> Fx, identity excluded), 2 (-> O2), 4 (-> O4) */
static void build_psi(int a) {
    int *pm = aperm[a]; int *seen = calloc(n, sizeof(int));
    nF = n2 = n4 = nother = 0;
    for (int i = 0; i < n; i++) if (!seen[i]) {
        int c[8], k = 0, x = i;
        do { if (k < 8) c[k] = x; k++; seen[x] = 1; x = inv[pm[x]]; } while (x != i && k <= 8);
        if (k == 1) { if (i != 0) Fx[nF++] = i; }
        else if (k == 2) { O2[n2][0] = c[0]; O2[n2][1] = c[1]; n2++; }
        else if (k == 4) { for (int j = 0; j < 4; j++) O4[n4][j] = c[j]; n4++; }
        else nother++;
    }
    free(seen);
}

int main(int argc, char **argv) {
    if (argc < 3) { fprintf(stderr, "usage: anti4k6 FILE.ht o4|o2\n"); return 2; }
    edgedir = getenv("EDGEDIR");
    if (getenv("MAXW")) MAXW = atoi(getenv("MAXW"));
    long long capX = getenv("CAP") ? atoll(getenv("CAP")) : 3000000LL;
    int extra = getenv("EXTRA") ? atoi(getenv("EXTRA")) : 0;
    int alphamax = getenv("ALPHAMAX") ? atoi(getenv("ALPHAMAX")) : 1 << 20;
    int mode4 = strcmp(argv[2], "o2") != 0;   /* o4 unless o2 */
    load(argv[1]);
    printf("GROUP %s n %d ninv %d nalpha %d mode %s\n", argv[1], n, ninv, nal, mode4 ? "o4" : "o2");
    clock_t t0 = clock(); long long totsol = 0;
    int nrec = 0;
    for (int a = 0; a < nal && nrec < alphamax; a++) {
        if (alp[a] != (mode4 ? 4 : 2)) continue;
        nrec++; cur_rec = a;
        build_psi(a);
        printf("ALPHA%d rec %d fixed %d two %d four %d other %d\n", alp[a], a, nF, n2, n4, nother);
        if (mode4) {
            /* type A: e + psi-fixed f + 4-orbit;  type B: 2-orbit + 4-orbit (no e) */
            run_pattern("A", 1, 1, 0, 1, 1, (long long)1 << 62);
            run_pattern("B", 0, 0, 1, 1, 1, (long long)1 << 62);
            if (extra) {
                run_pattern("X5", 1, 5, 0, 0, 0, capX);
                run_pattern("X31", 1, 3, 1, 0, 0, capX);
                run_pattern("X12", 1, 1, 2, 0, 0, capX);
                run_pattern("X03", 0, 0, 3, 0, 0, capX);
            }
        } else {
            /* calibration: the sdk K = 6 types for psi of order 2 (f = fixed incl. e, m = pairs) */
            run_pattern("f6m0", 1, 5, 0, 0, 0, capX);
            run_pattern("f4m1", 1, 3, 1, 0, 0, capX);
            run_pattern("f2m2", 1, 1, 2, 0, 0, capX);
            run_pattern("f0m3", 0, 0, 3, 0, 0, capX);
        }
        totsol += typesol;
    }
    printf("DONE n %d 2n %d records %d sols %d best %d bestrec %d evals %lld passXX %lld anomaly_yy %lld anomaly_odd %lld secs %.1f\n",
           n, 2 * n, nrec, nsol, gbest == (1 << 30) ? -1 : gbest, gbest_rec, evals, npassA, anomaly_yy, anomaly_odd,
           (double)(clock() - t0) / CLOCKS_PER_SEC);
    return 0;
}
