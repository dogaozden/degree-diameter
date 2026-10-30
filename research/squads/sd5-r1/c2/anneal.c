/* anneal.c (card c4): tabu search / simulated annealing over psi-invariant connection sets S of valency 7 for
 * Haar graphs H(G,S), restricted to the self-dual family psi(x) = beta(x)^-1 with beta an automorphism of G of order
 * 1 or 2 (ALPHA index in export.g's table).  Identity is always in S (as in haar75 anti).
 * Type (f,m): f psi-fixed elements including the identity (Fix(psi) = {x : beta(x) = x^-1}), m psi-pairs
 * {g, beta(g)^-1}; f + 2m = 7.  Energy = |G \ XX| only, X = S^-1 S (self-dual: XX = G implies YY = G).
 * A set with energy 0 is checked with the full test (YY = G, YY S = G, distinct elements) before it is reported.
 * Table loading, xx_uncov and the fullcheck logic are copied from research/d75-raise/src/haar75.c.
 *
 * usage: anneal FILE.ht ALPHA F M
 * env:   MODE=tabu|sa (default tabu), SECS (default 60), SEED (default 1), MAXSOL (default 1000000),
 *        STALL (tabu iterations without improvement before a restart, default 400), TEN (tabu tenure, default 10),
 *        T0, T1 (SA temperatures, defaults 2.0 and 0.05), EDGES=file (writes the first solution's edge list),
 *        INIT="a b c ..." (optional: start from this S, element indices; used for calibration only).
 * output: "SOL ..." lines (element indices of S), then "END ..." summary.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <stdint.h>
#include <math.h>

static int n, ninv;
static uint16_t *mul;
static int *inv;
static int nal; static int alp[64]; static int *aperm[64];
static uint32_t *stampA, *stampB; static uint32_t stA = 0, stB = 0;
static long long evals = 0;
#define M(a,b) mul[(size_t)(a) * n + (b)]

static int rdint(FILE *f) { int x; if (fscanf(f, "%d", &x) != 1) { fprintf(stderr, "read error\n"); exit(1); } return x; }

/* copied from haar75.c: table loading */
static void load(const char *path) {
    FILE *f = fopen(path, "r"); if (!f) { perror(path); exit(1); }
    n = rdint(f); ninv = rdint(f);
    mul = malloc(sizeof(uint16_t) * n * n); inv = malloc(sizeof(int) * n);
    for (int i = 0; i < n * n; i++) mul[i] = rdint(f);
    for (int i = 0; i < n; i++) inv[i] = rdint(f);
    char w[32];
    while (fscanf(f, "%31s", w) == 1) {
        if (!strcmp(w, "ALPHA")) {
            int p = rdint(f); alp[nal] = p; aperm[nal] = malloc(sizeof(int) * n);
            for (int i = 0; i < n; i++) aperm[nal][i] = rdint(f);
            if (fscanf(f, "%31s", w) != 1 || strcmp(w, "CENT")) { fprintf(stderr, "format\n"); exit(1); }
            int k = rdint(f);
            for (int j = 0; j < k; j++) for (int i = 0; i < n; i++) rdint(f);
            nal++; if (nal >= 64) break;
        }
    }
    fclose(f);
    stampA = calloc(n, sizeof(uint32_t)); stampB = calloc(n, sizeof(uint32_t));
    for (int i = 0; i < n; i++) if (M(0, i) != i || M(i, 0) != i || M(i, inv[i]) != 0) { fprintf(stderr, "bad table\n"); exit(1); }
}

/* copied in spirit from haar75.c xx_uncov: number of elements of G in X X, X = S^-1 S (left = 1) or S S^-1 */
static int xx_cov(const int *S, int k, int left) {
    int X[64], nx = 0;
    stB++;
    for (int i = 0; i < k; i++) for (int j = 0; j < k; j++) {
        int x = left ? M(inv[S[i]], S[j]) : M(S[i], inv[S[j]]);
        if (stampB[x] != stB) { stampB[x] = stB; X[nx++] = x; }
    }
    stA++; int cov = 0;
    for (int i = 0; i < nx; i++) { const uint16_t *row = mul + (size_t)X[i] * n;
        for (int j = 0; j < nx; j++) { int z = row[X[j]]; if (stampA[z] != stA) { stampA[z] = stA; cov++; } } }
    return cov;
}
static inline int energy(const int *S, int k) { evals++; return n - xx_cov(S, k, 1); }

/* copied from haar75.c fullcheck: YY = G and YY S = G and distinct elements */
static int fullcheck(const int *S, int k) {
    for (int i = 0; i < k; i++) for (int j = i + 1; j < k; j++) if (S[i] == S[j]) return 0;
    if (xx_cov(S, k, 1) != n) return 0;
    int Y[64], ny = 0; stB++;
    for (int i = 0; i < k; i++) for (int j = 0; j < k; j++) { int x = M(S[i], inv[S[j]]); if (stampB[x] != stB) { stampB[x] = stB; Y[ny++] = x; } }
    char *yy = calloc(n, 1), *odd = calloc(n, 1);
    for (int i = 0; i < ny; i++) for (int j = 0; j < ny; j++) yy[M(Y[i], Y[j])] = 1;
    for (int z = 0; z < n; z++) if (yy[z]) for (int i = 0; i < k; i++) odd[M(z, S[i])] = 1;
    int ok = 1; for (int z = 0; z < n; z++) if (!odd[z]) ok = 0;
    free(yy); free(odd); return ok;
}

/* ---- psi structure ---- */
static int *psi;
static int nF, *Fl;           /* non-identity psi-fixed elements */
static int nP, (*Pr)[2];      /* psi-pairs {g, psi g} */
static int f, m, k;           /* f includes identity, k = 7 = f + 2m */
static int nsol = 0, maxsol = 1000000; static const char *edges_out = NULL;
static uint64_t rs = 88172645463325252ULL;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }

/* state: fx[0..f-2] indices into Fl, pr[0..m-1] indices into Pr */
static int fx[8], pr[8];
static char *usedF, *usedP;   /* per index into Fl / Pr */

static void make_S(const int *fxs, const int *prs, int *S) {
    int c = 0; S[c++] = 0;
    for (int i = 0; i < f - 1; i++) S[c++] = Fl[fxs[i]];
    for (int j = 0; j < m; j++) { S[c++] = Pr[prs[j]][0]; S[c++] = Pr[prs[j]][1]; }
}

static void report(const int *S, const char *tag) {
    nsol++;
    printf("SOL %s", tag); for (int i = 0; i < k; i++) printf(" %d", S[i]); printf("\n"); fflush(stdout);
    if (edges_out && nsol == 1) {
        FILE *fo = fopen(edges_out, "w"); fprintf(fo, "%d\n", 2 * n);
        for (int g = 0; g < n; g++) for (int i = 0; i < k; i++) fprintf(fo, "%d %d\n", g, n + M(S[i], g));
        fclose(fo);
    }
}

static void clear_state(void) { memset(usedF, 0, nF); memset(usedP, 0, nP); }
static void random_state(void) {
    clear_state();
    for (int i = 0; i < f - 1; i++) { int c; do c = rnd() % nF; while (usedF[c]); usedF[c] = 1; fx[i] = c; }
    for (int j = 0; j < m; j++) { int c; do c = rnd() % nP; while (usedP[c]); usedP[c] = 1; pr[j] = c; }
}

static long long nsolspan = 0;
/* verify and report when energy is zero */
static void check_zero(const int *S, const char *tag) {
    if (fullcheck(S, k)) { report(S, tag); nsolspan++; }
    else printf("ZERO-NOT-FULL %s", tag), printf("\n");
}

/* ---- tabu search (full neighbourhood, best admissible move) ---- */
static int TEN = 10, STALL = 400;
static void run_tabu(double secs) {
    long *tabuF = calloc(nF, sizeof(long)), *tabuP = calloc(nP, sizeof(long));
    time_t t0 = time(NULL); long it = 0, restarts = 0; int gbest = 1 << 30;
    random_state();
    int S[8]; make_S(fx, pr, S); int E = energy(S, k);
    int rbest = E; long since = 0;
    while (difftime(time(NULL), t0) < secs) {
        it++;
        if (E == 0) {
            char tag[64]; snprintf(tag, sizeof tag, "tabu_r%ld", restarts);
            make_S(fx, pr, S); check_zero(S, tag);
            if (nsol >= maxsol) break;
            /* continue from a fresh random state */
            restarts++; random_state(); make_S(fx, pr, S); E = energy(S, k); rbest = E; since = 0; continue;
        }
        int bestE = 1 << 30, bt = -1, bi = -1, bc = -1, cnt = 0; /* bt: 0 fixed slot, 1 pair slot */
        /* fixed slots */
        for (int i = 0; i < f - 1; i++) {
            int old = fx[i];
            for (int c = 0; c < nF; c++) {
                if (usedF[c]) continue;
                fx[i] = c; make_S(fx, pr, S); int e = energy(S, k);
                int tabu = tabuF[c] > it;
                if (tabu && !(e < gbest)) continue;
                if (e < bestE) { bestE = e; bt = 0; bi = i; bc = c; cnt = 1; }
                else if (e == bestE && (rnd() % (++cnt)) == 0) { bt = 0; bi = i; bc = c; }
            }
            fx[i] = old;
        }
        /* pair slots */
        for (int j = 0; j < m; j++) {
            int old = pr[j];
            for (int q = 0; q < nP; q++) {
                if (usedP[q]) continue;
                pr[j] = q; make_S(fx, pr, S); int e = energy(S, k);
                int tabu = tabuP[q] > it;
                if (tabu && !(e < gbest)) continue;
                if (e < bestE) { bestE = e; bt = 1; bi = j; bc = q; cnt = 1; }
                else if (e == bestE && (rnd() % (++cnt)) == 0) { bt = 1; bi = j; bc = q; }
            }
            pr[j] = old;
        }
        if (bt < 0) { restarts++; random_state(); make_S(fx, pr, S); E = energy(S, k); rbest = E; since = 0; continue; }
        if (bt == 0) { int old = fx[bi]; usedF[old] = 0; usedF[bc] = 1; fx[bi] = bc; tabuF[old] = it + TEN + rnd() % 5; }
        else         { int old = pr[bi]; usedP[old] = 0; usedP[bc] = 1; pr[bi] = bc; tabuP[old] = it + TEN + rnd() % 5; }
        E = bestE;
        if (E < rbest) { rbest = E; since = 0; } else since++;
        if (E < gbest) gbest = E;
        if (since > STALL) { restarts++; random_state(); make_S(fx, pr, S); E = energy(S, k); rbest = E; since = 0; }
    }
    printf("END mode tabu iters %ld restarts %ld best %d sols %d evals %lld\n", it, restarts, gbest, nsol, evals);
    free(tabuF); free(tabuP);
}

/* ---- simulated annealing: random single moves, Metropolis, geometric-style linear schedule ---- */
static void run_sa(double secs) {
    double T0 = getenv("T0") ? atof(getenv("T0")) : 2.0, T1 = getenv("T1") ? atof(getenv("T1")) : 0.05;
    time_t t0 = time(NULL); long it = 0, restarts = 0; int gbest = 1 << 30;
    random_state(); int S[8]; make_S(fx, pr, S); int E = energy(S, k); int rbest = E;
    double T = T0; long epoch = 0;
    while (1) {
        if ((it & 255) == 0) { double el = difftime(time(NULL), t0); if (el >= secs) break; T = T0 * pow(T1 / T0, el / secs); }
        it++;
        if (E == 0) {
            char tag[64]; snprintf(tag, sizeof tag, "sa_r%ld", restarts);
            make_S(fx, pr, S); check_zero(S, tag);
            if (nsol >= maxsol) break;
            restarts++; random_state(); make_S(fx, pr, S); E = energy(S, k); rbest = E; continue;
        }
        int nslot = (f - 1) + m; int s = rnd() % nslot;
        if (s < f - 1) {
            int i = s, old = fx[i], c; do c = rnd() % nF; while (usedF[c]);
            usedF[old] = 0; usedF[c] = 1; fx[i] = c; make_S(fx, pr, S); int E2 = energy(S, k);
            if (E2 <= E || (double)(rnd() % 1000000) / 1e6 < exp((E - E2) / T)) { E = E2; }
            else { usedF[c] = 0; usedF[old] = 1; fx[i] = old; }
        } else {
            int j = s - (f - 1), old = pr[j], q; do q = rnd() % nP; while (usedP[q]);
            usedP[old] = 0; usedP[q] = 1; pr[j] = q; make_S(fx, pr, S); int E2 = energy(S, k);
            if (E2 <= E || (double)(rnd() % 1000000) / 1e6 < exp((E - E2) / T)) { E = E2; }
            else { usedP[q] = 0; usedP[old] = 1; pr[j] = old; }
        }
        if (E < rbest) rbest = E;
        if (E < gbest) gbest = E;
        epoch++;
    }
    printf("END mode sa iters %ld restarts %ld best %d sols %d evals %lld\n", it, restarts, gbest, nsol, evals);
}

int main(int argc, char **argv) {
    if (argc < 5) { fprintf(stderr, "usage: anneal FILE.ht ALPHA F M\n"); return 2; }
    int a = atoi(argv[2]); f = atoi(argv[3]); m = atoi(argv[4]); k = f + 2 * m;
    if (k != 7) { fprintf(stderr, "need F + 2M = 7\n"); return 2; }
    edges_out = getenv("EDGES");
    double secs = getenv("SECS") ? atof(getenv("SECS")) : 60; int seed = getenv("SEED") ? atoi(getenv("SEED")) : 1;
    if (getenv("MAXSOL")) maxsol = atoi(getenv("MAXSOL"));
    if (getenv("TEN")) TEN = atoi(getenv("TEN"));
    if (getenv("STALL")) STALL = atoi(getenv("STALL"));
    load(argv[1]);
    if (a < 0 || a >= nal) { fprintf(stderr, "bad ALPHA index (nal=%d)\n", nal); return 2; }
    if (alp[a] != 1 && alp[a] != 2) { fprintf(stderr, "ALPHA %d has order %d: need 1 or 2\n", a, alp[a]); return 2; }
    /* psi(x) = beta(x)^-1 */
    psi = malloc(sizeof(int) * n);
    for (int i = 0; i < n; i++) psi[i] = inv[aperm[a][i]];
    for (int i = 0; i < n; i++) if (psi[psi[i]] != i) { fprintf(stderr, "psi is not an involution\n"); return 2; }
    Fl = malloc(sizeof(int) * n); Pr = malloc(sizeof(int) * 2 * n); nF = 0; nP = 0;
    for (int i = 1; i < n; i++) { if (psi[i] == i) Fl[nF++] = i; else if (i < psi[i]) { Pr[nP][0] = i; Pr[nP][1] = psi[i]; nP++; } }
    usedF = calloc(nF + 1, 1); usedP = calloc(nP + 1, 1);
    printf("GROUP %s n %d ninv %d alpha %d fixed_nonid %d pairs %d type f %d m %d\n", argv[1], n, ninv, a, nF, nP, f, m);
    fflush(stdout);
    if (f - 1 > nF || m > nP) { printf("END infeasible\n"); return 0; }
    srand(0); rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 20; i++) rnd();
    const char *mode = getenv("MODE") ? getenv("MODE") : "tabu";
    if (getenv("INIT")) {  /* calibration: start from a given S (element indices), must be psi-invariant */
        int S0[8], c = 0; char *p = getenv("INIT"); int x, nread;
        while (c < 7 && sscanf(p, "%d%n", &x, &nread) == 1) { S0[c++] = x; p += nread; }
        /* map elements to slots */
        clear_state(); int fi = 0, pi = 0;
        for (int i = 1; i < 7; i++) {
            int x0 = S0[i];
            if (psi[x0] == x0) { int idx = -1; for (int t = 0; t < nF; t++) if (Fl[t] == x0) idx = t; if (idx < 0 || fi >= f - 1) { printf("END bad INIT\n"); return 0; } fx[fi++] = idx; usedF[idx] = 1; }
        }
        for (int i = 1; i < 7; i++) {
            int x0 = S0[i];
            if (psi[x0] != x0 && x0 < psi[x0]) { int idx = -1; for (int t = 0; t < nP; t++) if (Pr[t][0] == x0) idx = t; if (idx < 0 || pi >= m) { printf("END bad INIT\n"); return 0; } pr[pi++] = idx; usedP[idx] = 1; }
        }
        int SS[8]; make_S(fx, pr, SS);
        printf("INIT energy %d\n", energy(SS, k)); fflush(stdout);
    }
    if (!strcmp(mode, "sa")) run_sa(secs); else run_tabu(secs);
    return 0;
}
