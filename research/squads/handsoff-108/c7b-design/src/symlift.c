/* symlift.c (worker c7b): K-symmetric cyclic lifts of H(q) + J=2 matchings over Z_m, annealed on orbit variables.
 * K = <k> of prime order P acting FIXED-POINT-FREELY on points and lines (automorphisms of H(q), src/symgroup.py).
 * Symmetry: hexagon voltage constant on flag orbits, matching voltage constant on point orbits, and matching
 * sigma_t(k^j p) = k^j sigma_t(p). A matching is given by tau_t (point orbit -> line orbit, a permutation of the s
 * orbits) and offsets c_t[i] in Z_P: sigma_t(k^j rep_i) = k^(j + c_t[i]) rep'_{tau_t(i)}.
 * Cost = sum over the s orbit representatives of point sources of uncovered (line, g) pairs (walks of length 7,
 * exactly as hexeval); the full cost is P times that (orbits of size P) with dup penalty 100 per double edge.
 * Output: best state expanded to the lift3/hexeval format (IN= of hexeval re-checks it in full).
 * env: M (m), J fixed 2, ITERS, TEMP0, TEMP1, SEED, OUT, KFILE (permutation of 2N vertices, one line),
 *      TMAX (seconds, optional), TOL (stop when units <= TOL).
 * usage: symlift HEXBIN */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <time.h>

static int q, N, Q1, V, m, P, J = 2, s, Dg, LANES;
static int32_t *pl;
static int *kperm;                 /* K on 2N vertices */
static int *po, *pk, *prep;        /* point orbit id, position (K^pk rep), rep point */
static int *lo, *lk, *lrep;        /* line orbit id, position, rep line (0..N-1) */
static int *Lpow;                  /* Lpow[k*s + j] = line index of K^k(lrep[j]) */
static int *fo, *forb_rep, F;      /* flag id = l*Q1+k; flag orbit id; number of flag orbits */
static int *hvo;                   /* flag-orbit voltages */
static int *mvo;                   /* J x s matching voltages per point orbit */
static int *tau;                   /* J x s */
static int *cof;                   /* J x s offsets */
static int *sig, *mv, *hv;         /* expanded */
static int *inn, *inw;
static uint64_t Mlo[64], Mhi[64], LaneMask;
static uint64_t *Wa, *Wb;
static uint64_t rs = 88172645463325252ULL;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline int rndi(int n) { return (int)(rnd() % (uint64_t)n); }
static inline uint64_t rot(uint64_t R, int g) {
    if (!g) return R;
    return ((R & Mlo[g]) << g) | ((R & Mhi[g]) >> (m - g));
}
static void setup_masks(void) {
    LaneMask = 0; for (int k = 0; k < LANES; k++) for (int h = 0; h < m; h++) LaneMask |= 1ULL << (k * m + h);
    for (int g = 0; g < m; g++) { Mlo[g] = Mhi[g] = 0;
        for (int k = 0; k < LANES; k++) for (int h = 0; h < m; h++) {
            uint64_t b = 1ULL << (k * m + h);
            if (h < m - g) Mlo[g] |= b; else Mhi[g] |= b; } }
}
static void expand_and_build(void) {
    for (int t = 0; t < J; t++) for (int p = 0; p < N; p++) {
        int i = po[p], k = pk[p];
        sig[t * N + p] = Lpow[((k + cof[t * s + i]) % P) * s + tau[t * s + i]];
        mv[t * N + p] = mvo[t * s + i];
    }
    for (int f = 0; f < N * Q1; f++) hv[f] = hvo[fo[f]];
    /* in-arcs: point p (node p) and line l (node N+l), Dg = Q1 + J */
    int *cnt = calloc(2 * N, sizeof(int));
    for (int l = 0; l < N; l++) for (int k = 0; k < Q1; k++) {
        int p = pl[l * Q1 + k], w = hv[l * Q1 + k];
        inn[(N + l) * Dg + cnt[N + l]] = p; inw[(N + l) * Dg + cnt[N + l]] = w; cnt[N + l]++;
        inn[p * Dg + cnt[p]] = N + l; inw[p * Dg + cnt[p]] = (m - w) % m; cnt[p]++;
    }
    for (int t = 0; t < J; t++) for (int p = 0; p < N; p++) {
        int l = sig[t * N + p], w = mv[t * N + p];
        inn[(N + l) * Dg + cnt[N + l]] = p; inw[(N + l) * Dg + cnt[N + l]] = w; cnt[N + l]++;
        inn[p * Dg + cnt[p]] = N + l; inw[p * Dg + cnt[p]] = (m - w) % m; cnt[p]++;
    }
    free(cnt);
}
/* number of parallel pairs at the representative points */
static long dup_reps(void) {
    long d = 0;
    for (int i = 0; i < s; i++) {
        int p = prep[i];
        for (int a = 0; a < Dg; a++) for (int b = a + 1; b < Dg; b++)
            if (inn[p * Dg + a] == inn[p * Dg + b] && inw[p * Dg + a] == inw[p * Dg + b]) d++;
    }
    return d;
}
/* uncovered (line,g) pairs summed over the orbit representatives */
static long cost_reps_cap(long cap) {
    long c = 0;
    for (int b0 = 0; b0 < s; b0 += LANES) {
        if (c > cap) return c;   /* early abort: partial sums only grow */
        int ns = s - b0 < LANES ? s - b0 : LANES;
        memset(Wa, 0, sizeof(uint64_t) * V);
        for (int k = 0; k < ns; k++) Wa[prep[b0 + k]] |= 1ULL << (k * m);
        for (int step = 1; step <= 7; step++) {
            for (int y = 0; y < V; y++) {
                uint64_t o = 0; const int *a = inn + (size_t)y * Dg, *w = inw + (size_t)y * Dg;
                for (int i = 0; i < Dg; i++) { uint64_t R = Wa[a[i]]; if (R) o |= rot(R, w[i]); }
                Wb[y] = o;
            }
            uint64_t *t = Wa; Wa = Wb; Wb = t;
        }
        for (int l = 0; l < N; l++) {
            uint64_t R = Wa[N + l];
            for (int k = 0; k < ns; k++) {
                uint64_t lane = (R >> (k * m)) & ((m == 64) ? ~0ULL : ((1ULL << m) - 1));
                c += m - __builtin_popcountll(lane);
            }
        }
    }
    return c;
}
static long cost_reps(void) { return cost_reps_cap(1L << 60); }
static void save(const char *fn, long cost) {
    FILE *f = fopen(fn, "w");
    fprintf(f, "%d %d %d %d %ld\ncyc %d\n", q, J, m, 8, cost, m);
    for (int t = 0; t < J; t++) { for (int p = 0; p < N; p++) fprintf(f, "%d ", sig[t * N + p]); fprintf(f, "\n"); }
    for (int t = 0; t < J; t++) { for (int p = 0; p < N; p++) fprintf(f, "%d ", mv[t * N + p]); fprintf(f, "\n"); }
    for (int i = 0; i < N * Q1; i++) fprintf(f, "%d ", hv[i]); fprintf(f, "\n");
    fclose(f);
}
int main(int argc, char **argv) {
    if (argc < 2) { fprintf(stderr, "usage: symlift HEXBIN\n"); return 1; }
    FILE *fh = fopen(argv[1], "rb"); int32_t h[3];
    if (!fh || fread(h, 4, 3, fh) != 3) { fprintf(stderr, "no hex\n"); return 1; }
    q = h[0]; N = h[1]; Q1 = q + 1; V = 2 * N; Dg = Q1 + J;
    pl = malloc(4L * N * Q1); if (fread(pl, 4, (size_t)N * Q1, fh) != (size_t)N * Q1) return 1; fclose(fh);
    m = getenv("M") ? atoi(getenv("M")) : 24;
    LANES = 64 / m; if (LANES < 1) { fprintf(stderr, "m too big\n"); return 1; }
    setup_masks();
    /* K */
    kperm = malloc(sizeof(int) * V);
    FILE *fk = fopen(getenv("KFILE") ? getenv("KFILE") : "K.txt", "r");
    for (int i = 0; i < V; i++) if (fscanf(fk, "%d", &kperm[i]) != 1) { fprintf(stderr, "bad K\n"); return 1; }
    fclose(fk);
    /* order P of K: smallest P>0 with K^P = id (prime in our use) */
    P = 0; { int *cur = malloc(sizeof(int) * V); for (int i = 0; i < V; i++) cur[i] = i;
        for (int e = 1; e <= V; e++) { int *nx = malloc(sizeof(int) * V); for (int i = 0; i < V; i++) nx[i] = kperm[cur[i]];
            free(cur); cur = nx; int id = 1; for (int i = 0; i < V; i++) if (cur[i] != i) { id = 0; break; }
            if (id) { P = e; break; } }
        free(cur); }
    /* orbits of points and lines */
    po = malloc(sizeof(int) * N); pk = malloc(sizeof(int) * N); lo = malloc(sizeof(int) * N); lk = malloc(sizeof(int) * N);
    for (int i = 0; i < N; i++) po[i] = lo[i] = -1;
    prep = malloc(sizeof(int) * N); lrep = malloc(sizeof(int) * N);
    s = 0;
    for (int p = 0; p < N; p++) if (po[p] < 0) {
        int x = p, k = 0;
        do { po[x] = s; pk[x] = k; x = kperm[x]; k++; } while (x != p && k <= P);
        if (k != P) { fprintf(stderr, "point orbit of size %d != P %d: K not semiregular\n", k, P); return 1; }
        prep[s] = p; s++;
    }
    int sl = 0;
    for (int l = 0; l < N; l++) if (lo[l] < 0) {
        int x = N + l, k = 0;
        do { lo[x - N] = sl; lk[x - N] = k; x = kperm[x]; k++; } while (x != N + l && k <= P);
        if (k != P) { fprintf(stderr, "line orbit size != P\n"); return 1; }
        lrep[sl] = l; sl++;
    }
    if (sl != s) { fprintf(stderr, "orbit counts differ\n"); return 1; }
    /* Lpow[k*s + j] = line index of K^k(lrep[j]) */
    Lpow = malloc(sizeof(int) * P * s);
    for (int j = 0; j < s; j++) { int x = N + lrep[j]; for (int k = 0; k < P; k++) { Lpow[k * s + j] = x - N; x = kperm[x]; } }
    /* flag orbits: flag f=(l,k) ~ (point pl, line l). K maps (p,l) to (Kp, Kl). */
    fo = malloc(sizeof(int) * N * Q1); for (int f = 0; f < N * Q1; f++) fo[f] = -1;
    int *flagof = malloc(sizeof(int) * (size_t)N * N); /* (line, point) -> flag, -1 if not incident */
    for (long i = 0; i < (long)N * N; i++) flagof[i] = -1;
    for (int l = 0; l < N; l++) for (int k = 0; k < Q1; k++) flagof[(long)l * N + pl[l * Q1 + k]] = l * Q1 + k;
    F = 0;
    for (int f = 0; f < N * Q1; f++) if (fo[f] < 0) {
        int l = f / Q1, p = pl[f];
        int ff = f;
        do { fo[ff] = F; int l2 = ff / Q1, p2 = pl[ff];
             int kp = kperm[p2], kl = kperm[N + l2] - N;
             ff = flagof[(long)kl * N + kp];
             if (ff < 0) { fprintf(stderr, "K not an automorphism\n"); return 1; }
        } while (fo[ff] < 0);
        if (fo[ff] != F) { fprintf(stderr, "flag orbit inconsistency\n"); return 1; }
        F++;
        (void)l; (void)p;
    }
    free(flagof);
    /* variables */
    hvo = malloc(sizeof(int) * F); mvo = malloc(sizeof(int) * J * s); tau = malloc(sizeof(int) * J * s); cof = malloc(sizeof(int) * J * s);
    sig = malloc(sizeof(int) * J * N); mv = malloc(sizeof(int) * J * N); hv = malloc(sizeof(int) * N * Q1);
    inn = malloc(sizeof(int) * (size_t)V * Dg); inw = malloc(sizeof(int) * (size_t)V * Dg);
    Wa = malloc(8L * V); Wb = malloc(8L * V);
    if (getenv("SEED")) rs ^= (uint64_t)atoll(getenv("SEED")) * 0x9E3779B97F4A7C15ULL;
    for (int i = 0; i < 10; i++) rnd();
    for (int i = 0; i < F; i++) hvo[i] = rndi(m);
    for (int t = 0; t < J; t++) {
        for (int i = 0; i < s; i++) { tau[t * s + i] = i; mvo[t * s + i] = rndi(m); cof[t * s + i] = rndi(P); }
        for (int i = s - 1; i > 0; i--) { int r = rndi(i + 1); int x = tau[t * s + i]; tau[t * s + i] = tau[t * s + r]; tau[t * s + r] = x; }
    }
    expand_and_build();
    long units = cost_reps(); long dups = dup_reps();
    long cur = units + 100 * dups, best = cur;
    long bestunits = units, bestdup = dups;
    char *out = getenv("OUT");
    if (out) save(out, P * units);
    long iters = getenv("ITERS") ? atol(getenv("ITERS")) : 0;
    double T0 = getenv("TEMP0") ? atof(getenv("TEMP0")) : 2.0, T1 = getenv("TEMP1") ? atof(getenv("TEMP1")) : 0.05;
    long tol = getenv("TOL") ? atol(getenv("TOL")) : 0;
    fprintf(stderr, "q=%d m=%d P=%d s=%d flag-orbits=%d initial units %ld dup %ld\n", q, m, P, s, F, units, dups);
    time_t t_start = time(NULL);
    long tmax = getenv("TMAX") ? atol(getenv("TMAX")) : 0;
    for (long it = 0; it < iters && best > tol; it++) {
        if (tmax && time(NULL) - t_start > tmax) break;
        double temp = T0 * pow(T1 / T0, (double)it / iters);
        int kind = rndi(4), t = rndi(J), a = 0, b = 0, olda = 0, oldb = 0;
        int *slot = NULL, *slot2 = NULL; int ov = 0, ov2 = 0;
        if (kind == 0) { a = rndi(F); slot = &hvo[a]; ov = *slot; int nv; do nv = rndi(m); while (nv == ov); *slot = nv; }
        else if (kind == 1) { a = rndi(s); slot = &mvo[t * s + a]; ov = *slot; int nv; do nv = rndi(m); while (nv == ov); *slot = nv; }
        else if (kind == 2) { a = rndi(s); slot = &cof[t * s + a]; ov = *slot; if (P > 1) { int nv; do nv = rndi(P); while (nv == ov); *slot = nv; } }
        else { a = rndi(s); b = rndi(s); if (a == b) continue;
            slot = &tau[t * s + a]; slot2 = &tau[t * s + b]; ov = *slot; ov2 = *slot2; *slot = ov2; *slot2 = ov; }
        expand_and_build();
        double u = (rnd() >> 11) * (1.0 / 9007199254740992.0);
        long cap = cur + (long)(-temp * log(u + 1e-300));
        dups = dup_reps();
        long ucap = cap - 100 * dups;
        units = (ucap < 0) ? ucap + 1 : cost_reps_cap(ucap);   /* exceeds ucap => reject */
        long nc = units + 100 * dups;
        if (ucap >= 0 && units <= ucap) {
            cur = nc;
            if (cur < best) {
                best = cur; bestunits = units; bestdup = dups;
                fprintf(stderr, "it %ld temp %.3f best units %ld dup %ld (full cost %ld)\n", it, temp, bestunits, bestdup, P * bestunits);
                if (out && bestdup == 0) save(out, P * bestunits);
            }
        } else {
            if (kind == 3) { *slot = ov; *slot2 = ov2; }
            else *slot = ov;
            expand_and_build();
        }
    }
    printf("RESULT symlift q %d m %d P %d s %d units %ld dup %ld full_cost %ld\n", q, m, P, s, bestunits, bestdup, P * bestunits);
    return 0;
}
