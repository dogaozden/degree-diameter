/* omega_symanneal.c (table-audit): search for a labelling of Omega H(q) (omega_model.h) with diameter <= D among
   labellings with two symmetries:
   - Z_5: the 5 copies of a block carry the same labelling (then copy 5B+i -> 5B+i+1, hub (t,k) -> (t,k+1) is an
     automorphism);
   - G = <g>, g an automorphism of H(q) acting semiregularly (orbits of size m) on points and on lines (hex_aut.py):
     rows = base points, and P_B(g t) = g P_B(t), L_B(g t) = g L_B(t), so g acting on every copy and on the rows is
     an automorphism.
   Parameters per block B and orbit s (rep p_s; row t = g^j p_s):  P_B(t) = g^(j + eP) p_(piP(s)),
   L_B(t) = g^(j + eL) l_(piL(s)).  Block 0 has P = identity.  Under both symmetries every vertex is equivalent to
   a hub (p_s,0) or (p_s,0bar), or a point p_s / line l_s of copy 5B, so BFS from those 2r(alpha+1) vertices decides
   the diameter exactly (the final graph is re-checked independently anyway).
   Cost = number of (source, vertex) pairs at distance > D.  Moves: change one exponent, swap two orbits.
   Env ZMODE=2: Z_5 acts with a row twist psi (G-equivariant, psi^5 = 1, orbits of psi on G-orbits are 5-cycles):
   copy 5B+i marks rows by P_B(psi^i(t)), so the 5 copies of a block differ; rotation (copy +1, hub (t,k)->(psi t,k+1))
   is an automorphism and the sources are the same 2r(alpha+1) as for the plain Z_5.  HUBONLY=1: score from hub sources
   only (a final check over all sources is printed).
   Env NOZ5=1: drop the Z_5 symmetry (all 5*alpha copies get their own marking; sources 10r(alpha+1)).
   usage: omega_symanneal HEX AUT TYPES INNER D SECONDS SEED OUTPREFIX [T0]
   AUT: hex_aut.py output (first line used); "none" = trivial group (m = 1, plain Z_5-symmetric search).
   Writes OUTPREFIX.lab (full labelling, omega_model.h format) whenever the best cost improves. */
#include "omega_model.h"
#include <math.h>
#include <time.h>

static uint64_t rs = 0x9E3779B97F4A7C15ULL;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int n, m, r, A, K, Z5 = 1, *psinv; /* psinv[i*n + t] = psi^-i (t) */
static int *orbP, *orbL, *sP, *jP;   /* orbP[s*m+j] = g^j p_s; sP[x], jP[x]: orbit and exponent of point x */
static int *piP, *eP, *piL, *eL;      /* [B*r + s] */
static Omega o;
static void fill(void) {
    for (int B = 0; B < K; B++) for (int t = 0; t < n; t++) {
        int s = sP[t], j = jP[t];
        int pp = orbP[piP[B * r + s] * m + (j + eP[B * r + s]) % m];
        int ll = orbL[piL[B * r + s] * m + (j + eL[B * r + s]) % m];
        if (Z5 == 1) for (int i = 0; i < 5; i++) { o.P[(long)(5 * B + i) * n + t] = pp; o.L[(long)(5 * B + i) * n + t] = ll; }
        else if (Z5 == 0) { o.P[(long)B * n + t] = pp; o.L[(long)B * n + t] = ll; }
        else for (int i = 0; i < 5; i++) { int u = psinv[i * n + t]; o.P[(long)(5 * B + i) * n + u] = pp; o.L[(long)(5 * B + i) * n + u] = ll; }
    }
}
/* c8 wildcard: smooth "excess" cost.  bad = pairs at distance > D (the score); ex = sum over pairs of max(0, dist - D),
   with BFS run past D up to D+CAPX levels (unreached pairs count CAPX+1 each).  The annealer minimises ex. */
#define CAPX 0
typedef struct { int B, w, s1, s2, kind, sv1, sv2, ev1, ev2; } Mv;
static int propose(Mv *mv) {   /* random single move on one block/orbit pair; returns 0 if no-op */
    mv->B = rnd() % K; mv->w = rnd() % 2; if (mv->B == 0 && mv->w == 0) mv->w = 1;
    int *pi = mv->w ? piL : piP, *e = mv->w ? eL : eP, B = mv->B;
    mv->s1 = rnd() % r; mv->s2 = rnd() % r; mv->kind = rnd() % 2;
    int s1 = mv->s1, s2 = mv->s2;
    mv->sv1 = pi[B * r + s1]; mv->sv2 = pi[B * r + s2]; mv->ev1 = e[B * r + s1]; mv->ev2 = e[B * r + s2];
    if (mv->kind == 0 || r == 1) { if (m == 1) return 0; e[B * r + s1] = rnd() % m; }
    else { if (s1 == s2) return 0; pi[B * r + s1] = mv->sv2; pi[B * r + s2] = mv->sv1; e[B * r + s1] = mv->ev2; e[B * r + s2] = mv->ev1; }
    return 1;
}
static void unmove(const Mv *mv) {
    int *pi = mv->w ? piL : piP, *e = mv->w ? eL : eP, B = mv->B;
    pi[B * r + mv->s1] = mv->sv1; pi[B * r + mv->s2] = mv->sv2; e[B * r + mv->s1] = mv->ev1; e[B * r + mv->s2] = mv->ev2;
}
static void om_far2(const Omega *o, const long *src, int ns, int D, long *bad_out, long *ex_out) {
    long NV = o->NV, bad = 0, ex = 0; uint64_t *vis = malloc(8 * NV), *fr = malloc(8 * NV), *nx = malloc(8 * NV);
    for (int s0 = 0; s0 < ns; s0 += 64) {
        int k = ns - s0 < 64 ? ns - s0 : 64; uint64_t full = k == 64 ? ~0ULL : ((1ULL << k) - 1);
        memset(vis, 0, 8 * NV); memset(fr, 0, 8 * NV);
        for (int i = 0; i < k; i++) { vis[src[s0 + i]] |= 1ULL << i; fr[src[s0 + i]] |= 1ULL << i; }
        int dist = 0;
        for (;;) {
            long newc = 0;
            for (long x = 0; x < NV; x++) { uint64_t acc = 0; const int *a = o->adj + x * o->maxd;
                for (int j = 0; j < o->deg[x]; j++) acc |= fr[a[j]];
                nx[x] = acc & ~vis[x]; newc += __builtin_popcountll(nx[x]); }
            if (!newc) break;
            dist++;
            if (dist > D) { bad += newc; ex += (long)(dist - D) * newc; }
            for (long x = 0; x < NV; x++) vis[x] |= nx[x];
            uint64_t *tt = fr; fr = nx; nx = tt;
            if (dist >= D + CAPX) break;
        }
        for (long x = 0; x < NV; x++) { long u = __builtin_popcountll(~vis[x] & full); bad += u; ex += (long)(CAPX + 1) * u; }
    }
    free(vis); free(fr); free(nx); *bad_out = bad; *ex_out = ex;
}
int main(int argc, char **argv) {
    if (argc < 9) { fprintf(stderr, "usage: omega_symanneal HEX AUT TYPES INNER D SECONDS SEED OUTPREFIX [T0]\n"); return 2; }
    if (om_load_hex(&o, argv[1])) return 2;
    om_alloc(&o, argv[3], argv[4]); n = o.n; A = o.A;
    int D = atoi(argv[5]); double secs = atof(argv[6]); rs ^= (uint64_t)atol(argv[7]) * 0x2545F4914F6CDD1DULL;
    for (int i = 0; i < 10; i++) rnd();
    const char *pre = argv[8]; double T0 = argc > 9 ? atof(argv[9]) : 2.0;
    int *g = malloc(sizeof(int) * 2 * n);
    if (!strcmp(argv[2], "none")) for (int i = 0; i < 2 * n; i++) g[i] = i;
    else { FILE *f = fopen(argv[2], "r"); for (int i = 0; i < 2 * n; i++) if (fscanf(f, "%d", &g[i]) != 1) return 2; fclose(f); }
    /* orbits */
    m = 1; { int x = g[0]; while (x != 0) { x = g[x]; m++; } }
    r = n / m; orbP = malloc(sizeof(int) * n); orbL = malloc(sizeof(int) * n); sP = malloc(sizeof(int) * n); jP = malloc(sizeof(int) * n);
    int *sL = malloc(sizeof(int) * n), *jL = malloc(sizeof(int) * n);
    for (int w = 0; w < 2; w++) {
        int *orb = w ? orbL : orbP, *so = w ? sL : sP, *jo = w ? jL : jP, ns = 0;
        for (int x = 0; x < n; x++) so[x] = -1;
        for (int x = 0; x < n; x++) if (so[x] < 0) {
            int y = x, j = 0;
            do { if (j >= m) { fprintf(stderr, "not semiregular\n"); return 2; } so[y] = ns; jo[y] = j; orb[ns * m + j] = y; j++; y = g[w * n + y] - w * n; } while (y != x);
            if (j != m) { fprintf(stderr, "not semiregular (orbit %d)\n", j); return 2; }
            ns++;
        }
        if (ns != r) { fprintf(stderr, "orbit count\n"); return 2; }
    }
    if (getenv("NOZ5")) Z5 = 0;
    if (getenv("ZMODE")) Z5 = atoi(getenv("ZMODE"));
    if (Z5 == 2) {   /* psi(g^j p_s) = g^(j + f(s)) p_tau(s), tau = 5-cycles on orbits (fixed orbits left fixed), cycle sums of f = 0 mod m */
        int *tau = malloc(sizeof(int) * r), *f = malloc(sizeof(int) * r), *ord = malloc(sizeof(int) * r);
        for (int s = 0; s < r; s++) { ord[s] = s; tau[s] = s; f[s] = 0; }
        for (int s = r - 1; s > 0; s--) { int u = rnd() % (s + 1); int tt = ord[s]; ord[s] = ord[u]; ord[u] = tt; }
        for (int b = 0; b + 5 <= r; b += 5) { int sum = 0;
            for (int i = 0; i < 5; i++) { tau[ord[b + i]] = ord[b + (i + 1) % 5]; if (i < 4) { f[ord[b + i]] = rnd() % m; sum += f[ord[b + i]]; } }
            f[ord[b + 4]] = ((-sum) % m + m) % m; }
        int *psi = malloc(sizeof(int) * n); psinv = malloc(sizeof(int) * 5 * n);
        for (int t = 0; t < n; t++) psi[t] = orbP[tau[sP[t]] * m + (jP[t] + f[sP[t]]) % m];
        for (int t = 0; t < n; t++) psinv[t] = t;
        for (int i = 1; i < 5; i++) for (int t = 0; t < n; t++) psinv[i * n + psi[t]] = psinv[(i - 1) * n + t];
        for (int t = 0; t < n; t++) { int u = t; for (int i = 0; i < 5; i++) u = psi[u]; if (u != t) { fprintf(stderr, "psi^5 != 1\n"); return 2; } }
    }
    K = Z5 ? A : 5 * A; int hubonly = getenv("HUBONLY") != NULL;
    fprintf(stderr, "n=%d m=%d r=%d alpha=%d markings=%d\n", n, m, r, A, K);
    piP = malloc(sizeof(int) * K * r); eP = malloc(sizeof(int) * K * r); piL = malloc(sizeof(int) * K * r); eL = malloc(sizeof(int) * K * r);
    for (int B = 0; B < K; B++) {
        for (int s = 0; s < r; s++) { piP[B * r + s] = s; piL[B * r + s] = s; eP[B * r + s] = 0; eL[B * r + s] = 0; }
        if (B > 0) for (int s = r - 1; s > 0; s--) { int u = rnd() % (s + 1); int tt = piP[B * r + s]; piP[B * r + s] = piP[B * r + u]; piP[B * r + u] = tt; }
        for (int s = r - 1; s > 0; s--) { int u = rnd() % (s + 1); int tt = piL[B * r + s]; piL[B * r + s] = piL[B * r + u]; piL[B * r + u] = tt; }
        for (int s = 0; s < r; s++) { if (B > 0) eP[B * r + s] = rnd() % m; eL[B * r + s] = rnd() % m; }
    }
    long ns = 0, *src = malloc(sizeof(long) * (10 * r * (A + 1)));
    for (int s = 0; s < r; s++) { int p = orbP[s * m]; for (int k = 0; k < (Z5 ? 1 : 5); k++) { src[ns++] = om_hub(&o, p, 0, k); src[ns++] = om_hub(&o, p, 1, k); } }
    long nhub = ns;
    for (int c = 0; c < 5 * A; c += Z5 ? 5 : 1) for (int s = 0; s < r; s++) { src[ns++] = (long)c * 2 * n + orbP[s * m]; src[ns++] = (long)c * 2 * n + n + orbL[s * m]; }
    long nall = ns; if (hubonly) ns = nhub;
    fill(); om_build(&o);
    long bad0 = 0, ex0 = 0; om_far2(&o, src, (int)ns, D, &bad0, &ex0);
    long cur = ex0, best = bad0;
    fprintf(stderr, "start bad %ld excess %ld (sources %ld)\n", bad0, ex0, ns);
    char path[512]; snprintf(path, sizeof path, "%s.lab", pre);
    /* calibration: median |delta excess| of 40 random moves from the start sets the temperature scale */
    double dl[40]; int nd = 0;
    for (int p = 0; p < 120 && nd < 40; p++) {
        Mv mv; if (!propose(&mv)) continue;
        fill(); om_build(&o); long b = 0, x = 0; om_far2(&o, src, (int)ns, D, &b, &x);
        if (x != cur) dl[nd++] = fabs((double)(x - cur));
        unmove(&mv);
    }
    for (int i = 1; i < nd; i++) { double v = dl[i]; int j = i - 1; while (j >= 0 && dl[j] > v) { dl[j + 1] = dl[j]; j--; } dl[j + 1] = v; }
    double med = nd ? dl[nd / 2] : 100.0;
    double fac = argc > 9 ? atof(argv[9]) : 1.0;
    double TS = fac * med, TE = TS / 300.0; if (TS <= 0) TS = 1.0;
    fprintf(stderr, "calibration: %d nonzero deltas, median %.1f, T start %.2f end %.4f\n", nd, med, TS, TE);
    time_t t0 = time(NULL); long it = 0, acc = 0;
    while (best > 0 && difftime(time(NULL), t0) < secs) {
        Mv mv; it++;
        if (!propose(&mv)) continue;
        fill(); om_build(&o);
        long b = 0, x = 0; om_far2(&o, src, (int)ns, D, &b, &x);
        if (b < best) {   /* o holds this proposal's labelling: save it if it is the best score so far */
            best = b; fprintf(stderr, "it %ld t %.0f bad %ld excess %ld\n", it, difftime(time(NULL), t0), b, x);
            om_write_lab(&o, path);
        }
        double frac = difftime(time(NULL), t0) / secs; double T = TS * pow(TE / TS, frac);
        double dd = (double)(x - cur);
        if (dd <= 0 || exp(-dd / T) * 4294967296.0 > (double)(rnd() & 0xffffffff)) { cur = x; acc++; }
        else unmove(&mv);
    }
    fill(); om_build(&o); long fin = om_far(&o, src, (int)nall, D, NULL, NULL, NULL);
    printf("final check over all %ld orbit representatives: far pairs %ld\n", nall, fin);
    printf("RESULT types=%s inner=%s m=%d D=%d best=%ld iters=%ld accepted=%ld lab=%s\n", o.types, o.inner, m, D, best, it, acc, path);
    return 0;
}
