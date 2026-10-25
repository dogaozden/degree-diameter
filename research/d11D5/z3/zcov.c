/* zcov.c: Z_a "covering cocycles" on the incidence graph of W(q).
   A labelling nu: flags -> Z_a (voltage point -> line).  For an opposite point pair (P,Q) the q+1 geodesics
   P-L1-R-L2-Q have voltages nu(P,L1) - nu(R,L1) + nu(R,L2) - nu(Q,L2); for an opposite line pair (L,M) the q+1
   geodesics L-P1-K-P2-M have -nu(P1,L) + nu(P1,K) - nu(P2,K) + nu(P2,M).  The pair is covered if its geodesic
   voltages take all a values.  cost = sum over opposite pairs (points and lines) of the number of missing values.
   With a = 3 and cost 0, W(q) + three parallel copies of any matching, lifted by Z_9 (nu -> 3nu, matching
   copies 1, 4, 7), has diameter <= 5 (research/d10D7/DM_D5.md: the only open case is coset 0 of opposite pairs).
   Input: gq/gq_q{q}.bin from gqgen.c (flag index = line*(q+1) + k, k-th point of the line).
   usage: zcov q a   env: SEED, SECS, T0, T1, IN (label file: one value per flag), OUT, SCORE=1 (score IN only),
          ONLYPTS=1 (ignore line pairs)
*/
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <time.h>
static uint64_t rs = 88172645463325252ULL;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline double urand(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }
int q, a, N, L, Q1, F;
int *pl;            /* L x Q1 points of each line */
int *lp;            /* N x Q1 lines through each point */
int *flag_pl;       /* N*Q1: flag index of (point, its k-th line) */
int *colline;       /* N x N: line through two collinear points, -1 if not collinear (or equal) */
int *concpt;        /* L x L: point on two concurrent lines */
int npairs;         /* pairs (points then lines) */
int ngeo;           /* npairs * Q1 */
int *gf;            /* ngeo x 4 flags */
int8_t *gs;         /* ngeo x 4 signs */
int *occ, *ooff;    /* flag -> list of (geo*4+slot) */
uint8_t *val;       /* geodesic voltage */
uint8_t *cnt;       /* npairs x a */
uint8_t *nu;
static int missing(int p) { int m = 0; for (int v = 0; v < a; v++) if (!cnt[p * a + v]) m++; return m; }
int main(int argc, char **argv) {
    q = atoi(argv[1]); a = atoi(argv[2]); Q1 = q + 1;
    if (getenv("SEED")) { rs ^= (uint64_t)atoll(getenv("SEED")) * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 20; i++) rnd(); }
    char fn[64]; sprintf(fn, "gq/gq_q%d.bin", q); FILE *f = fopen(fn, "rb"); int32_t h[3];
    if (!f || fread(h, 4, 3, f) != 3) { fprintf(stderr, "no %s\n", fn); return 1; }
    N = h[1]; L = h[2]; pl = malloc(4L * L * Q1); if (fread(pl, 4, (size_t)L * Q1, f) != (size_t)L * Q1) return 1; fclose(f);
    F = L * Q1; lp = malloc(4L * N * Q1); flag_pl = malloc(4L * N * Q1); int *dg = calloc(N, 4);
    for (int l = 0; l < L; l++) for (int k = 0; k < Q1; k++) { int p = pl[l * Q1 + k]; lp[p * Q1 + dg[p]] = l; flag_pl[p * Q1 + dg[p]] = l * Q1 + k; dg[p]++; }
    colline = malloc(4L * N * N); for (long i = 0; i < (long)N * N; i++) colline[i] = -1;
    for (int l = 0; l < L; l++) for (int i = 0; i < Q1; i++) for (int j = 0; j < Q1; j++) if (i != j) colline[(long)pl[l * Q1 + i] * N + pl[l * Q1 + j]] = l;
    concpt = malloc(4L * L * L); for (long i = 0; i < (long)L * L; i++) concpt[i] = -1;
    for (int p = 0; p < N; p++) for (int i = 0; i < Q1; i++) for (int j = 0; j < Q1; j++) if (i != j) concpt[(long)lp[p * Q1 + i] * L + lp[p * Q1 + j]] = p;
    /* flag index lookup (point, line) */
    #define FL(p, l) flagidx(p, l)
    int onlypts = getenv("ONLYPTS") != NULL;
    long cap = (long)N * N / 2 + (onlypts ? 0 : (long)L * L / 2) + 16;
    gf = malloc(4L * cap * Q1 * 4); gs = malloc(cap * Q1 * 4);
    npairs = 0; long g = 0;
    /* helper: flag of point p on line l */
    int *fpl = malloc(4L * N * Q1);  /* not used */
    (void)fpl;
    for (int P = 0; P < N; P++) for (int Q = P + 1; Q < N; Q++) {
        if (colline[(long)P * N + Q] >= 0) continue;
        for (int i = 0; i < Q1; i++) {
            int L1 = lp[P * Q1 + i]; int R = -1;
            for (int k = 0; k < Q1; k++) { int r = pl[L1 * Q1 + k]; if (r != P && colline[(long)r * N + Q] >= 0) { R = r; break; } }
            int L2 = colline[(long)R * N + Q];
            int fs[4], pts[4] = {P, R, R, Q}, lns[4] = {L1, L1, L2, L2};
            for (int s = 0; s < 4; s++) { int ff = -1; for (int k = 0; k < Q1; k++) if (pl[lns[s] * Q1 + k] == pts[s]) ff = lns[s] * Q1 + k; fs[s] = ff; }
            for (int s = 0; s < 4; s++) { gf[g * 4 + s] = fs[s]; gs[g * 4 + s] = (s & 1) ? -1 : 1; }
            g++;
        }
        npairs++;
    }
    int nptpairs = npairs;
    if (!onlypts) for (int A = 0; A < L; A++) for (int B = A + 1; B < L; B++) {
        if (concpt[(long)A * L + B] >= 0) continue;
        for (int i = 0; i < Q1; i++) {
            int P1 = pl[A * Q1 + i]; int K = -1, P2 = -1;
            for (int k = 0; k < Q1; k++) { int l = lp[P1 * Q1 + k]; if (l != A && concpt[(long)l * L + B] >= 0) { K = l; break; } }
            P2 = concpt[(long)K * L + B];
            int pts[4] = {P1, P1, P2, P2}, lns[4] = {A, K, K, B}, sg[4] = {-1, 1, -1, 1};
            for (int s = 0; s < 4; s++) { int ff = -1; for (int k = 0; k < Q1; k++) if (pl[lns[s] * Q1 + k] == pts[s]) ff = lns[s] * Q1 + k; gf[g * 4 + s] = ff; gs[g * 4 + s] = sg[s]; }
            g++;
        }
        npairs++;
    }
    ngeo = g;
    int *co = calloc(F, 4); for (long e = 0; e < 4L * ngeo; e++) co[gf[e]]++;
    ooff = malloc(4L * (F + 1)); ooff[0] = 0; for (int i = 0; i < F; i++) ooff[i + 1] = ooff[i] + co[i];
    occ = malloc(4L * ooff[F]); memset(co, 0, 4L * F); for (long e = 0; e < 4L * ngeo; e++) occ[ooff[gf[e]] + co[gf[e]]++] = e;
    nu = malloc(F);
    if (getenv("IN")) { FILE *g2 = fopen(getenv("IN"), "r"); for (int i = 0; i < F; i++) { int v; if (fscanf(g2, "%d", &v) != 1) { fprintf(stderr, "short IN\n"); return 1; } nu[i] = ((v % a) + a) % a; } fclose(g2); }
    else for (int i = 0; i < F; i++) nu[i] = rnd() % a;
    val = malloc(ngeo); cnt = calloc((size_t)npairs * a, 1);
    long cost = 0;
    for (long e = 0; e < ngeo; e++) { int s = 0; for (int k = 0; k < 4; k++) s += gs[e * 4 + k] * nu[gf[e * 4 + k]]; val[e] = ((s % a) + a) % a; cnt[(e / Q1) * a + val[e]]++; }
    long bp = 0, bl = 0; for (int p = 0; p < npairs; p++) { int m = missing(p); cost += m; if (m) { if (p < nptpairs) bp++; else bl++; } }
    printf("W(%d) a=%d flags=%d point pairs=%d line pairs=%d cost=%ld (bad point pairs %ld, line pairs %ld)\n", q, a, F, nptpairs, npairs - nptpairs, cost, bp, bl);
    if (getenv("SCORE")) return 0;
    double secs = getenv("SECS") ? atof(getenv("SECS")) : 60, T0 = getenv("T0") ? atof(getenv("T0")) : 1.0, T1 = getenv("T1") ? atof(getenv("T1")) : 0.05;
    long best = cost; uint8_t *bestnu = malloc(F); memcpy(bestnu, nu, F);
    int *tp = malloc(4L * ooff[F]); int8_t *dlt = malloc(ooff[F]);
    clock_t t0 = clock(); long it = 0; double T = T0;
    while (best > 0) {
        if ((it & 1023) == 0) { double el = (double)(clock() - t0) / CLOCKS_PER_SEC; if (el > secs) break; T = T0 * pow(T1 / T0, el / secs);
            if ((it & ((1 << 18) - 1)) == 0) { printf("t=%.0f it=%ld cost=%ld best=%ld T=%.3f\n", el, it, cost, best, T); fflush(stdout); } }
        it++;
        int fl = rnd() % F; int d = 1 + rnd() % (a - 1);
        /* apply tentatively */
        long dc = 0; int n = 0;
        for (int j = ooff[fl]; j < ooff[fl + 1]; j++) { int e = occ[j]; long ge = e / 4; int sgn = gs[e]; int p = ge / Q1;
            int ov = val[ge], nv = ((ov + sgn * d) % a + a) % a;
            int before = (cnt[p * a + ov] == 1) - 0; (void)before;
            int m0 = missing(p); cnt[p * a + ov]--; cnt[p * a + nv]++; int m1 = missing(p); dc += m1 - m0; val[ge] = nv; tp[n++] = j; }
        if (dc <= 0 || urand() < exp(-dc / T)) { nu[fl] = (nu[fl] + d) % a; cost += dc; if (cost < best) { best = cost; memcpy(bestnu, nu, F); } }
        else { for (int t = n - 1; t >= 0; t--) { int e = occ[tp[t]]; long ge = e / 4; int sgn = gs[e]; int p = ge / Q1; int nv = val[ge], ov = ((nv - sgn * d) % a + a) % a; cnt[p * a + nv]--; cnt[p * a + ov]++; val[ge] = ov; } }
    }
    printf("RESULT W(%d) a=%d best=%ld iters=%ld\n", q, a, best, it);
    if (getenv("OUT")) { FILE *g2 = fopen(getenv("OUT"), "w"); for (int i = 0; i < F; i++) fprintf(g2, "%d\n", bestnu[i]); fclose(g2); }
    return 0;
}
