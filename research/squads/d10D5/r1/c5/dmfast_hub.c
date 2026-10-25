/* dmfast_hub.c: research/d10D7/dmfast.c plus FREE="p1 p2 ..." (freed points: no matching jumps at p_i or at the
 * line sigma(p_i) when computing routes), for the hub construction in this folder (dmhub.c).  sigma should then be
 * kept fixed (SWAPP=0) since swaps would move the freed lines.  Original header follows.
 *
 * dmfast.c: fast annealer for the doubled-matching (DM) lift of GH(q).
 *
 * DM lift: base = GH(q) incidence graph + a matching sigma (point -> line) whose edges are doubled, voltages in
 * Z_6: 1 and 4 on the two copies of each matching edge, hexagon voltages nu in {0,3}.  Lift: 6*|GH(q)| vertices,
 * max degree q+3.  Every pair of lift vertices is within distance 7 except possibly sheets {0,3} of an OPPOSITE
 * same-colour pair (v,u) (hexagon distance 6), and those are covered iff
 *   (a) the q+1 hexagon geodesics from v to u do not all have the same nu-parity, or
 *   (b) a "route" exists: a walk of length 6 from v to u with jump-sum = 0 mod 3 and at least one jump
 *       (then both sheets 0 and 3 are reached, using the two parallel copies).
 * (Proof sketch in research/squads/cells/d10D7.md; lift2 with DM=1 checks the full lift exactly.)
 *
 * This program: R (route sets) from sigma by BFS in the Z_3 polygon-cover lift with a "jumped" flag; c(v,u) = number
 * of odd geodesics for every opposite same-colour pair (byte matrix); cost = #{unordered opposite pairs not in R with
 * c in {0, q+1}}.  Anneals nu by single flag flips with exact incremental updates (each flag lies on 6 q^5
 * geodesics).  sigma is fixed (from IN or random).
 * usage: dmfast q   env: SEED, ITERS, SECS, TEMP0, TEMP1, IN (lift2 DM solution file), OUT (lift2 DM solution file)
 *   BASE=<polygon file> NPOLY=<n> (default hex/hex_q{q}.bin, n = 6; gq/gq_q{q}.bin with NPOLY=4 for quadrangles,
 *   target diameter n+1 = 5); NOROUTE=1 ignores routes; SWAPP=p also anneals sigma; NUZERO=1 starts from nu = 0
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <time.h>

static int q, Np, Q1, V, NP = 6;            /* NP = polygon diameter n (6 hexagon, 4 quadrangle) */            /* Np points (= lines); vertices 0..Np-1 points, Np..2Np-1 lines */
static int *adj;                    /* V x Q1 hexagon neighbours */
static int *flagof;                 /* V x Q1 -> flag index (shared by both ends) */
static int *flagp, *flagl;          /* flag -> point, line vertex */
static uint8_t *nu;                 /* flag -> 0/1 */
static int *sig, *sinv;             /* point -> line index, line index -> point */
static uint8_t *isfreeP, *isfreeLn;  /* freed points / freed lines (by index): no jumps there */
/* exact-coverage structure of freed flags (p_i on l_i = sigma(p_i)): sigma swaps must keep allowed(x, sigma(x)) */
static int nfl = 0, flp[64], fll[64]; static uint8_t *inA, *inG, *inPp, *inLl;   /* [i*Np + x] */
static int allowed(int x, int M) {
    if (isfreeP[x] || isfreeLn[M]) return 0;
    for (int i = 0; i < nfl; i++) {
        if (inG[i * Np + M] && !inPp[i * Np + x]) return 0;
        if (inA[i * Np + x] && !inLl[i * Np + M]) return 0;
    }
    return 1;
}
static uint8_t *cnt;                /* same-colour pair matrix: cnt[v*Np + u] for v,u in one class; two classes */
static uint8_t *route;              /* bit matrix per class: route[(v*Np+u)] as bytes (0/1) */
static uint64_t rs = 88172645463325252ULL;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline size_t pidx(int a, int b) {   /* a, b same class */
    int cls = a >= Np; int i = a - cls * Np, j = b - cls * Np;
    return (size_t)cls * Np * Np + (size_t)i * Np + j;
}

static void load_hex(void) {
    char fn[256]; sprintf(fn, "hex/hex_q%d.bin", q);
    if (getenv("BASE")) snprintf(fn, sizeof fn, "%s", getenv("BASE"));
    FILE *f = fopen(fn, "rb"); int32_t h[3]; if (!f || fread(h, 4, 3, f) != 3) { fprintf(stderr, "no hex\n"); exit(1); }
    Np = h[1]; Q1 = q + 1; V = 2 * Np;
    int32_t *pl = malloc(4L * Np * Q1); if (fread(pl, 4, (size_t)Np * Q1, f) != (size_t)Np * Q1) exit(1); fclose(f);
    adj = malloc(sizeof(int) * V * Q1); flagof = malloc(sizeof(int) * V * Q1);
    flagp = malloc(sizeof(int) * Np * Q1); flagl = malloc(sizeof(int) * Np * Q1);
    int *dg = calloc(V, sizeof(int));
    for (int l = 0; l < Np; l++) for (int k = 0; k < Q1; k++) {
        int p = pl[l * Q1 + k], fi = l * Q1 + k;     /* flag index = lift2's hexagon-voltage index */
        flagp[fi] = p; flagl[fi] = Np + l;
        adj[p * Q1 + dg[p]] = Np + l; flagof[p * Q1 + dg[p]] = fi; dg[p]++;
        adj[(Np + l) * Q1 + dg[Np + l]] = p; flagof[(Np + l) * Q1 + dg[Np + l]] = fi; dg[Np + l]++;
    }
    free(pl); free(dg);
}

/* routes: BFS from s in the base with matching jumps, states (vertex, jumpsum mod 3, jumped flag) for 6 steps;
   route to u iff state (u, 0, 1) reachable at step 6 (exactly; opposite pairs have even distance 6). */
static void compute_routes(void) {
    size_t nb = (size_t)2 * Np * Np;
    route = calloc(nb, 1);
    /* bitmask per vertex: bit (j*2 + f) for jumpsum j in Z3 and flag f */
    uint8_t *A = malloc(V), *B = malloc(V);
    for (int s = 0; s < V; s++) {
        memset(A, 0, V); A[s] = 1;   /* j=0, f=0 -> bit 0 */
        for (int step = 1; step <= NP; step++) {
            memset(B, 0, V);
            for (int x = 0; x < V; x++) if (A[x]) {
                uint8_t a = A[x];
                for (int k = 0; k < Q1; k++) B[adj[x * Q1 + k]] |= a;     /* hexagon edge: same state */
                /* jump: point x -> line sig(x) with +1; line x -> point sinv with -1 */
                int y; int dj;
                if (x < Np) { if (isfreeP[x]) continue; y = Np + sig[x]; dj = 1; } else { if (isfreeLn[x - Np]) continue; y = sinv[x - Np]; dj = 2; }
                uint8_t o = 0;
                for (int j = 0; j < 3; j++) for (int f = 0; f < 2; f++) if (a >> (j * 2 + f) & 1) o |= 1 << (((j + dj) % 3) * 2 + 1);
                B[y] |= o;
            }
            uint8_t *t = A; A = B; B = t;
        }
        int cls = s >= Np;
        for (int u = cls * Np; u < (cls + 1) * Np; u++) if (A[u] & 2) route[pidx(s, u)] = 1;
    }
    free(A); free(B);
}

/* parities: for source s, BFS in H to depth 5 with parity, then counts at opposite targets */
static int *dist5; static uint8_t *par5; static int *qu;
static void count_source(int s) {
    for (int v = 0; v < V; v++) dist5[v] = -1;
    int h = 0, t = 0; dist5[s] = 0; par5[s] = 0; qu[t++] = s;
    while (h < t) { int x = qu[h++]; if (dist5[x] == NP - 1) continue;
        for (int k = 0; k < Q1; k++) { int y = adj[x * Q1 + k]; if (dist5[y] < 0) { dist5[y] = dist5[x] + 1; par5[y] = par5[x] ^ nu[flagof[x * Q1 + k]]; qu[t++] = y; } } }
    int cls = s >= Np;
    for (int u = cls * Np; u < (cls + 1) * Np; u++) {
        if (dist5[u] >= 0) { cnt[pidx(s, u)] = 255; continue; }   /* not opposite */
        int c = 0;
        for (int k = 0; k < Q1; k++) { int y = adj[u * Q1 + k]; c += par5[y] ^ nu[flagof[u * Q1 + k]]; }
        cnt[pidx(s, u)] = c;
    }
}
static inline int bad(size_t i) { return !route[i] && (cnt[i] == 0 || cnt[i] == Q1); }

/* enumerate geodesics through flag f (orientation: point p then line l at positions k, k+1); for each, endpoints
   (a, b) and current parity; apply delta to cnt and return the change in #bad (counting each unordered pair once
   via a<b) */
static int Lw[8][4096 * 8], Lpar[8][4096 * 8];  /* walk endpoints from p (away from l) of length k, and parities */
static int nL[8];
static void walks_from(int start, int avoid_first, int maxlen, int store[8][4096 * 8], int spar[8][4096 * 8], int *ns) {
    /* NB walks of length 0..maxlen from start whose first step avoids avoid_first; endpoints and parities */
    static int stk_v[8], stk_prev[8], stk_par[8], stk_k[8];
    for (int L = 0; L <= maxlen; L++) ns[L] = 0;
    store[0][0] = start; spar[0][0] = 0; ns[0] = 1;
    /* iterative DFS */
    int depth = 0; stk_v[0] = start; stk_prev[0] = avoid_first; stk_par[0] = 0; stk_k[0] = 0;
    while (depth >= 0) {
        if (depth == maxlen || stk_k[depth] >= Q1) { depth--; if (depth >= 0) stk_k[depth]++; continue; }
        int x = stk_v[depth], k = stk_k[depth];
        int y = adj[x * Q1 + k];
        if (y == stk_prev[depth]) { stk_k[depth]++; continue; }
        int np = stk_par[depth] ^ nu[flagof[x * Q1 + k]];
        int d = depth + 1;
        store[d][ns[d]] = y; spar[d][ns[d]] = np; ns[d]++;
        stk_v[d] = y; stk_prev[d] = x; stk_par[d] = np; stk_k[d] = 0; depth = d;
    }
}
static int Rw[8][4096 * 8], Rpar[8][4096 * 8]; static int nR[8];
static long flip_delta(int f, int apply) {
    int p = flagp[f], l = flagl[f];
    walks_from(p, l, NP - 1, Lw, Lpar, nL);
    walks_from(l, p, NP - 1, Rw, Rpar, nR);
    long d = 0;
    for (int k = 0; k <= NP - 1; k++) {
        int kr = NP - 1 - k;
        for (int i = 0; i < nL[k]; i++) {
            int a = Lw[k][i], pa = Lpar[k][i];
            for (int j = 0; j < nR[kr]; j++) {
                int b = Rw[kr][j];
                int parity = pa ^ nu[f] ^ Rpar[kr][j];        /* current parity of this geodesic */
                size_t i1 = pidx(a, b), i2 = pidx(b, a);
                int before = bad(i1);
                int nc = cnt[i1] + (parity ? -1 : 1);
                if (apply) { cnt[i1] = nc; cnt[i2] = nc; }
                int after = !route[i1] && (nc == 0 || nc == Q1);
                if (a < b) d += after - before;
                else if (a == b) { fprintf(stderr, "a==b?\n"); exit(1); }
                else d += after - before;   /* each unordered pair appears once (orientation p->l fixed) */
            }
        }
    }
    return d;
}

int main(int argc, char **argv) {
    q = atoi(argv[1]); if (getenv("NPOLY")) NP = atoi(getenv("NPOLY")); load_hex();
    if (getenv("SEED")) rs ^= (uint64_t)atoll(getenv("SEED")) * 0x9E3779B97F4A7C15ULL;
    for (int i = 0; i < 10; i++) rnd();
    int NF = Np * Q1;
    nu = malloc(NF); sig = malloc(sizeof(int) * Np); sinv = malloc(sizeof(int) * Np);
    for (int p = 0; p < Np; p++) sig[p] = p;
    for (int p = Np - 1; p > 0; p--) { int r = rnd() % (p + 1); int x = sig[p]; sig[p] = sig[r]; sig[r] = x; }
    for (int i = 0; i < NF; i++) nu[i] = rnd() & 1;
    if (getenv("IN")) {   /* lift2 DM file */
        FILE *f = fopen(getenv("IN"), "r"); int qq, jj, mm, dd; long c; char line[256];
        if (!f || fscanf(f, "%d %d %d %d %ld\n", &qq, &jj, &mm, &dd, &c) != 5 || !fgets(line, sizeof line, f)) { fprintf(stderr, "bad IN\n"); return 1; }
        for (int t = 0; t < jj; t++) for (int p = 0; p < Np; p++) { int x; if (fscanf(f, "%d", &x) != 1) return 1; if (t == 0) sig[p] = x; }
        for (int t = 0; t < jj; t++) for (int p = 0; p < Np; p++) { int x; if (fscanf(f, "%d", &x) != 1) return 1; }
        for (int i = 0; i < NF; i++) { int x; if (fscanf(f, "%d", &x) != 1) return 1; nu[i] = (x / 3) & 1; }
        fclose(f);
    }
    for (int p = 0; p < Np; p++) sinv[sig[p]] = p;
    if (getenv("NUZERO")) memset(nu, 0, NF);
    isfreeP = calloc(Np, 1); isfreeLn = calloc(Np, 1);
    if (getenv("FREE")) { char *s = getenv("FREE"), *e; for (;;) { long x = strtol(s, &e, 10); if (e == s) break; isfreeP[x] = 1; isfreeLn[sig[x]] = 1; flp[nfl] = x; fll[nfl] = sig[x]; nfl++; s = e; } }
    inA = calloc((size_t)64 * Np, 1); inG = calloc((size_t)64 * Np, 1); inPp = calloc((size_t)64 * Np, 1); inLl = calloc((size_t)64 * Np, 1);
    for (int i = 0; i < nfl; i++) {   /* adj: point x -> lines (Np + l); line Np + l -> points */
        int p = flp[i], l = fll[i];
        for (int a = 0; a < Q1; a++) { int L = adj[p * Q1 + a] - Np; for (int b = 0; b < Q1; b++) { int x = adj[(Np + L) * Q1 + b]; if (x == p) continue; inPp[i * Np + x] = 1; if (L != l) inA[i * Np + x] = 1; } }
        for (int a = 0; a < Q1; a++) { int y = adj[(Np + l) * Q1 + a]; for (int b = 0; b < Q1; b++) { int M2 = adj[y * Q1 + b] - Np; if (M2 == l) continue; inLl[i * Np + M2] = 1; if (y != p) inG[i * Np + M2] = 1; } }
    }
    if (getenv("CHECKALLOWED")) { int bad = 0; for (int x = 0; x < Np; x++) if (!isfreeP[x] && !allowed(x, sig[x])) bad++; fprintf(stderr, "sigma entries not allowed: %d\n", bad); }
    struct timespec t0; clock_gettime(CLOCK_MONOTONIC, &t0);
    if (getenv("NOROUTE")) route = calloc((size_t)2 * Np * Np, 1); else compute_routes();
    size_t npairs = (size_t)2 * Np * Np;
    cnt = malloc(npairs);
    dist5 = malloc(sizeof(int) * V); par5 = malloc(V); qu = malloc(sizeof(int) * V);
    for (int s = 0; s < V; s++) count_source(s);
    long cost = 0, opp = 0, rcov = 0;
    for (int a = 0; a < V; a++) { int cls = a >= Np; for (int b = a + 1; b < (cls + 1) * Np; b++) { size_t i = pidx(a, b); if (cnt[i] == 255) continue; opp++; rcov += route[i]; cost += bad(i); } }
    struct timespec t1; clock_gettime(CLOCK_MONOTONIC, &t1);
    fprintf(stderr, "q=%d opposite pairs %ld, with route %ld (%.1f%%), initial cost %ld (%.3f%%)  [setup %.1fs]\n", q, opp, rcov, 100.0 * rcov / opp, cost, 100.0 * cost / opp,
        (t1.tv_sec - t0.tv_sec) + 1e-9 * (t1.tv_nsec - t0.tv_nsec));
    long iters = getenv("ITERS") ? atol(getenv("ITERS")) : 0;
    double secs = getenv("SECS") ? atof(getenv("SECS")) : 1e18;
    double T0 = getenv("TEMP0") ? atof(getenv("TEMP0")) : 1.0, T1 = getenv("TEMP1") ? atof(getenv("TEMP1")) : 0.02;
    long best = cost; uint8_t *bestnu = malloc(NF); memcpy(bestnu, nu, NF);
    int *bestsig = malloc(sizeof(int) * Np); memcpy(bestsig, sig, sizeof(int) * Np);
    double swapp = getenv("SWAPP") ? atof(getenv("SWAPP")) : 0.0; long nswapacc = 0;
    uint8_t *route_bak = malloc(npairs);
    long it;
    for (it = 0; it < iters && cost > 0; it++) {
        if ((it & 63) == 0) { struct timespec ts; clock_gettime(CLOCK_MONOTONIC, &ts); if ((ts.tv_sec - t1.tv_sec) + 1e-9 * (ts.tv_nsec - t1.tv_nsec) > secs) break; }
        double temp = T0 * pow(T1 / T0, (double)it / iters);
        if (swapp > 0 && (rnd() >> 11) * (1.0 / 9007199254740992.0) < swapp) {
            int p1 = rnd() % Np, p2 = rnd() % Np; if (p1 == p2) continue;
            if (nfl && !(allowed(p1, sig[p2]) && allowed(p2, sig[p1]))) continue;
            memcpy(route_bak, route, npairs);
            int l1 = sig[p1], l2 = sig[p2]; sig[p1] = l2; sig[p2] = l1; sinv[l2] = p1; sinv[l1] = p2;
            free(route); compute_routes();
            long nc = 0; for (size_t i = 0; i < npairs; i++) if (cnt[i] != 255 && bad(i)) nc++;
            nc /= 2;
            long d = nc - cost;
            double u = (rnd() >> 11) * (1.0 / 9007199254740992.0);
            if (d <= 0 || u < exp(-d / temp)) { cost = nc; nswapacc++;
                if (cost < best) { best = cost; memcpy(bestnu, nu, NF); memcpy(bestsig, sig, sizeof(int) * Np); fprintf(stderr, "it %ld temp %.3f cost %ld (swap)\n", it, temp, cost); } }
            else { sig[p1] = l1; sig[p2] = l2; sinv[l1] = p1; sinv[l2] = p2; memcpy(route, route_bak, npairs); }
            continue;
        }
        int f = rnd() % NF;
        long d = flip_delta(f, 0);
        double u = (rnd() >> 11) * (1.0 / 9007199254740992.0);
        if (d <= 0 || u < exp(-d / temp)) {
            flip_delta(f, 1); nu[f] ^= 1; cost += d;
            if (cost < best) { best = cost; memcpy(bestnu, nu, NF); memcpy(bestsig, sig, sizeof(int) * Np); if (best < 50 || (it & 1023) == 0) fprintf(stderr, "it %ld temp %.3f cost %ld\n", it, temp, cost); }
        }
    }
    printf("RESULT dmfast q %d iters %ld best %ld (of %ld opposite pairs) swaps accepted %ld\n", q, it, best, opp, nswapacc);
    memcpy(sig, bestsig, sizeof(int) * Np);
    if (getenv("OUT")) {
        FILE *g = fopen(getenv("OUT"), "w");
        fprintf(g, "%d 2 6 7 %ld\ncyc 6\n", q, best);
        for (int t = 0; t < 2; t++) { for (int p = 0; p < Np; p++) fprintf(g, "%d ", sig[p]); fprintf(g, "\n"); }
        for (int p = 0; p < Np; p++) fprintf(g, "1 "); fprintf(g, "\n");
        for (int p = 0; p < Np; p++) fprintf(g, "4 "); fprintf(g, "\n");
        for (int i = 0; i < NF; i++) fprintf(g, "%d ", 3 * bestnu[i]); fprintf(g, "\n");
        fclose(g);
    }
    return 0;
}
