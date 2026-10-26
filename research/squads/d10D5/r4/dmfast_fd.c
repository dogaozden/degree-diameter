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
static uint8_t *delf = NULL, *ngeo = NULL; static int fdn = 0, fdp[64], fdl[64];   /* FLAGDEL: deleted flag edges, geodesic counts */
static int nfl = 0, flp[64], fll[64]; static uint8_t *inA, *inG, *inPp, *inLl;   /* [i*Np + x] */
static char isfd[64];   /* FLAGDEL flag i: coverage may not use its deleted edge (point side: inA instead of inPp; line side: inG instead of inLl) */
/* relaxed coverage (RELAX=1): sigma swaps are kept only if every freed point still reaches coset 1 of each opposite
 * point (p-L-x-sigma(x)-u, x ~ p, or p-w-sinv(w)-sigma(u)-u) and dually for freed lines; same test as dmhub.c */
static int *mk = NULL, stp = 0, patch = 0; static uint8_t *onfl = NULL, *thrfp = NULL;
static char hadj[64][64]; static int usehadj = 0;   /* HUBADJ="i:j ...": line-side hubs of flag i ~ point-side hubs of flag j */
static int cover_ok(void) {
    if (!mk) mk = calloc(2 * Np, sizeof(int));
    if (!onfl) {   /* PATCH=1: points on a freed line / lines through a freed point count as covered (hub edges patch them) */
        onfl = calloc(Np, 1); thrfp = calloc(Np, 1);
        for (int i = 0; i < nfl; i++) { for (int k = 0; k < Q1; k++) { onfl[adj[(Np + fll[i]) * Q1 + k]] = 1; thrfp[adj[flp[i] * Q1 + k] - Np] = 1; } }
    }
    for (int i = 0; i < nfl; i++) {
        int p = flp[i], l = fll[i]; stp++;
        for (int x = 0; x < Np; x++) if ((isfd[i] ? inA[i * Np + x] : inPp[i * Np + x]) && !isfreeP[x]) { int L = sig[x]; for (int k = 0; k < Q1; k++) mk[adj[(Np + L) * Q1 + k]] = stp; }
        for (int a = 0; a < Q1; a++) { int w = adj[p * Q1 + a] - Np; if (isfreeLn[w]) continue; int z = sinv[w];
            for (int b = 0; b < Q1; b++) { int u = sinv[adj[z * Q1 + b] - Np]; if (!isfreeP[u]) mk[u] = stp; } }
        if (usehadj) for (int j = 0; j < nfl; j++) if (hadj[i][j]) for (int k = 0; k < Q1; k++) mk[adj[(Np + fll[j]) * Q1 + k]] = stp;
        for (int u = 0; u < Np; u++) if (u != p && !inPp[i * Np + u] && mk[u] != stp && !(patch && onfl[u])) return 0;
        stp++;
        for (int M2 = 0; M2 < Np; M2++) if ((isfd[i] ? inG[i * Np + M2] : inLl[i * Np + M2]) && !isfreeLn[M2]) { int y = sinv[M2]; for (int k = 0; k < Q1; k++) mk[Np + adj[y * Q1 + k] - Np] = stp; }
        for (int a = 0; a < Q1; a++) { int y = adj[(Np + l) * Q1 + a]; if (isfreeP[y]) continue; int ly = sig[y];
            for (int b = 0; b < Q1; b++) { int z = adj[(Np + ly) * Q1 + b]; if (!isfreeP[z]) mk[Np + sig[z]] = stp; } }
        if (usehadj) for (int j = 0; j < nfl; j++) if (hadj[j][i]) for (int k = 0; k < Q1; k++) mk[Np + adj[flp[j] * Q1 + k] - Np] = stp;
        for (int m = 0; m < Np; m++) if (m != l && !inLl[i * Np + m] && mk[Np + m] != stp && !(patch && thrfp[m])) return 0;
    }
    return 1;
}
static int d1_ok(void) {   /* FLAGDEL D1 condition (same as dmhub2.c d1_cost), for the flags in FDSET */
    if (!fdn) return 1;
    if (!mk) mk = calloc(2 * Np, sizeof(int));
    for (int f = 0; f < fdn; f++) {
        int p = fdp[f], l = fdl[f];
        for (int a = 0; a < Q1; a++) {
            int L = adj[p * Q1 + a] - Np; if (L == l || isfreeLn[L]) continue;
            int v = sinv[L], von = 0; for (int b = 0; b < Q1; b++) if (adj[(Np + l) * Q1 + b] == v) von = 1;
            if (von) continue;
            stp++;
            for (int b = 0; b < Q1; b++) { int L1 = adj[v * Q1 + b] - Np; for (int c = 0; c < Q1; c++) { int x = adj[(Np + L1) * Q1 + c]; if (x == v || isfreeP[x]) continue;
                int lx = sig[x]; for (int k = 0; k < Q1; k++) mk[adj[(Np + lx) * Q1 + k]] = stp; } }
            for (int b = 0; b < Q1; b++) { int L2 = adj[v * Q1 + b] - Np; if (isfreeLn[L2]) continue; int z = sinv[L2];
                for (int k = 0; k < Q1; k++) { int u = sinv[adj[z * Q1 + k] - Np]; if (!isfreeP[u]) mk[u] = stp; } }
            for (int b = 0; b < Q1; b++) { int u = adj[(Np + l) * Q1 + b]; if (u == p) continue;
                if (isfreeP[u]) { int co = 0; for (int c = 0; c < Q1 && !co; c++) for (int d = 0; d < Q1; d++) if (adj[u * Q1 + c] == adj[v * Q1 + d]) { co = 1; break; } if (co) continue; }
                if (mk[u] != stp) return 0; }
        }
        for (int a = 0; a < Q1; a++) {
            int y = adj[(Np + l) * Q1 + a]; if (y == p || isfreeP[y]) continue;
            int sl = sig[y], thr = 0; for (int b = 0; b < Q1; b++) if (adj[p * Q1 + b] == Np + sl) thr = 1;
            if (thr) continue;
            stp++;
            for (int b = 0; b < Q1; b++) { int y2 = adj[(Np + sl) * Q1 + b]; for (int c = 0; c < Q1; c++) { int M2 = adj[y2 * Q1 + c] - Np; if (M2 == sl || isfreeLn[M2]) continue;
                int w = sinv[M2]; for (int k = 0; k < Q1; k++) mk[adj[w * Q1 + k]] = stp; } }
            for (int b = 0; b < Q1; b++) { int y2 = adj[(Np + sl) * Q1 + b]; if (isfreeP[y2]) continue; int ly = sig[y2];
                for (int k = 0; k < Q1; k++) { int z = adj[(Np + ly) * Q1 + k]; if (!isfreeP[z]) mk[Np + sig[z]] = stp; } }
            for (int b = 0; b < Q1; b++) { int t = adj[p * Q1 + b] - Np; if (t == l) continue;
                if (isfreeLn[t]) { int co = 0; for (int c = 0; c < Q1 && !co; c++) for (int d = 0; d < Q1; d++) if (adj[(Np + t) * Q1 + c] == adj[(Np + sl) * Q1 + d]) { co = 1; break; } if (co) continue; }
                if (mk[Np + t] != stp) return 0; }
        }
    }
    return 1;
}
static int cover_count(void) {   /* RELAX=2: number of coverage holes (cover_ok without early exit) */
    int nh = 0;
    if (!mk) mk = calloc(2 * Np, sizeof(int));
    if (!onfl) {   /* PATCH=1: points on a freed line / lines through a freed point count as covered (hub edges patch them) */
        onfl = calloc(Np, 1); thrfp = calloc(Np, 1);
        for (int i = 0; i < nfl; i++) { for (int k = 0; k < Q1; k++) { onfl[adj[(Np + fll[i]) * Q1 + k]] = 1; thrfp[adj[flp[i] * Q1 + k] - Np] = 1; } }
    }
    for (int i = 0; i < nfl; i++) {
        int p = flp[i], l = fll[i]; stp++;
        for (int x = 0; x < Np; x++) if ((isfd[i] ? inA[i * Np + x] : inPp[i * Np + x]) && !isfreeP[x]) { int L = sig[x]; for (int k = 0; k < Q1; k++) mk[adj[(Np + L) * Q1 + k]] = stp; }
        for (int a = 0; a < Q1; a++) { int w = adj[p * Q1 + a] - Np; if (isfreeLn[w]) continue; int z = sinv[w];
            for (int b = 0; b < Q1; b++) { int u = sinv[adj[z * Q1 + b] - Np]; if (!isfreeP[u]) mk[u] = stp; } }
        if (usehadj) for (int j = 0; j < nfl; j++) if (hadj[i][j]) for (int k = 0; k < Q1; k++) mk[adj[(Np + fll[j]) * Q1 + k]] = stp;
        for (int u = 0; u < Np; u++) if (u != p && !inPp[i * Np + u] && mk[u] != stp && !(patch && onfl[u])) nh++;
        stp++;
        for (int M2 = 0; M2 < Np; M2++) if ((isfd[i] ? inG[i * Np + M2] : inLl[i * Np + M2]) && !isfreeLn[M2]) { int y = sinv[M2]; for (int k = 0; k < Q1; k++) mk[Np + adj[y * Q1 + k] - Np] = stp; }
        for (int a = 0; a < Q1; a++) { int y = adj[(Np + l) * Q1 + a]; if (isfreeP[y]) continue; int ly = sig[y];
            for (int b = 0; b < Q1; b++) { int z = adj[(Np + ly) * Q1 + b]; if (!isfreeP[z]) mk[Np + sig[z]] = stp; } }
        if (usehadj) for (int j = 0; j < nfl; j++) if (hadj[j][i]) for (int k = 0; k < Q1; k++) mk[Np + adj[flp[j] * Q1 + k] - Np] = stp;
        for (int m = 0; m < Np; m++) if (m != l && !inLl[i * Np + m] && mk[Np + m] != stp && !(patch && thrfp[m])) nh++;
    }
    return nh;
}
static int d1_count(void) {   /* RELAX=2: number of D1 holes */
    int nh = 0;
    if (!fdn) return 0;
    if (!mk) mk = calloc(2 * Np, sizeof(int));
    for (int f = 0; f < fdn; f++) {
        int p = fdp[f], l = fdl[f];
        for (int a = 0; a < Q1; a++) {
            int L = adj[p * Q1 + a] - Np; if (L == l || isfreeLn[L]) continue;
            int v = sinv[L], von = 0; for (int b = 0; b < Q1; b++) if (adj[(Np + l) * Q1 + b] == v) von = 1;
            if (von) continue;
            stp++;
            for (int b = 0; b < Q1; b++) { int L1 = adj[v * Q1 + b] - Np; for (int c = 0; c < Q1; c++) { int x = adj[(Np + L1) * Q1 + c]; if (x == v || isfreeP[x]) continue;
                int lx = sig[x]; for (int k = 0; k < Q1; k++) mk[adj[(Np + lx) * Q1 + k]] = stp; } }
            for (int b = 0; b < Q1; b++) { int L2 = adj[v * Q1 + b] - Np; if (isfreeLn[L2]) continue; int z = sinv[L2];
                for (int k = 0; k < Q1; k++) { int u = sinv[adj[z * Q1 + k] - Np]; if (!isfreeP[u]) mk[u] = stp; } }
            for (int b = 0; b < Q1; b++) { int u = adj[(Np + l) * Q1 + b]; if (u == p) continue;
                if (isfreeP[u]) { int co = 0; for (int c = 0; c < Q1 && !co; c++) for (int d = 0; d < Q1; d++) if (adj[u * Q1 + c] == adj[v * Q1 + d]) { co = 1; break; } if (co) continue; }
                if (mk[u] != stp) nh++; }
        }
        for (int a = 0; a < Q1; a++) {
            int y = adj[(Np + l) * Q1 + a]; if (y == p || isfreeP[y]) continue;
            int sl = sig[y], thr = 0; for (int b = 0; b < Q1; b++) if (adj[p * Q1 + b] == Np + sl) thr = 1;
            if (thr) continue;
            stp++;
            for (int b = 0; b < Q1; b++) { int y2 = adj[(Np + sl) * Q1 + b]; for (int c = 0; c < Q1; c++) { int M2 = adj[y2 * Q1 + c] - Np; if (M2 == sl || isfreeLn[M2]) continue;
                int w = sinv[M2]; for (int k = 0; k < Q1; k++) mk[adj[w * Q1 + k]] = stp; } }
            for (int b = 0; b < Q1; b++) { int y2 = adj[(Np + sl) * Q1 + b]; if (isfreeP[y2]) continue; int ly = sig[y2];
                for (int k = 0; k < Q1; k++) { int z = adj[(Np + ly) * Q1 + k]; if (!isfreeP[z]) mk[Np + sig[z]] = stp; } }
            for (int b = 0; b < Q1; b++) { int t = adj[p * Q1 + b] - Np; if (t == l) continue;
                if (isfreeLn[t]) { int co = 0; for (int c = 0; c < Q1 && !co; c++) for (int d = 0; d < Q1; d++) if (adj[(Np + t) * Q1 + c] == adj[(Np + sl) * Q1 + d]) { co = 1; break; } if (co) continue; }
                if (mk[Np + t] != stp) nh++; }
        }
    }
    return nh;
}
static int relax = 0;
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
static uint8_t *rc = NULL;   /* GEN: per ordered opposite pair, bit0 = a length-4 walk with a jump and jump-sum 1 (coset 1),
                               bit1 = jump-sum 2 (coset 2), deleted flag edges avoided; hub routes give both */
static int gen = 0;
static void compute_routes(void) {
    size_t nb = (size_t)2 * Np * Np;
    route = calloc(nb, 1);
    if (!rc) rc = malloc(nb);
    memset(rc, 0, nb);
    /* bitmask per vertex: bit (j*2 + f) for jumpsum j in Z3 and flag f */
    uint8_t *A = malloc(V), *B = malloc(V);
    for (int s = 0; s < V; s++) {
        memset(A, 0, V); A[s] = 1;   /* j=0, f=0 -> bit 0 */
        for (int step = 1; step <= NP; step++) {
            memset(B, 0, V);
            for (int x = 0; x < V; x++) if (A[x]) {
                uint8_t a = A[x];
                for (int k = 0; k < Q1; k++) if (!delf[flagof[x * Q1 + k]]) B[adj[x * Q1 + k]] |= a;     /* polygon edge: same state */
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
        for (int u = cls * Np; u < (cls + 1) * Np; u++) { if (A[u] & 2) route[pidx(s, u)] = 1; rc[pidx(s, u)] = ((A[u] >> 3) & 1) | (((A[u] >> 5) & 1) << 1); }
    }
    free(A); free(B);
    /* hub routes (HUBADJ): (p_i,0) -> line-side hub i -> point-side hub j -> (l_j, every sheet) -> every point on l_j,
       and (l_i,0) -> point-side hub i -> line-side hub j -> (p_j) -> every line through p_j: these pairs are covered */
    if (usehadj) for (int i = 0; i < nfl; i++) for (int j = 0; j < nfl; j++) {
        if (hadj[i][j]) for (int k = 0; k < Q1; k++) { int b = adj[(Np + fll[j]) * Q1 + k]; if (b != flp[i]) { route[pidx(flp[i], b)] = 1; route[pidx(b, flp[i])] = 1; rc[pidx(flp[i], b)] = 3; rc[pidx(b, flp[i])] = 3; } }
        if (hadj[j][i]) for (int k = 0; k < Q1; k++) { int t = adj[flp[j] * Q1 + k]; if (t != Np + fll[i]) { route[pidx(Np + fll[i], t)] = 1; route[pidx(t, Np + fll[i])] = 1; rc[pidx(Np + fll[i], t)] = 3; rc[pidx(t, Np + fll[i])] = 3; } }
    }
}

/* parities: for source s, BFS in H to depth 5 with parity, then counts at opposite targets */
static int *dist5; static uint8_t *par5; static int *qu;
static int *distF = NULL;
static void count_source(int s) {
    if (!distF) distF = malloc(sizeof(int) * V);
    for (int v = 0; v < V; v++) distF[v] = -1;
    { int h = 0, t = 0; distF[s] = 0; qu[t++] = s;
      while (h < t) { int x = qu[h++]; if (distF[x] == NP - 1) continue;
        for (int k = 0; k < Q1; k++) { int y = adj[x * Q1 + k]; if (distF[y] < 0) { distF[y] = distF[x] + 1; qu[t++] = y; } } } }
    for (int v = 0; v < V; v++) dist5[v] = -1;
    int h = 0, t = 0; dist5[s] = 0; par5[s] = 0; qu[t++] = s;
    while (h < t) { int x = qu[h++]; if (dist5[x] == NP - 1) continue;
        for (int k = 0; k < Q1; k++) { if (delf[flagof[x * Q1 + k]]) continue; int y = adj[x * Q1 + k]; if (dist5[y] < 0) { dist5[y] = dist5[x] + 1; par5[y] = par5[x] ^ nu[flagof[x * Q1 + k]]; qu[t++] = y; } } }
    int cls = s >= Np;
    for (int u = cls * Np; u < (cls + 1) * Np; u++) {
        if (distF[u] >= 0) { cnt[pidx(s, u)] = 255; continue; }   /* not opposite in the quadrangle (hubs reroute the
                                                                     pairs whose short path used a deleted flag edge) */
        int c = 0, g = 0;
        for (int k = 0; k < Q1; k++) { if (delf[flagof[u * Q1 + k]]) continue; int y = adj[u * Q1 + k]; if (dist5[y] != NP - 1) continue; c += par5[y] ^ nu[flagof[u * Q1 + k]]; g++; }
        cnt[pidx(s, u)] = c; ngeo[pidx(s, u)] = g;
    }
}
static inline int bad(size_t i) { return !route[i] && (cnt[i] == 0 || cnt[i] == ngeo[i]); }
static int hla[512], hlb[512], nhl = 0;   /* GEN: sample of current holes (source, target) */
static uint8_t *hasHub = NULL;   /* vertices whose fibre carries hubs (freed points/lines, XDEL endpoints): their
                                   pairs at base distance <= 2 change sheet through the hub */
static long holes_count(void) {   /* GEN: ordered same-colour pairs (s, u), s != u, with no coset-1 walk of length 4
                                     from s to u avoiding deleted edges (coverage + D1 for any deleted edges); pairs at
                                     base distance 2 count only when neither end has hubs */
    long h = 0; nhl = 0;
    for (int a = 0; a < V; a++) { int cls = a >= Np;
        for (int b = cls * Np; b < (cls + 1) * Np; b++) { if (a == b) continue; size_t i = pidx(a, b);
            if (rc[i] & 1) continue;
            if (cnt[i] == 255 && (hasHub[a] || hasHub[b])) continue;
            if (nhl < 512) { hla[nhl] = a; hlb[nhl] = b; nhl++; }
            h++; } }
    return h;
}

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
        if (y == stk_prev[depth] || delf[flagof[x * Q1 + k]]) { stk_k[depth]++; continue; }
        int np = stk_par[depth] ^ nu[flagof[x * Q1 + k]];
        int d = depth + 1;
        store[d][ns[d]] = y; spar[d][ns[d]] = np; ns[d]++;
        stk_v[d] = y; stk_prev[d] = x; stk_par[d] = np; stk_k[d] = 0; depth = d;
    }
}
static int Rw[8][4096 * 8], Rpar[8][4096 * 8]; static int nR[8];
static long flip_delta(int f, int apply) {
    int p = flagp[f], l = flagl[f]; if (delf[f]) return 0;
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
                if (cnt[i1] == 255) continue;
                int before = bad(i1);
                int nc = cnt[i1] + (parity ? -1 : 1);
                if (apply) { cnt[i1] = nc; cnt[i2] = nc; }
                int after = !route[i1] && (nc == 0 || nc == ngeo[i1]);
                if (a < b) d += after - before;
                else if (a == b) { fprintf(stderr, "a==b?\n"); exit(1); }
                else d += after - before;   /* each unordered pair appears once (orientation p->l fixed) */
            }
        }
    }
    return d;
}

static void write_out(long best, uint8_t *bestnu, int *bestsig) {
    if (!getenv("OUT")) return;
    FILE *g = fopen(getenv("OUT"), "w"); int NF = Np * Q1;
    fprintf(g, "%d 2 6 7 %ld\ncyc 6\n", q, best);
    for (int t = 0; t < 2; t++) { for (int p = 0; p < Np; p++) fprintf(g, "%d ", bestsig[p]); fprintf(g, "\n"); }
    for (int p = 0; p < Np; p++) fprintf(g, "1 "); fprintf(g, "\n");
    for (int p = 0; p < Np; p++) fprintf(g, "4 "); fprintf(g, "\n");
    for (int i = 0; i < NF; i++) fprintf(g, "%d ", 3 * bestnu[i]); fprintf(g, "\n");
    fclose(g);
}

/* EJECT=d: depth-limited search over nu flips (exact flip_delta): take a bad pair, try every flag on its geodesics,
   recurse on the remaining bad pairs while the cost stays within the slack. */
static long ej_cost; static long ej_nodes = 0;
static int first_bad(int *a0, int *b0, int skip) {
    int c = 0;
    for (int a = 0; a < V; a++) { int cls = a >= Np; for (int b = a + 1; b < (cls + 1) * Np; b++) { size_t i = pidx(a, b); if (cnt[i] != 255 && bad(i)) { if (c++ == skip) { *a0 = a; *b0 = b; return 1; } } } }
    return 0;
}
static int geo_flags(int a, int b, int *cand) {
    int nc = 0;
    for (int k1 = 0; k1 < Q1; k1++) { if (delf[flagof[a * Q1 + k1]]) continue; int n1 = adj[a * Q1 + k1];
        for (int k2 = 0; k2 < Q1; k2++) { if (delf[flagof[n1 * Q1 + k2]]) continue; int x = adj[n1 * Q1 + k2]; if (x == a) continue;
            for (int k3 = 0; k3 < Q1; k3++) { if (delf[flagof[x * Q1 + k3]]) continue; int n2 = adj[x * Q1 + k3]; if (n2 == n1) continue;
                for (int k4 = 0; k4 < Q1; k4++) if (adj[n2 * Q1 + k4] == b && !delf[flagof[n2 * Q1 + k4]] && nc < 252) {
                    cand[nc++] = flagof[a * Q1 + k1]; cand[nc++] = flagof[n1 * Q1 + k2]; cand[nc++] = flagof[x * Q1 + k3]; cand[nc++] = flagof[n2 * Q1 + k4]; } } } }
    return nc;
}
static int eject(int depth, long slack) {
    if (ej_cost == 0) return 1;
    if (depth == 0) return 0;
    int a, b; if (!first_bad(&a, &b, 0)) return ej_cost == 0;
    int cand[256]; int nc = geo_flags(a, b, cand);
    for (int t = 0; t < nc; t++) {
        int f = cand[t]; int dup = 0; for (int u = 0; u < t; u++) if (cand[u] == f) dup = 1; if (dup) continue;
        long d = flip_delta(f, 0); ej_nodes++;
        if (ej_cost + d > slack) continue;
        flip_delta(f, 1); nu[f] ^= 1; ej_cost += d;
        if (eject(depth - 1, slack)) return 1;
        long d2 = flip_delta(f, 0); flip_delta(f, 1); nu[f] ^= 1; ej_cost += d2;
    }
    return 0;
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
    delf = calloc((size_t)Np * Q1, 1);
    if (getenv("FDSET")) { char *s2 = getenv("FDSET"), *e2; for (;;) { long ii = strtol(s2, &e2, 10); if (e2 == s2) break; s2 = e2;
        int p = flp[ii], l = fll[ii]; fdp[fdn] = p; fdl[fdn++] = l; isfd[ii] = 1;
        for (int k = 0; k < Q1; k++) if (adj[p * Q1 + k] == Np + l) delf[flagof[p * Q1 + k]] = 1; }
        fprintf(stderr, "FLAGDEL: %d flag edges deleted\n", fdn); }
    if (getenv("XDEL")) { char *s3 = getenv("XDEL"), *e3; int nx = 0;   /* XDEL="x:L ...": ordinary flag edges deleted too */
        for (;;) { long x = strtol(s3, &e3, 10); if (e3 == s3 || *e3 != ':') break; s3 = e3 + 1; long L = strtol(s3, &e3, 10); s3 = e3;
            for (int k = 0; k < Q1; k++) if (adj[x * Q1 + k] == Np + L) { delf[flagof[x * Q1 + k]] = 1; nx++; } }
        fprintf(stderr, "XDEL: %d ordinary flag edges deleted\n", nx); }
    hasHub = calloc(V, 1);
    for (int i = 0; i < nfl; i++) { hasHub[flp[i]] = 1; hasHub[Np + fll[i]] = 1; }
    if (getenv("XDEL")) { char *s3 = getenv("XDEL"), *e3;
        for (;;) { long x = strtol(s3, &e3, 10); if (e3 == s3 || *e3 != ':') break; s3 = e3 + 1; long L = strtol(s3, &e3, 10); s3 = e3; hasHub[x] = 1; hasHub[Np + L] = 1; } }
    gen = getenv("GEN") ? atoi(getenv("GEN")) : 0;
    inA = calloc((size_t)64 * Np, 1); inG = calloc((size_t)64 * Np, 1); inPp = calloc((size_t)64 * Np, 1); inLl = calloc((size_t)64 * Np, 1);
    for (int i = 0; i < nfl; i++) {   /* adj: point x -> lines (Np + l); line Np + l -> points */
        int p = flp[i], l = fll[i];
        for (int a = 0; a < Q1; a++) { int L = adj[p * Q1 + a] - Np; for (int b = 0; b < Q1; b++) { int x = adj[(Np + L) * Q1 + b]; if (x == p) continue; inPp[i * Np + x] = 1; if (L != l) inA[i * Np + x] = 1; } }
        for (int a = 0; a < Q1; a++) { int y = adj[(Np + l) * Q1 + a]; for (int b = 0; b < Q1; b++) { int M2 = adj[y * Q1 + b] - Np; if (M2 == l) continue; inLl[i * Np + M2] = 1; if (y != p) inG[i * Np + M2] = 1; } }
    }
    relax = getenv("RELAX") ? atoi(getenv("RELAX")) : 0; patch = getenv("PATCH") ? atoi(getenv("PATCH")) : 0;
    if (getenv("HUBADJ")) { char *s = getenv("HUBADJ"), *e; usehadj = 1;
        for (;;) { long i = strtol(s, &e, 10); if (e == s || *e != ':') break; s = e + 1; long j = strtol(s, &e, 10); s = e; hadj[i][j] = 1; } }
    if (relax) fprintf(stderr, "relaxed coverage at start: %s, D1 %s\n", cover_ok() ? "ok" : "NOT ok", d1_ok() ? "ok" : "NOT ok");
    if (getenv("CHECKALLOWED")) { int bad = 0; for (int x = 0; x < Np; x++) if (!isfreeP[x] && !allowed(x, sig[x])) bad++; fprintf(stderr, "sigma entries not allowed: %d\n", bad); }
    struct timespec t0; clock_gettime(CLOCK_MONOTONIC, &t0);
    if (getenv("NOROUTE")) route = calloc((size_t)2 * Np * Np, 1); else compute_routes();
    size_t npairs = (size_t)2 * Np * Np;
    cnt = malloc(npairs); ngeo = calloc(npairs, 1);
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
    double swapp = getenv("SWAPP") ? atof(getenv("SWAPP")) : 0.0; long nswapacc = 0; double phole = getenv("PHOLE") ? atof(getenv("PHOLE")) : 0.7;
    uint8_t *route_bak = malloc(npairs);
    double ptarg = getenv("PTARG") ? atof(getenv("PTARG")) : 0.0; static int bla[256], blb[256]; int nbl = 0;
    long it; long covpen = relax == 2 ? (gen ? holes_count() : cover_count() + d1_count()) : 0; long penw = getenv("PENW") ? atol(getenv("PENW")) : 3;
    if (relax == 2) { fprintf(stderr, "penalty mode: coverage+D1 holes %ld, weight %ld\n", covpen, penw); if (covpen) best = 1L << 40; }
    long bestpen = cost + penw * covpen; uint8_t *bpnu = malloc(NF); memcpy(bpnu, nu, NF); int *bpsig = malloc(sizeof(int) * Np); memcpy(bpsig, sig, sizeof(int) * Np);   /* GEN: best penalised state */
    for (it = 0; it < iters && (cost > 0 || covpen > 0); it++) {
        if ((it & 63) == 0) { struct timespec ts; clock_gettime(CLOCK_MONOTONIC, &ts); if ((ts.tv_sec - t1.tv_sec) + 1e-9 * (ts.tv_nsec - t1.tv_nsec) > secs) break; }
        double temp = T0 * pow(T1 / T0, (double)it / iters);
        if (gen && it % 20000 == 0) fprintf(stderr, "it %ld temp %.3f cost %ld holes %ld\n", it, temp, cost, covpen);
        if (gen && cost + penw * covpen < bestpen) { bestpen = cost + penw * covpen; memcpy(bpnu, nu, NF); memcpy(bpsig, sig, sizeof(int) * Np); }
        if (swapp > 0 && (rnd() >> 11) * (1.0 / 9007199254740992.0) < swapp) {
            int p1 = rnd() % Np, p2 = rnd() % Np;
            if (ptarg > 0 && nbl && (rnd() >> 11) * (1.0 / 9007199254740992.0) < ptarg) {
                /* targeted route: for a bad point pair (a,b) make sigma(a) meet sigma(b); for lines make the preimages collinear */
                int r = rnd() % nbl, a = bla[r], b = blb[r]; if (rnd() & 1) { int t = a; a = b; b = t; }
                if (a < Np) { int y = adj[(Np + sig[b]) * Q1 + rnd() % Q1]; int M2 = adj[y * Q1 + rnd() % Q1] - Np; p1 = a; p2 = sinv[M2]; }
                else { int xb = sinv[b - Np]; int Lz = adj[xb * Q1 + rnd() % Q1]; int z = adj[Lz * Q1 + rnd() % Q1]; p1 = sinv[a - Np]; p2 = z; }
            }
            if (gen && nhl && (rnd() >> 11) * (1.0 / 9007199254740992.0) < phole) {
                /* targeted hole repair: a lacks a coset-1 walk to b.  Points: give a point x collinear with a a line
                   through b (walk a - M - x - sigma(x) - b).  Lines: give a point y on a a line through a point z of b
                   (walk a - y - sigma(y) - z - b). */
                int r = rnd() % nhl, a = hla[r], b = hlb[r];
                if (a < Np) { int M2 = adj[a * Q1 + rnd() % Q1]; int x = adj[M2 * Q1 + rnd() % Q1]; int L2 = adj[b * Q1 + rnd() % Q1] - Np; p1 = x; p2 = sinv[L2]; }
                else { int y = adj[a * Q1 + rnd() % Q1]; int z = adj[b * Q1 + rnd() % Q1]; int L2 = adj[z * Q1 + rnd() % Q1] - Np; p1 = y; p2 = sinv[L2]; }
            }
            if (p1 == p2) continue;
            if (nfl && !relax && !(allowed(p1, sig[p2]) && allowed(p2, sig[p1]))) continue;
            long cov2 = 0;
            if (nfl && relax == 1) { if (isfreeP[p1] || isfreeP[p2]) continue;
                int a1 = sig[p1], a2 = sig[p2]; sig[p1] = a2; sig[p2] = a1; sinv[a2] = p1; sinv[a1] = p2;
                int ok = cover_ok() && d1_ok(); sig[p1] = a1; sig[p2] = a2; sinv[a1] = p1; sinv[a2] = p2; if (!ok) continue; }
            if (nfl && relax == 2 && gen) { if (isfreeP[p1] || isfreeP[p2]) continue; }
            else if (nfl && relax == 2) { if (isfreeP[p1] || isfreeP[p2]) continue;
                int a1 = sig[p1], a2 = sig[p2]; sig[p1] = a2; sig[p2] = a1; sinv[a2] = p1; sinv[a1] = p2;
                cov2 = cover_count() + d1_count(); sig[p1] = a1; sig[p2] = a2; sinv[a1] = p1; sinv[a2] = p2;
                if (cov2 > covpen + 3) continue; }
            memcpy(route_bak, route, npairs);
            int l1 = sig[p1], l2 = sig[p2]; sig[p1] = l2; sig[p2] = l1; sinv[l2] = p1; sinv[l1] = p2;
            uint8_t *rc_bak = NULL; if (gen) { rc_bak = malloc(npairs); memcpy(rc_bak, rc, npairs); }
            free(route); compute_routes();
            if (gen && relax == 2) cov2 = holes_count();
            long nc = 0; for (size_t i = 0; i < npairs; i++) if (cnt[i] != 255 && bad(i)) nc++;
            nc /= 2;
            long d = nc - cost + (relax == 2 ? penw * (cov2 - covpen) : 0);
            double u = (rnd() >> 11) * (1.0 / 9007199254740992.0);
            if (d <= 0 || u < exp(-d / temp)) { cost = nc; if (relax == 2) covpen = cov2; nswapacc++;
                if (cost + penw * covpen < best && covpen == 0) { best = cost; memcpy(bestnu, nu, NF); memcpy(bestsig, sig, sizeof(int) * Np); fprintf(stderr, "it %ld temp %.3f cost %ld (swap)\n", it, temp, cost); if (best < 5) write_out(best, bestnu, bestsig); } }
            else { sig[p1] = l1; sig[p2] = l2; sinv[l1] = p1; sinv[l2] = p2; memcpy(route, route_bak, npairs); if (gen) memcpy(rc, rc_bak, npairs); }
            if (rc_bak) free(rc_bak);
            continue;
        }
        int f = rnd() % NF;
        if (ptarg > 0) {   /* targeted: a flag on a geodesic of a currently bad pair (list refreshed every 4096 its) */
            if ((it & 4095) == 0) { nbl = 0;
                for (int a = 0; a < V && nbl < 256; a++) { int cls = a >= Np; for (int b = a + 1; b < (cls + 1) * Np && nbl < 256; b++) { size_t i = pidx(a, b); if (cnt[i] != 255 && bad(i)) { bla[nbl] = a; blb[nbl] = b; nbl++; } } } }
            if (nbl && (rnd() >> 11) * (1.0 / 9007199254740992.0) < ptarg) {
                int r = rnd() % nbl, a = bla[r], b = blb[r], cand[256], nc = 0;
                for (int k1 = 0; k1 < Q1; k1++) { int n1 = adj[a * Q1 + k1];
                    for (int k2 = 0; k2 < Q1; k2++) { int x = adj[n1 * Q1 + k2]; if (x == a) continue;
                        for (int k3 = 0; k3 < Q1; k3++) { int n2 = adj[x * Q1 + k3]; if (n2 == n1) continue;
                            for (int k4 = 0; k4 < Q1; k4++) if (adj[n2 * Q1 + k4] == b && nc < 252) {
                                cand[nc++] = flagof[a * Q1 + k1]; cand[nc++] = flagof[n1 * Q1 + k2]; cand[nc++] = flagof[x * Q1 + k3]; cand[nc++] = flagof[n2 * Q1 + k4]; } } } }
                if (nc) f = cand[rnd() % nc];
            }
        }
        long d = flip_delta(f, 0);
        double u = (rnd() >> 11) * (1.0 / 9007199254740992.0);
        if (d <= 0 || u < exp(-d / temp)) {
            flip_delta(f, 1); nu[f] ^= 1; cost += d;
            if (cost < best && covpen == 0) { best = cost; memcpy(bestnu, nu, NF); memcpy(bestsig, sig, sizeof(int) * Np); if (best < 50 || (it & 1023) == 0) fprintf(stderr, "it %ld temp %.3f cost %ld\n", it, temp, cost); if (best < 5) write_out(best, bestnu, bestsig); }
        }
    }
    if (getenv("EJECT") && best > 0 && best < 64) {
        /* restore the best state and recompute routes/counts, then the ejection search */
        memcpy(sig, bestsig, sizeof(int) * Np); for (int p = 0; p < Np; p++) sinv[sig[p]] = p; memcpy(nu, bestnu, NF);
        free(route); compute_routes(); for (int s2 = 0; s2 < V; s2++) count_source(s2);
        ej_cost = 0; for (size_t i = 0; i < npairs; i++) if (cnt[i] != 255 && bad(i)) ej_cost++; ej_cost /= 2;
        int D = atoi(getenv("EJECT")); long sl = getenv("EJSLACK") ? atol(getenv("EJSLACK")) : 3;
        fprintf(stderr, "eject: start cost %ld depth %d slack +%ld\n", ej_cost, D, sl);
        for (int dd = 1; dd <= D && ej_cost > 0; dd++) { long c0 = ej_cost; if (eject(dd, c0 + sl)) break; fprintf(stderr, "eject depth %d: no solution (%ld nodes)\n", dd, ej_nodes); }
        fprintf(stderr, "eject: final cost %ld (%ld nodes)\n", ej_cost, ej_nodes);
        if (ej_cost < best) { best = ej_cost; memcpy(bestnu, nu, NF); }
    }
    printf("RESULT dmfast q %d iters %ld best %ld (of %ld opposite pairs) swaps accepted %ld\n", q, it, best, opp, nswapacc);
    if (gen && best >= (1L << 40)) { memcpy(bestsig, bpsig, sizeof(int) * Np); memcpy(bestnu, bpnu, NF); fprintf(stderr, "GEN: no hole-free state; writing the best penalised state (%ld)\n", bestpen); }
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
