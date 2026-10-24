/* uhcheck.c: diameter check of the polygon cover GH(q) + j matchings over Z_m (m <= 64) with units, hub links and
   super-hubs. Generalizes ucheck12 (session cell-14-7, second session, 2026-10-24).
   Lift (x,g) ~ (w, g+h) (cyclic group, h = voltage of the dart x->w). A unit (p,t) deletes the matching edge
   (p, sigma_t(p)) from every copy and adds hubs z ~ {(p,c)}, z' ~ {(l,c)}, l = sigma_t(p).
   New vertices: hub z_i = 2i (line-like), z'_i = 2i+1 (point-like), i = 0..NU-1, then super-hubs 2NU.. 2NU+NS-1.
   EXTRAS file (optional): first line "NS", then lines "a b": an edge between new vertices a and b (any of them).
   The cyclic shift of copies fixes every new vertex, so checking the sources (x,0), x a base vertex, and every new
   vertex covers all pairs. Same-side targets need distance <= D-1, others <= D.
   Usage: uhcheck GHFILE STATE UNITFILE EXTRAS|- D [THREADS] [FIRST LAST]
   UNITFILE lines "p t" or "p t l" (l is checked against sigma_t(p) when given).
   Prints the number of (source, target) pairs at distance > D; exit 0 iff there are none.
   Compile: gcc -O3 -march=native -fopenmp -o uhcheck uhcheck.c */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <omp.h>
typedef uint64_t u64;
static int P, q, J, m, D, NV, deg, NU, NS, NX;   /* NX = 2NU + NS new vertices */
static int *nbr, *vin;
static int *up, *ul;                 /* unit point (base index), unit line (base index P + line) */
static int *xside;                   /* side of new vertex: 0 point-like, 1 line-like */
static int *xatt;                    /* base vertex attached to new vertex (all copies), or -1 */
static int *xadj, *xadjs;            /* new-new adjacency (CSR) */
static int *xlo0, *xn0, *xlo1, *xn1; /* new vertices of side 0 / side 1 lists */
static u64 FULL, HI[65], LO[65]; static int LN;
static inline u64 rot(u64 x, int h) { if (!h) return x; return ((x << h) & HI[h]) | ((x >> (m - h)) & LO[h]); }
static inline u64 lanefill(u64 x) { u64 r = 0; for (int i = 0; i < LN; i++) if ((x >> (i * m)) & FULL) r |= FULL << (i * m); return r; }
static int *battH, *battN;
static FILE *dumpf = NULL;   /* DUMP=file: missed pairs "k source target copy" (base sources only) */           /* base vertex -> list of new vertices attached (CSR over base vertices) */

static long long check_block(int kind, const int *srcl, int cnt, u64 *A, u64 *B, u64 *ZA, u64 *ZB) {
    /* kind 0: base sources srcl[] (same side); kind 1: new-vertex sources srcl[] (same side) */
    memset(A, 0, 8 * (size_t)NV); memset(ZA, 0, 8 * (size_t)NX);
    int side;
    if (kind == 0) { side = srcl[0] < P ? 0 : 1; for (int i = 0; i < cnt; i++) A[srcl[i]] |= 1ULL << (i * m); }
    else { side = xside[srcl[0]]; for (int i = 0; i < cnt; i++) ZA[srcl[i]] |= FULL << (i * m); }
    u64 used = 0; for (int i = 0; i < cnt; i++) used |= FULL << (i * m);
    u64 *cur = A, *nxt = B, *zc = ZA, *zn = ZB;
    long long miss = 0;
    for (int k = 1; k <= D; k++) {
        int ns = side ^ (k & 1); int lo = ns ? P : 0, hi = ns ? NV : P;
        for (int w = lo; w < hi; w++) {
            const int *nb = nbr + (size_t)w * deg; const int *vi = vin + (size_t)w * deg; u64 r = 0;
            for (int s = 0; s < deg; s++) { int x = nb[s]; if (x >= 0) { u64 v = cur[x]; if (v) r |= rot(v, vi[s]); } }
            for (int e = battH[w]; e < battH[w + 1]; e++) r |= zc[battN[e]];
            nxt[w] = r;
        }
        memset(zn, 0, 8 * (size_t)NX);
        for (int v = 0; v < NX; v++) if (xside[v] == ns) {
            u64 r = 0; if (xatt[v] >= 0) r |= lanefill(cur[xatt[v]]);
            for (int e = xadjs[v]; e < xadjs[v + 1]; e++) r |= zc[xadj[e]];
            zn[v] = r;
        }
        u64 *t = cur; cur = nxt; nxt = t; u64 *tz = zc; zc = zn; zn = tz;
        if (k >= D - 1) {
            for (int w = lo; w < hi; w++) miss += __builtin_popcountll(used & ~cur[w]);
            if (dumpf && kind == 0) {
                #pragma omp critical
                for (int w = lo; w < hi; w++) { u64 mm = used & ~cur[w]; while (mm) { int b = __builtin_ctzll(mm); mm &= mm - 1;
                    fprintf(dumpf, "%d %d %d %d\n", k, srcl[b / m], w, b % m); } }
            }
            for (int v = 0; v < NX; v++) if (xside[v] == ns) miss += __builtin_popcountll(used & ~zc[v]) / m;
        }
    }
    return miss;
}

int main(int argc, char **argv) {
    if (argc < 6) { fprintf(stderr, "usage: uhcheck GHFILE STATE UNITFILE EXTRAS|- D [THREADS] [FIRST LAST]\n"); return 2; }
    FILE *f = fopen(argv[1], "r"); if (!f || fscanf(f, "%d %d", &P, &q) != 2) return 2;
    int *lines = malloc(sizeof(int) * (size_t)P * (q + 1));
    for (size_t i = 0; i < (size_t)P * (q + 1); i++) if (fscanf(f, "%d", &lines[i]) != 1) return 2;
    fclose(f);
    D = atoi(argv[5]); int nth = argc > 6 ? atoi(argv[6]) : 1;
    f = fopen(argv[2], "r"); int qq, dd; char gbuf[256];
    if (!f || fscanf(f, "glift %d %d %d %d\n", &qq, &J, &m, &dd) != 4 || qq != q) { fprintf(stderr, "bad state\n"); return 2; }
    if (!fgets(gbuf, sizeof gbuf, f) || strncmp(gbuf, "cyc", 3)) { fprintf(stderr, "only cyclic groups\n"); return 2; }
    int *sig = malloc(sizeof(int) * (size_t)J * P), *hv = malloc(sizeof(int) * (size_t)J * P);
    for (int p = 0; p < P; p++) for (int t = 0; t < J; t++) if (fscanf(f, "%d %d", &sig[t * P + p], &hv[t * P + p]) != 2) return 2;
    int *fv = malloc(sizeof(int) * (size_t)P * (q + 1));
    for (size_t i = 0; i < (size_t)P * (q + 1); i++) if (fscanf(f, "%d", &fv[i]) != 1) return 2;
    fclose(f);
    /* units */
    int cap = 1 << 16; up = malloc(sizeof(int) * cap); ul = malloc(sizeof(int) * cap); int *ut = malloc(sizeof(int) * cap);
    NU = 0; f = fopen(argv[3], "r"); char lb[256];
    while (f && fgets(lb, sizeof lb, f)) { int a, b, c; int k = sscanf(lb, "%d %d %d", &a, &b, &c); if (k < 2) continue;
        up[NU] = a; ut[NU] = b - 1; ul[NU] = P + sig[(b - 1) * P + a];
        if (k == 3 && c != sig[(b - 1) * P + a]) { fprintf(stderr, "unit %d: line %d is not sigma_%d(%d) = %d\n", NU, c, b, a, sig[(b - 1) * P + a]); return 1; }
        NU++; }
    if (f) fclose(f);
    /* extras */
    NS = 0; int nxe = 0; int *xea = malloc(sizeof(int) * cap), *xeb = malloc(sizeof(int) * cap);
    if (strcmp(argv[4], "-")) { f = fopen(argv[4], "r"); if (!f || fscanf(f, "%d", &NS) != 1) { fprintf(stderr, "bad extras\n"); return 2; }
        int a, b; while (fscanf(f, "%d %d", &a, &b) == 2) { xea[nxe] = a; xeb[nxe] = b; nxe++; } fclose(f); }
    NX = 2 * NU + NS;
    xside = malloc(sizeof(int) * (NX + 1)); xatt = malloc(sizeof(int) * (NX + 1));
    for (int i = 0; i < NU; i++) { xside[2 * i] = 1; xatt[2 * i] = up[i]; xside[2 * i + 1] = 0; xatt[2 * i + 1] = ul[i]; }
    for (int s = 0; s < NS; s++) { xside[2 * NU + s] = -1; xatt[2 * NU + s] = -1; }
    /* sides of super-hubs from their neighbours */
    for (int pass = 0; pass < 4; pass++) for (int e = 0; e < nxe; e++) { int a = xea[e], b = xeb[e];
        if (a < 0 || b < 0 || a >= NX || b >= NX || a == b) { fprintf(stderr, "bad extra edge %d %d\n", a, b); return 2; }
        if (xside[a] >= 0 && xside[b] < 0) xside[b] = 1 - xside[a]; if (xside[b] >= 0 && xside[a] < 0) xside[a] = 1 - xside[b]; }
    for (int v = 0; v < NX; v++) if (xside[v] < 0) { fprintf(stderr, "new vertex %d has no side\n", v); return 2; }
    for (int e = 0; e < nxe; e++) if (xside[xea[e]] == xside[xeb[e]]) { fprintf(stderr, "extra edge %d %d joins one side (not bipartite)\n", xea[e], xeb[e]); return 1; }
    xadjs = calloc(NX + 1, sizeof(int)); for (int e = 0; e < nxe; e++) { xadjs[xea[e] + 1]++; xadjs[xeb[e] + 1]++; }
    for (int v = 0; v < NX; v++) xadjs[v + 1] += xadjs[v];
    xadj = malloc(sizeof(int) * (2 * nxe + 1)); { int *pos = calloc(NX, sizeof(int));
        for (int e = 0; e < nxe; e++) { int a = xea[e], b = xeb[e]; xadj[xadjs[a] + pos[a]++] = b; xadj[xadjs[b] + pos[b]++] = a; } free(pos); }
    /* duplicate new-new edges? */
    for (int v = 0; v < NX; v++) for (int e = xadjs[v]; e < xadjs[v + 1]; e++) for (int e2 = e + 1; e2 < xadjs[v + 1]; e2++) if (xadj[e] == xadj[e2]) { fprintf(stderr, "repeated extra edge at %d\n", v); return 1; }
    NV = 2 * P; deg = q + 1 + J; FULL = m == 64 ? ~0ULL : ((1ULL << m) - 1);
    LN = 64 / m;
    for (int h = 0; h <= m; h++) { HI[h] = 0; LO[h] = 0; for (int i = 0; i < LN; i++) for (int bpos = 0; bpos < m; bpos++) { if (bpos >= h) HI[h] |= 1ULL << (i * m + bpos); else LO[h] |= 1ULL << (i * m + bpos); } }
    nbr = malloc(sizeof(int) * (size_t)NV * deg); vin = malloc(sizeof(int) * (size_t)NV * deg);
    int *cnt = calloc(NV, sizeof(int));
    for (int l = 0; l < P; l++) for (int k = 0; k <= q; k++) { int p = lines[l * (q + 1) + k], h = fv[l * (q + 1) + k];
        nbr[(size_t)p * deg + cnt[p]] = P + l; vin[(size_t)p * deg + cnt[p]] = (m - h) % m; cnt[p]++;
        nbr[(size_t)(P + l) * deg + cnt[P + l]] = p; vin[(size_t)(P + l) * deg + cnt[P + l]] = h; cnt[P + l]++; }
    char *del = calloc((size_t)J * P, 1);
    for (int i = 0; i < NU; i++) { if (del[ut[i] * P + up[i]]) { fprintf(stderr, "unit %d repeated\n", i); return 1; } del[ut[i] * P + up[i]] = 1; }
    long long ndel = 0;
    for (int t = 0; t < J; t++) for (int p = 0; p < P; p++) { int l = sig[t * P + p], h = hv[t * P + p];
        int x = del[t * P + p] ? -1 : P + l, y = del[t * P + p] ? -1 : p; if (del[t * P + p]) ndel++;
        nbr[(size_t)p * deg + cnt[p]] = x; vin[(size_t)p * deg + cnt[p]] = (m - h) % m; cnt[p]++;
        nbr[(size_t)(P + l) * deg + cnt[P + l]] = y; vin[(size_t)(P + l) * deg + cnt[P + l]] = h; cnt[P + l]++; }
    for (int v = 0; v < NV; v++) if (cnt[v] != deg) { fprintf(stderr, "degree error at %d\n", v); return 1; }
    for (int t = 0; t < J; t++) { char *seen = calloc(P, 1); for (int p = 0; p < P; p++) { if (seen[sig[t * P + p]]) { fprintf(stderr, "sigma_%d not a bijection\n", t + 1); return 1; } seen[sig[t * P + p]] = 1; } free(seen); }
    /* base vertex -> attached new vertices */
    battH = calloc(NV + 1, sizeof(int)); for (int v = 0; v < NX; v++) if (xatt[v] >= 0) battH[xatt[v] + 1]++;
    for (int w = 0; w < NV; w++) battH[w + 1] += battH[w];
    battN = malloc(sizeof(int) * (NX + 1)); { int *pos = calloc(NV, sizeof(int)); for (int v = 0; v < NX; v++) if (xatt[v] >= 0) battN[battH[xatt[v]] + pos[xatt[v]]++] = v; free(pos); }
    /* degrees: base vertices: deg - (deleted slots) + attached hubs <= deg; new vertices: m*(att) + extra edges <= deg */
    int maxdeg = 0, badd = 0;
    for (int w = 0; w < NV; w++) { int dg = battH[w + 1] - battH[w]; for (int s = 0; s < deg; s++) if (nbr[(size_t)w * deg + s] >= 0) dg++; if (dg > deg) badd++; if (dg > maxdeg) maxdeg = dg; }
    for (int v = 0; v < NX; v++) { int dg = (xatt[v] >= 0 ? m : 0) + xadjs[v + 1] - xadjs[v]; if (dg > deg) badd++; if (dg > maxdeg) maxdeg = dg; }
    if (badd) { fprintf(stderr, "%d vertices exceed degree %d\n", badd, deg); return 1; }
    int first = argc > 8 ? atoi(argv[7]) : 0, last = argc > 8 ? atoi(argv[8]) : NV;
    if (getenv("DUMP")) dumpf = fopen(getenv("DUMP"), "w");
    double t0 = omp_get_wtime(); long long tot = 0, nbadsrc = 0, done = 0, totx = 0;
    int nblk = 0; int *bstart = malloc(sizeof(int) * (NV / LN + 4)), *bcnt = malloc(sizeof(int) * (NV / LN + 4));
    int *srcv = NULL;
    if (getenv("ONLYUNITS")) {   /* only the unit endpoints as base sources (search mode; the full check needs all) */
        char *isS = calloc(NV, 1); for (int i = 0; i < NU; i++) { isS[up[i]] = 1; isS[ul[i]] = 1; }
        srcv = malloc(sizeof(int) * NV); int ns2 = 0; for (int v = 0; v < NV; v++) if (isS[v]) srcv[ns2++] = v;
        for (int s = 0; s < ns2; ) { int e = s + LN; if (e > ns2) e = ns2; while (e > s + 1 && (srcv[e - 1] < P) != (srcv[s] < P)) e--; bstart[nblk] = s; bcnt[nblk] = e - s; nblk++; s = e; }
        free(isS);
    } else
    for (int s = first; s < last; ) { int e = s + LN; if (e > last) e = last; if (s < P && e > P) e = P; bstart[nblk] = s; bcnt[nblk] = e - s; nblk++; s = e; }
    /* new-vertex source blocks, grouped by side */
    int *xs0 = malloc(sizeof(int) * (NX + 1)), *xs1 = malloc(sizeof(int) * (NX + 1)), n0 = 0, n1 = 0;
    for (int v = 0; v < NX; v++) { if (xside[v]) xs1[n1++] = v; else xs0[n0++] = v; }
    #pragma omp parallel num_threads(nth) reduction(+:tot, nbadsrc, totx)
    {
        u64 *A = malloc(8 * (size_t)NV), *B = malloc(8 * (size_t)NV), *ZA = malloc(8 * (size_t)NX + 8), *ZB = malloc(8 * (size_t)NX + 8);
        int sl[64];
        #pragma omp for schedule(dynamic, 16)
        for (int bi = 0; bi < nblk; bi++) {
            for (int i = 0; i < bcnt[bi]; i++) sl[i] = srcv ? srcv[bstart[bi] + i] : bstart[bi] + i;
            long long c = check_block(0, sl, bcnt[bi], A, B, ZA, ZB); tot += c; if (c) nbadsrc++;
            long long d;
            #pragma omp atomic capture
            d = ++done;
            if (d % 4000 == 0) { fprintf(stderr, "  %lld blocks of %d done, %.0fs\n", d, LN, omp_get_wtime() - t0); }
        }
        #pragma omp for schedule(dynamic, 1)
        for (int kk = 0; kk < 2; kk++) {
            int *xs = kk ? xs1 : xs0, nx = kk ? n1 : n0;
            for (int i0 = 0; i0 < nx; i0 += LN) { int c0 = nx - i0 < LN ? nx - i0 : LN; for (int i = 0; i < c0; i++) sl[i] = xs[i0 + i];
                long long c = check_block(1, sl, c0, A, B, ZA, ZB); tot += c; totx += c; if (c) nbadsrc++; }
        }
    }
    printf("uhcheck q=%d j=%d m=%d D=%d units=%d superhubs=%d extra_edges=%d deleted_base_edges=%lld lift_vertices=%lld max_degree=%d "
           "sources %d..%d (+%d new vertices): pairs beyond D = %lld (from new-vertex sources %lld), bad blocks %lld, %.1fs\n",
           q, J, m, D, NU, NS, nxe, ndel, (long long)NV * m + NX, maxdeg, first, last, NX, tot, totx, nbadsrc, omp_get_wtime() - t0);
    if (dumpf) fclose(dumpf);
    return tot ? 1 : 0;
}
