/* ucheck.c: diameter check of the polygon cover GH(q) + j matchings over Z_m (m <= 64) with units.
   Lift (x,g) ~ (w, g+h) (cyclic group, h = voltage of the dart x->w). A unit (p,t) deletes the matching edge
   (p, sigma_t(p)) from every copy and adds z ~ {(p,c)} and z' ~ {(l,c)}, l = sigma_t(p).
   The cyclic shift (x,c) -> (x,c+1) is an automorphism fixing every z, z', so checking the sources (x,0) for all base
   vertices x and the sources z_i, z'_i covers all pairs. Same-side targets need distance <= D-1, others <= D.
   Usage: ucheck GHFILE STATE UNITFILE D [THREADS] [FIRST LAST]   (sources FIRST..LAST-1 of the base vertices, then
   all unit vertices; default all). Prints the number of (source, target) pairs at distance > D. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <omp.h>
typedef uint64_t u64;
static int P, q, J, m, D, NV, deg, NU;
static int *nbr, *vin;       /* base slots; nbr = -1 for deleted slots */
static int *up, *ul;         /* unit point p_i (base index), unit line l_i (base index P+line) */
static int *isUP, *isUL;     /* base vertex -> unit index list head (-1 if none); allow several units per vertex */
static int *nextUP, *nextUL;
static u64 FULL, FULLALL, HI[65], LO[65]; static int LN;
static inline u64 rot(u64 x, int h) { if (!h) return x; return ((x << h) & HI[h]) | ((x >> (m - h)) & LO[h]); }
static inline u64 lanefill(u64 x) { u64 r = 0; for (int i = 0; i < LN; i++) if ((x >> (i * m)) & FULL) r |= FULL << (i * m); return r; }

static long long check_block(int kind, const int *srcl, int cnt, u64 *A, u64 *B, u64 *ZA, u64 *ZB) {
    /* kind 0: base sources srcl[0..cnt-1] (same side); kind 1: z_{srcl[i]}; kind 2: z'_{srcl[i]}; lane i = source i */
    memset(A, 0, 8 * (size_t)NV); memset(ZA, 0, 16 * (size_t)NU);
    int side;
    if (kind == 0) { side = srcl[0] < P ? 0 : 1; for (int i = 0; i < cnt; i++) A[srcl[i]] |= 1ULL << (i * m); }
    else if (kind == 1) { side = 1; for (int i = 0; i < cnt; i++) ZA[2 * srcl[i]] |= FULL << (i * m); }
    else { side = 0; for (int i = 0; i < cnt; i++) ZA[2 * srcl[i] + 1] |= FULL << (i * m); }
    u64 used = 0; for (int i = 0; i < cnt; i++) used |= FULL << (i * m);
    u64 *cur = A, *nxt = B, *zc = ZA, *zn = ZB;
    long long miss = 0;
    for (int k = 1; k <= D; k++) {
        int ns = side ^ (k & 1); int lo = ns ? P : 0, hi = ns ? NV : P;
        memset(zn, 0, 16 * (size_t)NU);
        for (int w = lo; w < hi; w++) {
            const int *nb = nbr + (size_t)w * deg; const int *vi = vin + (size_t)w * deg; u64 r = 0;
            for (int s = 0; s < deg; s++) { int x = nb[s]; if (x >= 0) { u64 v = cur[x]; if (v) r |= rot(v, vi[s]); } }
            nxt[w] = r;
        }
        for (int i = 0; i < NU; i++) {
            if (ns == 1) zn[2 * i] = lanefill(cur[up[i]]);
            else zn[2 * i + 1] = lanefill(cur[ul[i]]);
        }
        for (int i = 0; i < NU; i++) {
            if (ns == 0) nxt[up[i]] |= zc[2 * i];
            if (ns == 1) nxt[ul[i]] |= zc[2 * i + 1];
        }
        u64 *t = cur; cur = nxt; nxt = t; u64 *tz = zc; zc = zn; zn = tz;
        if (k >= D - 1) {
            for (int w = lo; w < hi; w++) miss += __builtin_popcountll(used & ~cur[w]);
            for (int i = 0; i < NU; i++) { if (ns == 1) miss += __builtin_popcountll(used & ~zc[2 * i]) / m; if (ns == 0) miss += __builtin_popcountll(used & ~zc[2 * i + 1]) / m; }
        }
    }
    return miss;
}

int main(int argc, char **argv) {
    if (argc < 5) { fprintf(stderr, "usage: ucheck GHFILE STATE UNITFILE D [THREADS] [FIRST LAST]\n"); return 2; }
    FILE *f = fopen(argv[1], "r"); if (!f || fscanf(f, "%d %d", &P, &q) != 2) return 2;
    int *lines = malloc(sizeof(int) * (size_t)P * (q + 1));
    for (size_t i = 0; i < (size_t)P * (q + 1); i++) if (fscanf(f, "%d", &lines[i]) != 1) return 2;
    fclose(f);
    D = atoi(argv[4]); int nth = argc > 5 ? atoi(argv[5]) : 1;
    f = fopen(argv[2], "r"); int qq, dd; char gbuf[256];
    if (!f || fscanf(f, "glift %d %d %d %d\n", &qq, &J, &m, &dd) != 4 || qq != q) { fprintf(stderr, "bad state\n"); return 2; }
    if (!fgets(gbuf, sizeof gbuf, f) || strncmp(gbuf, "cyc", 3)) { fprintf(stderr, "only cyclic groups\n"); return 2; }
    int *sig = malloc(sizeof(int) * (size_t)J * P), *hv = malloc(sizeof(int) * (size_t)J * P);
    for (int p = 0; p < P; p++) for (int t = 0; t < J; t++) if (fscanf(f, "%d %d", &sig[t * P + p], &hv[t * P + p]) != 2) return 2;
    int *fv = malloc(sizeof(int) * (size_t)P * (q + 1));
    for (size_t i = 0; i < (size_t)P * (q + 1); i++) if (fscanf(f, "%d", &fv[i]) != 1) return 2;
    fclose(f);
    /* units */
    f = fopen(argv[3], "r"); int cap = 1024; up = malloc(sizeof(int) * cap); ul = malloc(sizeof(int) * cap); int *ut = malloc(sizeof(int) * cap);
    NU = 0; int a, b; while (f && fscanf(f, "%d %d", &a, &b) == 2) { up[NU] = a; ut[NU] = b - 1; ul[NU] = P + sig[(b - 1) * P + a]; NU++; }
    if (f) fclose(f);
    NV = 2 * P; deg = q + 1 + J; FULL = m == 64 ? ~0ULL : ((1ULL << m) - 1);
    LN = 64 / m; FULLALL = 0; for (int i = 0; i < LN; i++) FULLALL |= FULL << (i * m);
    for (int h = 0; h <= m; h++) { HI[h] = 0; LO[h] = 0; for (int i = 0; i < LN; i++) for (int bpos = 0; bpos < m; bpos++) { if (bpos >= h) HI[h] |= 1ULL << (i * m + bpos); else LO[h] |= 1ULL << (i * m + bpos); } }
    nbr = malloc(sizeof(int) * (size_t)NV * deg); vin = malloc(sizeof(int) * (size_t)NV * deg);
    int *cnt = calloc(NV, sizeof(int));
    for (int l = 0; l < P; l++) for (int k = 0; k <= q; k++) { int p = lines[l * (q + 1) + k], h = fv[l * (q + 1) + k];
        nbr[(size_t)p * deg + cnt[p]] = P + l; vin[(size_t)p * deg + cnt[p]] = (m - h) % m; cnt[p]++;
        nbr[(size_t)(P + l) * deg + cnt[P + l]] = p; vin[(size_t)(P + l) * deg + cnt[P + l]] = h; cnt[P + l]++; }
    char *del = calloc((size_t)J * P, 1);
    for (int i = 0; i < NU; i++) del[ut[i] * P + up[i]] = 1;
    long long ndel = 0;
    for (int t = 0; t < J; t++) for (int p = 0; p < P; p++) { int l = sig[t * P + p], h = hv[t * P + p];
        int x = del[t * P + p] ? -1 : P + l, y = del[t * P + p] ? -1 : p; if (del[t * P + p]) ndel++;
        nbr[(size_t)p * deg + cnt[p]] = x; vin[(size_t)p * deg + cnt[p]] = (m - h) % m; cnt[p]++;
        nbr[(size_t)(P + l) * deg + cnt[P + l]] = y; vin[(size_t)(P + l) * deg + cnt[P + l]] = h; cnt[P + l]++; }
    for (int v = 0; v < NV; v++) if (cnt[v] != deg) { fprintf(stderr, "degree error at %d\n", v); return 1; }
    /* sanity: every sigma_t is a bijection */
    for (int t = 0; t < J; t++) { char *seen = calloc(P, 1); for (int p = 0; p < P; p++) { if (seen[sig[t * P + p]]) { fprintf(stderr, "sigma_%d not a bijection\n", t + 1); return 1; } seen[sig[t * P + p]] = 1; } free(seen); }
    int first = argc > 7 ? atoi(argv[6]) : 0, last = argc > 7 ? atoi(argv[7]) : NV;
    double t0 = omp_get_wtime(); long long tot = 0, nbadsrc = 0, done = 0;
    /* blocks of LN sources of the same side */
    int nblk = 0; int *bstart = malloc(sizeof(int) * (NV / LN + 4)), *bcnt = malloc(sizeof(int) * (NV / LN + 4));
    for (int s = first; s < last; ) { int e = s + LN; if (e > last) e = last; if (s < P && e > P) e = P; bstart[nblk] = s; bcnt[nblk] = e - s; nblk++; s = e; }
    #pragma omp parallel num_threads(nth) reduction(+:tot, nbadsrc)
    {
        u64 *A = malloc(8 * (size_t)NV), *B = malloc(8 * (size_t)NV), *ZA = malloc(16 * (size_t)NU + 16), *ZB = malloc(16 * (size_t)NU + 16);
        int sl[64];
        #pragma omp for schedule(dynamic, 16)
        for (int bi = 0; bi < nblk; bi++) {
            for (int i = 0; i < bcnt[bi]; i++) sl[i] = bstart[bi] + i;
            long long c = check_block(0, sl, bcnt[bi], A, B, ZA, ZB); tot += c; if (c) nbadsrc++;
            long long d;
            #pragma omp atomic capture
            d = ++done;
            if (d % 2000 == 0) { fprintf(stderr, "  %lld blocks of %d done, %.0fs\n", d, LN, omp_get_wtime() - t0); }
        }
        #pragma omp for schedule(dynamic, 1)
        for (int kk = 1; kk <= 2; kk++) {
            for (int i0 = 0; i0 < NU; i0 += LN) { int c0 = NU - i0 < LN ? NU - i0 : LN; for (int i = 0; i < c0; i++) sl[i] = i0 + i;
                long long c = check_block(kk, sl, c0, A, B, ZA, ZB); tot += c; if (c) nbadsrc++; }
        }
    }
    printf("ucheck q=%d j=%d m=%d D=%d units=%d deleted_base_edges=%lld lift_vertices=%lld sources %d..%d (+%d unit vertices): pairs beyond D = %lld, bad blocks %lld, %.1fs\n",
           q, J, m, D, NU, ndel, (long long)NV * m + 2LL * NU, first, last, 2 * NU, tot, nbadsrc, omp_get_wtime() - t0);
    return tot ? 1 : 0;
}
