/* hcheck5.c -- card c5 of squad d16D10-r1: independent diameter checker for Haar graphs H(G,S),
 * G = SL(2,p) x Z_n. Written from the definitions in CARDS.md / PREAMBLE.md only.
 *
 * Definitions used:
 *   Vertices (g,A), (g,B); g = (M,z), M in SL(2,p) (2x2 over F_p, det 1), z in Z_n.  |V| = 2N, N = p(p^2-1) n.
 *   Edges (g,A) ~ (s g, B) for s = (M_s, z_s) in S, with s g = (M_s M, z_s + z).
 *     Equivalently (h,B) ~ (s^-1 h, A), where s^-1 = (adj M_s, -z_s) and adj[[a,b],[c,d]] = [[d,-b],[-c,a]].
 *   Right multiplication by k is an automorphism, so diameter <= D iff BFS from (e,A) and from (e,B)
 *   reaches all 2N vertices within D steps.
 * Element index of M = [[a,b],[c,d]]:  iM = (a p + b - 1) p + t,  t = c if a != 0 else d.
 *   This is a bijection onto [0, p(p^2-1)).  Group index = iM n + z (matches the idx column of the solution
 *   files; the loader checks it and reports mismatches).
 * Storage: one 2-bit field per vertex, so 4 bits per group element. Field 0 = unseen, 1 + (level mod 3) otherwise.
 *   BFS step L expands every field equal to 1 + (L mod 3). Vertices of levels L-3, L-6, ... are also expanded
 *   (they carry the same label); that is harmless because all their neighbours are labelled already.
 * Block layout: field of (iM, side X, z) is (iM*2 + X)*n + z, so the 2n fields of one SL element are contiguous.
 *   Expansion of a block side uses the matrix of iM once, then one target block per generator.
 * Parallelism: OpenMP over iM; new labels are written with atomic OR into zero fields only.
 *
 * build: gcc -O3 -march=native -fopenmp -o hcheck5 hcheck5.c
 * usage: THREADS=2 ./hcheck5 FILE
 *        THREADS=2 ./hcheck5 -synth p n d seed D [-steps K] [-one] [-v]   (random S, timing only, no file)
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <omp.h>
#include <sys/mman.h>

static uint32_t P;             /* prime p */
static uint64_t NZ;            /* n */
static uint64_t NSL;           /* |SL(2,p)| = p(p^2-1) */
static uint64_t N2;            /* 2N = number of vertices */
static uint64_t NW;            /* 64-bit words, 32 fields each */
static uint64_t *W;            /* packed 2-bit fields */
static int nS;                 /* d = |S| */
static uint32_t GM[64][4], GMI[64][4];   /* matrices of s and of s^-1 (row-major a,b,c,d) */
static uint32_t GZ[64], GZI[64];         /* z of s and of s^-1 (mod n) */
static uint32_t *INV;          /* INV[x] = x^-1 mod p, x in [1,p) */
static uint64_t FMM;           /* Lemire fastmod constant for divisor p */
static uint32_t FMD;

static inline uint32_t fmodp(uint32_t x) {
    uint64_t low = FMM * (uint64_t)x;
    return (uint32_t)(((__uint128_t)low * FMD) >> 64);
}

/* matrix m (a,b,c,d) of det 1 from element index iM */
static inline void dec_sl(uint64_t iM, uint32_t *m) {
    uint64_t r = iM / P, t = iM - r * P;
    uint64_t q = r + 1;                       /* a p + b = q */
    uint32_t a = (uint32_t)(q / P), b = (uint32_t)(q - (uint64_t)a * P);
    uint32_t c, d;
    if (a) {
        c = (uint32_t)t;
        d = fmodp(fmodp(b * c + 1) * INV[a]);   /* d = (1 + bc)/a */
    } else {
        d = (uint32_t)t;
        c = P - INV[b];                         /* -b c = 1 */
    }
    m[0] = a; m[1] = b; m[2] = c; m[3] = d;
}

static inline uint64_t enc_sl(const uint32_t *m) {
    uint64_t r = (uint64_t)m[0] * P + m[1] - 1;
    uint64_t t = m[0] ? m[2] : m[3];
    return r * P + t;
}

/* o = s * m (2x2 mod p) */
static inline void mulmat(const uint32_t *s, const uint32_t *m, uint32_t *o) {
    o[0] = fmodp(s[0] * m[0] + s[1] * m[2]);
    o[1] = fmodp(s[0] * m[1] + s[1] * m[3]);
    o[2] = fmodp(s[2] * m[0] + s[3] * m[2]);
    o[3] = fmodp(s[2] * m[1] + s[3] * m[3]);
}

/* 1 if field f was 0 and is now set to vn, else 0 */
static inline uint64_t set_if_zero(uint64_t f, uint64_t vn) {
    uint64_t *wp = &W[f >> 5];
    unsigned sh = (unsigned)(f & 31) << 1;
    uint64_t cur = __atomic_load_n(wp, __ATOMIC_RELAXED);
    if ((cur >> sh) & 3) return 0;
    uint64_t old = __atomic_fetch_or(wp, vn << sh, __ATOMIC_RELAXED);
    return ((old >> sh) & 3) ? 0 : 1;
}

static inline uint64_t lowmask(unsigned j) {          /* bits of fields 0..j-1 */
    return j >= 32 ? ~0ULL : ((1ULL << (2 * j)) - 1);
}

/* bit 2j set iff field j of w equals v (v in 1..3) */
static inline uint64_t match_mask(uint64_t w, unsigned v) {
    const uint64_t L = 0x5555555555555555ULL;
    uint64_t b0 = w & L, b1 = (w >> 1) & L;
    uint64_t m0 = (v & 1) ? b0 : (~b0 & L);
    uint64_t m1 = (v & 2) ? b1 : (~b1 & L);
    return m0 & m1;
}

/* fields [lo,hi) equal to v: out[i] = field - lo */
static inline unsigned scan_hits(uint64_t lo, uint64_t hi, unsigned v, uint32_t *out) {
    unsigned cnt = 0;
    uint64_t f = lo;
    while (f < hi) {
        uint64_t wi = f >> 5, ws = wi << 5, we = ws + 32;
        uint64_t seg = hi < we ? hi : we;
        unsigned jlo = (unsigned)(f - ws), jhi = (unsigned)(seg - ws);
        uint64_t m = match_mask(__atomic_load_n(&W[wi], __ATOMIC_RELAXED), v);
        m &= lowmask(jhi) & ~lowmask(jlo);
        while (m) {
            unsigned pos = (unsigned)__builtin_ctzll(m) >> 1;
            out[cnt++] = (uint32_t)(ws + pos - lo);
            m &= m - 1;
        }
        f = seg;
    }
    return cnt;
}

static uint64_t g_hits, g_blocksides;   /* statistics of the last step */
static inline uint64_t xs64(uint64_t x) { x ^= x << 13; x ^= x >> 7; x ^= x << 17; return x; }
static uint64_t g_ilim;                 /* bench: only SL indices below this are expanded */

/* one BFS step: expand all fields == v, label new ones with vn */
static uint64_t bfs_step(unsigned v, unsigned vn) {
    uint64_t added = 0, hits = 0, bsides = 0;
    #pragma omp parallel reduction(+:added,hits,bsides)
    {
        uint32_t *hz = malloc(2 * NZ * sizeof(uint32_t));
        uint32_t m[4], o[4];
        #pragma omp for schedule(dynamic, 4096)
        for (uint64_t iM = 0; iM < g_ilim; iM++) {
            uint64_t base = iM * 2 * NZ;
            unsigned nh[2];
            nh[0] = scan_hits(base, base + NZ, v, hz);
            nh[1] = scan_hits(base + NZ, base + 2 * NZ, v, hz + NZ);
            if (!nh[0] && !nh[1]) continue;
            dec_sl(iM, m);
            for (int X = 0; X < 2; X++) {
                if (!nh[X]) continue;
                const uint32_t *hzX = hz + (uint64_t)X * NZ;
                uint32_t (*G)[4] = X ? GMI : GM;
                const uint32_t *ZS = X ? GZI : GZ;
                uint64_t tside = 1 - (uint64_t)X;
                bsides++;
                hits += nh[X];
                uint64_t tbv[64];
                for (int k = 0; k < nS; k++) {       /* all targets first, prefetched together */
                    mulmat(G[k], m, o);
                    tbv[k] = (enc_sl(o) * 2 + tside) * NZ;
                    __builtin_prefetch(&W[tbv[k] >> 5], 1);
                    __builtin_prefetch(&W[(tbv[k] + NZ - 1) >> 5], 1);
                }
                for (int k = 0; k < nS; k++) {
                    uint64_t tb = tbv[k];
                    uint64_t sh = ZS[k];
                    for (unsigned i = 0; i < nh[X]; i++) {
                        uint64_t zt = hzX[i] + sh;
                        if (zt >= NZ) zt -= NZ;
                        added += set_if_zero(tb + zt, vn);
                    }
                }
            }
        }
        free(hz);
    }
    g_hits = hits;
    g_blocksides = bsides;
    return added;
}

/* BFS from one source field to depth D. Returns 1 if all 2N vertices are reached within D. */
static int bfs_from(uint64_t src, unsigned D, unsigned *ecc, int verbose) {
    memset(W, 0, NW * sizeof(uint64_t));
    W[src >> 5] |= 1ULL << ((src & 31) * 2);       /* level 0: value 1 */
    uint64_t count = 1;
    for (unsigned L = 0; L < D; L++) {
        unsigned v = L % 3 + 1, vn = (L + 1) % 3 + 1;
        double t0 = omp_get_wtime();
        uint64_t added = bfs_step(v, vn);
        double t1 = omp_get_wtime();
        count += added;
        if (verbose)
            fprintf(stderr, "  step L=%u: expanded-blocksides=%llu hits=%llu new=%llu total=%llu  %.3f s\n",
                    L, (unsigned long long)g_blocksides, (unsigned long long)g_hits,
                    (unsigned long long)added, (unsigned long long)count, t1 - t0);
        if (count == N2) { *ecc = L + 1; return 1; }
        if (added == 0) return 0;                   /* level L+1 empty: component exhausted */
    }
    return 0;
}

static uint32_t powmod32(uint32_t x, uint32_t e, uint32_t m) {
    uint64_t r = 1, b = x % m;
    while (e) { if (e & 1) r = r * b % m; b = b * b % m; e >>= 1; }
    return (uint32_t)r;
}

static int is_prime(uint64_t x) {
    if (x < 2) return 0;
    for (uint64_t q = 2; q * q <= x; q++) if (x % q == 0) return 0;
    return 1;
}

static int setup(uint32_t p, uint64_t n) {
    if (p < 3 || p >= 46000 || !is_prime(p)) { fprintf(stderr, "bad p=%u\n", p); return 0; }
    if (n < 1 || n > (1u << 20)) { fprintf(stderr, "n=%llu out of range\n", (unsigned long long)n); return 0; }
    P = p; NZ = n;
    NSL = (uint64_t)p * ((uint64_t)p * p - 1);
    N2 = 2 * NSL * NZ;
    NW = (N2 + 31) / 32 + 1;
    FMD = P;
    FMM = UINT64_C(0xFFFFFFFFFFFFFFFF) / P + 1;
    INV = malloc((size_t)P * sizeof(uint32_t));
    INV[0] = 0;
    for (uint32_t x = 1; x < P; x++) INV[x] = powmod32(x, P - 2, P);
    return 1;
}

static int set_generator(int i, const uint32_t *m, uint64_t z) {
    uint32_t a = m[0], b = m[1], c = m[2], d = m[3];
    if (a >= P || b >= P || c >= P || d >= P) return 0;
    uint64_t det = ((uint64_t)a * d % P + P - (uint64_t)b * c % P) % P;   /* ad - bc mod p */
    if (det != 1) return 0;
    if (z >= NZ) return 0;
    GM[i][0] = a; GM[i][1] = b; GM[i][2] = c; GM[i][3] = d;
    GZ[i] = (uint32_t)z;
    GMI[i][0] = d; GMI[i][1] = (P - b) % P; GMI[i][2] = (P - c) % P; GMI[i][3] = a;
    GZI[i] = (uint32_t)((NZ - z) % NZ);
    return 1;
}

int main(int argc, char **argv) {
    const char *file = NULL;
    int synth = 0, one = 0, verbose = 0;
    double bench = 0;
    unsigned long sp = 0, sn = 0, sd = 0, sD = 0, sK = 0;
    unsigned long long sseed = 1;
    for (int i = 1; i < argc; i++) {
        if (!strcmp(argv[i], "-synth") && i + 5 < argc) {
            synth = 1;
            sp = strtoul(argv[++i], NULL, 10); sn = strtoul(argv[++i], NULL, 10);
            sd = strtoul(argv[++i], NULL, 10); sseed = strtoull(argv[++i], NULL, 10);
            sD = strtoul(argv[++i], NULL, 10);
        } else if (!strcmp(argv[i], "-steps") && i + 1 < argc) {
            sK = strtoul(argv[++i], NULL, 10);
        } else if (!strcmp(argv[i], "-one")) one = 1;
        else if (!strcmp(argv[i], "-v")) verbose = 1;
        else if (!strcmp(argv[i], "-bench") && i + 1 < argc) { bench = strtod(argv[++i], NULL); }
        else file = argv[i];
    }
    int th = getenv("THREADS") ? atoi(getenv("THREADS")) : 2;
    if (th < 1) th = 1;
    if (th > 2) th = 2;                              /* card rule: at most 2 threads */
    omp_set_num_threads(th);

    unsigned long long Nfile = 0;
    unsigned D = 0;
    int d = 0;
    uint64_t gidx[64];

    if (synth) {
        if (!setup((uint32_t)sp, sn)) return 2;
        nS = (int)sd;
        uint64_t rs = sseed * 6364136223846793005ULL + 1442695040888963407ULL;
        for (int i = 0; i < nS; i++) {
            rs = rs * 6364136223846793005ULL + 1442695040888963407ULL;
            uint64_t iM = (rs >> 17) % NSL;
            uint32_t m[4];
            dec_sl(iM, m);
            rs = rs * 6364136223846793005ULL + 1442695040888963407ULL;
            uint64_t z = (rs >> 17) % NZ;
            set_generator(i, m, z);
        }
        D = (unsigned)sD;
        fprintf(stderr, "synthetic S: p=%u n=%llu d=%d seed=%llu (timing only)\n", P, (unsigned long long)NZ, nS, sseed);
    } else {
        if (!file) { fprintf(stderr, "usage: %s FILE | -synth p n d seed D\n", argv[0]); return 2; }
        FILE *fp = fopen(file, "r");
        if (!fp) { perror(file); return 2; }
        char line[4096], tag1[32], tag2[32];
        if (!fgets(line, sizeof line, fp)) { fprintf(stderr, "empty file\n"); return 2; }
        int dd, DD; unsigned long pl; unsigned long long nn;
        if (sscanf(line, "%d %d %31s %lu %31s %llu", &dd, &DD, tag1, &pl, tag2, &nn) != 6 ||
            strcmp(tag1, "sl") || strcmp(tag2, "n")) {
            fprintf(stderr, "bad header: %s", line); return 2;
        }
        char *q = strstr(line, " N ");
        if (q) sscanf(q + 3, "%llu", &Nfile);
        if (!setup((uint32_t)pl, nn)) return 2;
        if (Nfile && Nfile != NSL * NZ) { fprintf(stderr, "header N=%llu != p(p^2-1)n=%llu\n", Nfile, (unsigned long long)(NSL * NZ)); return 2; }
        if (dd < 1 || dd > 64) { fprintf(stderr, "bad d\n"); return 2; }
        d = dd; nS = dd; D = (unsigned)DD;
        int idx_bad = 0;
        for (int i = 0; i < dd; i++) {
            if (!fgets(line, sizeof line, fp)) { fprintf(stderr, "missing generator line\n"); return 2; }
            unsigned long long idx, z; unsigned a, b, c, dm;
            if (sscanf(line, "%llu mat(%u,%u,%u,%u) z=%llu", &idx, &a, &b, &c, &dm, &z) != 6) {
                fprintf(stderr, "bad generator line: %s", line); return 2;
            }
            uint32_t m[4] = {a, b, c, dm};
            if (!set_generator(i, m, z)) { fprintf(stderr, "generator %d not in SL(2,p) x Z_n\n", i); return 2; }
            gidx[i] = idx;
            uint32_t mm[4] = {a, b, c, dm};
            if (idx != enc_sl(mm) * NZ + z) idx_bad++;
        }
        fclose(fp);
        fprintf(stderr, "loaded %s: d=%d D=%u p=%u n=%llu N=%llu; idx-column mismatches=%d\n",
                file, d, D, P, (unsigned long long)NZ, (unsigned long long)(NSL * NZ), idx_bad);
        int distinct = 1;
        for (int i = 0; i < dd && distinct; i++)
            for (int j = i + 1; j < dd; j++)
                if (!memcmp(GM[i], GM[j], sizeof GM[i]) && GZ[i] == GZ[j]) { distinct = 0; break; }
        fprintf(stderr, "generators distinct: %s\n", distinct ? "yes" : "no");
    }

    if (sK && sK < D) D = (unsigned)sK;

    {
        size_t bytes = (size_t)NW * sizeof(uint64_t);
        size_t al = (size_t)1 << 21;
        bytes = (bytes + al - 1) / al * al;
        if (posix_memalign((void **)&W, al, bytes)) { fprintf(stderr, "out of memory (%.2f GB)\n", bytes / 1e9); return 2; }
        madvise(W, bytes, MADV_HUGEPAGE);       /* THP is in madvise mode on this host */
        memset(W, 0, bytes);
    }

    g_ilim = NSL;
    if (bench > 0) {
        /* timing at full memory size: random labels (about 1/4 of fields = 1), then one expansion step over a
           fraction of the SL indices */
        #pragma omp parallel for schedule(static)
        for (uint64_t i = 0; i < NW; i++) {
            uint64_t s = 0x9E3779B97F4A7C15ULL * (i + 1) + 1;
            uint64_t r1 = xs64(s), r2 = xs64(r1), r3 = xs64(r2), r4 = xs64(r3);
            uint64_t b0 = (r1 | r2) & 0x5555555555555555ULL, b1 = (r3 | r4) & 0x5555555555555555ULL;
            W[i] = b0 | (b1 << 1);     /* field values: 0 ~6%, 1 ~19%, 2 ~19%, 3 ~56% */
        }
        g_ilim = (uint64_t)(bench * (double)NSL);
        double tb0 = omp_get_wtime();
        uint64_t added = bfs_step(1, 2);
        double tb1 = omp_get_wtime() - tb0;
        printf("BENCH p=%u n=%llu N=%llu bytes_W=%.2fGB frac=%.4f threads=%d step_time=%.3f hits=%llu blocksides=%llu new=%llu ns_per_attempt=%.3f\n",
               P, (unsigned long long)NZ, (unsigned long long)(NSL * NZ), NW * 8.0 / 1e9, bench, th, tb1,
               (unsigned long long)g_hits, (unsigned long long)g_blocksides, (unsigned long long)added,
               tb1 * th * 1e9 / ((double)g_hits * nS));
        free(W);
        return 0;
    }
    uint32_t e[4] = {1, 0, 0, 1};
    uint64_t iE = enc_sl(e);
    uint64_t srcA = (iE * 2 + 0) * NZ + 0;
    uint64_t srcB = (iE * 2 + 1) * NZ + 0;

    double t0 = omp_get_wtime();
    unsigned eccA = 0, eccB = 0;
    int okA = bfs_from(srcA, D, &eccA, verbose);
    double tA = omp_get_wtime() - t0;
    fprintf(stderr, "from (e,A): %s within %u, ecc %u (%.3f s)\n", okA ? "all reached" : "NOT all reached", D,
            okA ? eccA : 0u, tA);
    int okB = 0;
    double tB = 0;
    if (!one) {
        double t1 = omp_get_wtime();
        okB = bfs_from(srcB, D, &eccB, verbose);
        tB = omp_get_wtime() - t1;
        fprintf(stderr, "from (e,B): %s within %u, ecc %u (%.3f s)\n", okB ? "all reached" : "NOT all reached", D,
                okB ? eccB : 0u, tB);
    } else {
        okB = 1;
    }
    double total = omp_get_wtime() - t0;
    int valid = okA && okB;
    printf("%s d=%d D=%u group=sl %u x Z_%llu N=%llu vertices=%llu threads=%d time=%.3f bfs_A=%.3f bfs_B=%.3f\n",
           valid ? "VALID" : "INVALID", nS, D, P, (unsigned long long)NZ, (unsigned long long)(NSL * NZ),
           (unsigned long long)N2, th, total, tA, tB);
    (void)gidx; (void)d;
    free(W);
    return valid ? 0 : 1;
}
