/* fixk.c -- squad round 2, card c3 (squad-r2-c3-haiku).
 * Fixed-k penalty search (min-conflict tabu, swap moves) for a clique of size k in
 *   G = Cay(F_11^4, { v : D(v) is a non-square mod 11 }),  D(s,b,c,f) = s^2 + 3c^2 + 8bf (mod 11).
 * Vertex (s,b,c,f) <-> index v = (s + 11b) + 121(c + 11f).  Vertex 0 = (0,0,0,0) is kept in K
 * (G is vertex-transitive, so no generality is lost).
 * cost = number of non-adjacent pairs inside K (K has exactly k vertices).
 * m[x] = #{y in K, y != x, y not adjacent to x}, maintained incrementally: adding/removing z changes m[w] for
 * the 7930 vertices w with w - z in NA (NA = nonzero non-edge differences; NA is symmetric since D(-d) = D(d)).
 * Swap (out y, in x): delta = m[x] - m[y] - [x,y non-adjacent].
 * Tabu: a vertex that left K may not re-enter for tenB + rnd(8) iterations; a vertex that entered may not leave for
 * 2 + rnd(3) iterations; aspiration when the move beats the best cost of the current run.
 * On cost 0 the clique is saved and k+1 is tried (one greedy vertex added).
 * Restarts after MAXNOIMP iterations without run improvement: half from the stage elite perturbed by 2..7 random
 * swaps, half from a fresh randomized greedy clique containing 0.
 * usage: fixk SEEDFILE|- KSTART CPU_SEC OUTDIR RNGSEED [MAXNOIMP] [TENB]
 *   SEEDFILE lines: "a b c e f" (offset; vertex (s,b,c,f) with s = (2a+e) mod 11) or "s b c f"; '#' lines ignored.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define H 121
#define NV 14641
#define MAXK 160

static unsigned char isEdge[NV];
static unsigned char ADD2[H * H], SUB2[H * H];
static int nNA, naLo[NV], naHi[NV];
static unsigned char m[NV];
static int K[MAXK], kn, posK[NV];
static long tabuIn[NV], tabuOut[NV];
static int cost;
static uint64_t rs = 88172645463325252ULL;
static int eliteK[MAXK], eliteN, eliteCost;
static int bufL[NV];
static int bestClique[MAXK], bestK = 0;
static unsigned char mark[NV];

static inline uint64_t rnd64(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline int rndn(int n) { return (int)((rnd64() >> 11) % (uint64_t)n); }
static inline int diffv(int x, int y) { return SUB2[(x % H) * H + (y % H)] + H * SUB2[(x / H) * H + (y / H)]; }
static inline int nonadj(int x, int y) { return !isEdge[diffv(x, y)]; }

static void init_tables(void) {
    int sq[11] = {0};
    for (int x = 1; x < 11; x++) sq[(x * x) % 11] = 1;
    for (int a = 0; a < H; a++)
        for (int b = 0; b < H; b++) {
            int a0 = a % 11, a1 = a / 11, b0 = b % 11, b1 = b / 11;
            ADD2[a * H + b] = (unsigned char)(((a0 + b0) % 11) + 11 * ((a1 + b1) % 11));
            SUB2[a * H + b] = (unsigned char)(((a0 - b0 + 11) % 11) + 11 * ((a1 - b1 + 11) % 11));
        }
    for (int v = 0; v < NV; v++) {
        int lo = v % H, hi = v / H;
        int s = lo % 11, b = lo / 11, c = hi % 11, f = hi / 11;
        int D = (s * s + 3 * c * c + 8 * b * f) % 11;
        isEdge[v] = (unsigned char)(D != 0 && !sq[D]);
    }
    nNA = 0;
    for (int d = 1; d < NV; d++)
        if (!isEdge[d]) { naLo[nNA] = d % H; naHi[nNA] = d / H; nNA++; }
}

/* m[w] += d for every w with w - z in NA */
static void upd(int z, int d) {
    const unsigned char *rl = ADD2 + (z % H) * H, *rh = ADD2 + (z / H) * H;
    if (d > 0)
        for (int j = 0; j < nNA; j++) m[rl[naLo[j]] + H * rh[naHi[j]]]++;
    else
        for (int j = 0; j < nNA; j++) m[rl[naLo[j]] + H * rh[naHi[j]]]--;
}

static void add_v(int x) { K[kn] = x; posK[x] = kn; kn++; upd(x, +1); }
static void rem_v(int y) {
    int p = posK[y], last = K[kn - 1];
    K[p] = last; posK[last] = p; kn--; posK[y] = -1; upd(y, -1);
}
static void clear_state(void) {
    memset(m, 0, sizeof m);
    for (int v = 0; v < NV; v++) posK[v] = -1;
    kn = 0; cost = 0;
}
static void set_state(const int *vs, int n) {
    clear_state();
    for (int i = 0; i < n; i++) { cost += m[vs[i]]; add_v(vs[i]); }
}
/* add an outside vertex of minimum m (random tie-break); cost grows by m */
static int greedy_add(void) {
    int mn = 255, cnt = 0, pick = -1;
    for (int v = 0; v < NV; v++)
        if (posK[v] < 0) {
            int mv = m[v];
            if (mv < mn) { mn = mv; cnt = 1; pick = v; }
            else if (mv == mn) { cnt++; if (rndn(cnt) == 0) pick = v; }
        }
    cost += mn; add_v(pick);
    return pick;
}
static void do_swap(int y, int x) { /* y in K (y != 0), x outside K */
    int d = m[x] - m[y] - nonadj(x, y);
    rem_v(y); add_v(x); cost += d;
}
static int recompute_cost(void) {
    int s = 0;
    for (int i = 0; i < kn; i++) s += m[K[i]];
    return s / 2;
}
static int is_clique(const int *vs, int n) {
    for (int i = 0; i < n; i++)
        for (int j = i + 1; j < n; j++)
            if (!isEdge[diffv(vs[i], vs[j])]) return 0;
    return 1;
}
static void write_clique(const char *path, const int *vs, int n) { /* lines: s b c f */
    FILE *f = fopen(path, "w");
    if (!f) return;
    for (int i = 0; i < n; i++) {
        int lo = vs[i] % H, hi = vs[i] / H;
        fprintf(f, "%d %d %d %d\n", lo % 11, lo / 11, hi % 11, hi / 11);
    }
    fclose(f);
}
static void write_offsets(const char *path, const int *vs, int n) { /* lines: a b c e f = 0 b c s f */
    FILE *f = fopen(path, "w");
    if (!f) return;
    for (int i = 0; i < n; i++) {
        int lo = vs[i] % H, hi = vs[i] / H;
        fprintf(f, "0 %d %d %d %d\n", lo / 11, hi % 11, lo % 11, hi / 11);
    }
    fclose(f);
}
static void save_found(const char *outdir) {
    char path[1024];
    if (!is_clique(K, kn) || recompute_cost() != 0) { fprintf(stderr, "BUG: saved set is not a clique\n"); exit(2); }
    snprintf(path, sizeof path, "%s/found_k%d.txt", outdir, kn);
    write_clique(path, K, kn);
    if (kn > bestK) {
        bestK = kn;
        memcpy(bestClique, K, sizeof(int) * kn);
        snprintf(path, sizeof path, "%s/best_offsets.txt", outdir);
        write_offsets(path, bestClique, bestK);
    }
    fprintf(stderr, "SAVED clique size %d\n", kn);
}

int main(int argc, char **argv) {
    if (argc < 6) {
        fprintf(stderr, "usage: fixk SEEDFILE|- KSTART CPU_SEC OUTDIR RNGSEED [MAXNOIMP] [TENB]\n");
        return 1;
    }
    const char *seedfile = argv[1];
    int k = atoi(argv[2]);
    double cpulim = atof(argv[3]);
    const char *outdir = argv[4];
    rs ^= (uint64_t)strtoull(argv[5], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    long maxnoimp = argc > 6 ? atol(argv[6]) : 100000;
    int tenB = argc > 7 ? atoi(argv[7]) : 7;
    init_tables();
    clear_state();

    int sv[MAXK], ns = 0;
    if (strcmp(seedfile, "-") != 0) {
        FILE *f = fopen(seedfile, "r");
        if (!f) { perror(seedfile); return 1; }
        char line[512];
        while (fgets(line, sizeof line, f)) {
            if (line[0] == '#') continue;
            long a[8]; int nn = 0; char *p = line, *end;
            for (;;) {
                long x = strtol(p, &end, 10);
                if (end == p) break;
                if (nn < 8) a[nn++] = x;
                p = end;
            }
            long s, b, c, fq;
            if (nn == 5) { s = ((2 * a[0] + a[3]) % 11 + 11) % 11; b = a[1]; c = a[2]; fq = a[4]; }
            else if (nn == 4) { s = a[0]; b = a[1]; c = a[2]; fq = a[3]; }
            else continue;
            s = (s % 11 + 11) % 11; b = (b % 11 + 11) % 11; c = (c % 11 + 11) % 11; fq = (fq % 11 + 11) % 11;
            if (ns < MAXK) sv[ns++] = (int)((s + 11 * b) + H * (c + 11 * fq));
        }
        fclose(f);
        if (ns > 0) {
            int t = sv[0], nd = 0;
            for (int i = 0; i < ns; i++) sv[i] = diffv(sv[i], t);   /* translate: vertex 0 is in the set */
            for (int i = 0; i < ns; i++) if (!mark[sv[i]]) { mark[sv[i]] = 1; sv[nd++] = sv[i]; }
            for (int i = 0; i < nd; i++) mark[sv[i]] = 0;
            ns = nd;
            set_state(sv, ns);
            fprintf(stderr, "seed: %d vertices, cost %d\n", ns, cost);
        }
    }
    if (ns == 0) { clear_state(); add_v(0); }
    if (k < kn) k = kn;
    while (kn < k) greedy_add();
    fprintf(stderr, "start: k=%d cost=%d\n", kn, cost);
    if (cost == 0) save_found(outdir);

    clock_t c0 = clock();
    int runBest = cost;
    eliteCost = cost; eliteN = kn; memcpy(eliteK, K, sizeof(int) * kn);
    long noimp = 0, restarts = 0, nsave = 0;
    long it;
    for (it = 1;; it++) {
        if ((it & 0xFFF) == 0) {
            double el = (double)(clock() - c0) / CLOCKS_PER_SEC;
            if (el > cpulim) break;
            if ((it & 0x3FFFF) == 0)
                fprintf(stderr, "it=%ld t=%.0fs k=%d cost=%d runBest=%d eliteCost=%d restarts=%ld\n",
                        it, el, kn, cost, runBest, eliteCost, restarts);
            if ((it & 0xFFFFF) == 0 && recompute_cost() != cost) { fprintf(stderr, "BUG: cost drift\n"); return 3; }
        }
        if (cost == 0) {
            save_found(outdir);
            nsave++;
            if (kn + 1 >= MAXK) break;
            greedy_add();
            k = kn;
            runBest = cost; eliteCost = cost; eliteN = kn; memcpy(eliteK, K, sizeof(int) * kn);
            noimp = 0;
            continue;
        }

        /* pass A: minimum m over outside vertices (overall and non-tabu) */
        int minAll = 255, minNT = 255;
        for (int v = 0; v < NV; v++)
            if (posK[v] < 0) {
                int mv = m[v];
                if (mv < minAll) minAll = mv;
                if (mv < minNT && tabuIn[v] < it) minNT = mv;
            }
        /* pass B: candidate entering vertices */
        int nL = 0;
        for (int v = 0; v < NV; v++)
            if (posK[v] < 0) {
                int mv = m[v];
                if (mv <= minAll + 1 || (mv <= minNT + 1 && tabuIn[v] < it)) bufL[nL++] = v;
            }
        /* leaving candidates: all of K except vertex 0 */
        int yv[MAXK], ny = 0;
        for (int i = 0; i < kn; i++) if (K[i] != 0) yv[ny++] = K[i];

        int bestD = 1 << 30, bx = -1, by = -1, nt = 0;
        for (int a = 0; a < nL; a++) {
            int x = bufL[a], mx = m[x];
            int xtabu = tabuIn[x] >= it;
            for (int j = 0; j < ny; j++) {
                int y = yv[j];
                int d = mx - m[y] - nonadj(x, y);
                if (xtabu || tabuOut[y] >= it)
                    if (!(cost + d < runBest)) continue;
                if (d < bestD) { bestD = d; bx = x; by = y; nt = 1; }
                else if (d == bestD) { nt++; if (rndn(nt) == 0) { bx = x; by = y; } }
            }
        }
        if (bx < 0) { bx = bufL[rndn(nL)]; by = yv[rndn(ny)]; }
        int oldc = cost;
        do_swap(by, bx);
        tabuIn[by] = it + tenB + rndn(8);
        tabuOut[bx] = it + 2 + rndn(3);
        (void)oldc;

        if (cost < runBest) { runBest = cost; noimp = 0; } else noimp++;
        if (cost < eliteCost) {
            eliteCost = cost; eliteN = kn; memcpy(eliteK, K, sizeof(int) * kn);
        }
        if (noimp > maxnoimp) {
            restarts++;
            if (rndn(2) == 0 && eliteN == kn) {
                set_state(eliteK, eliteN);
                int r = 2 + rndn(6);
                for (int t = 0; t < r; t++) {
                    int y;
                    do { y = K[rndn(kn)]; } while (y == 0);
                    int x;
                    do { x = rndn(NV); } while (posK[x] >= 0);
                    do_swap(y, x);
                }
            } else {
                clear_state();
                add_v(0);
                while (kn < k) greedy_add();
            }
            runBest = cost; noimp = 0;
        }
    }
    double el = (double)(clock() - c0) / CLOCKS_PER_SEC;
    fprintf(stderr, "END it=%ld t=%.1fs k=%d cost=%d eliteCost=%d restarts=%ld saved=%ld bestK=%d\n",
            it, el, kn, cost, eliteCost, restarts, nsave, bestK);
    {
        char path[1024];
        snprintf(path, sizeof path, "%s/elite_k%d.txt", outdir, eliteN);
        write_clique(path, eliteK, eliteN);
    }
    return 0;
}
