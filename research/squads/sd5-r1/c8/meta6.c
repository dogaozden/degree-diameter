/* meta6.c: bipartite Cayley graphs Cay(H,T) on metacyclic groups H = <x,y | x^M = y^K = 1, y x y^-1 = x^R>, |H| = N = M*K.
 * Edges x ~ t*x for t in T, T = T^-1, |T| = 6, T inside the odd coset of an index-2 subgroup (chi = j mod 2 when
 * MODE 0 and K even; chi = i mod 2 when MODE 1 and M even and R odd). The graph is bipartite, 6-regular, and
 * vertex-transitive under right multiplication, so diameter = ecc(e) = max distance from the identity (BFS).
 * Search: tabu search over the orbits {t, t^-1} (and involutions) with cost = N - |ball of radius 5 around e|.
 * Element (i,j) = x^i y^j has index i*K + j, identity 0; product (i,j)(p,q) = (i + R^j p mod M, j + q mod K).
 *
 * usage: meta6 one M K R MODE SECS SEED OUT      tabu on one group; writes edge list OUT on success
 *        meta6 sweep N SECS SEED                 all metacyclic groups of order N (both modes, all R), one line each
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

static int M, K, R, N, MODE;
static int *rp, *inv, *invol, *pairr, ninv, npair;
static uint16_t *MT;
static int *stamp, *dist, *queue, curstamp;
static int T[6];
static uint64_t rng = 88172645463325252ULL;

static inline uint64_t rnd(void) { rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17; return rng; }
static inline int rndint(int n) { return (int)(rnd() % (uint64_t)n); }

static int mul_slow(int x, int y) {
    int xi = x / K, xj = x % K, yi = y / K, yj = y % K;
    int zi = (int)((xi + (long)rp[xj] * yi) % M);
    return zi * K + (xj + yj) % K;
}
static int par(int x) { return MODE == 0 ? ((x % K) & 1) : ((x / K) & 1); }

static int ball(void) { /* number of vertices at distance <= 5 from e, with T[] */
    int head = 0, tail = 0;
    curstamp++;
    queue[tail++] = 0; stamp[0] = curstamp; dist[0] = 0;
    while (head < tail) {
        int x = queue[head++];
        if (dist[x] == 5) continue;
        for (int s = 0; s < 6; s++) {
            int y = MT[(size_t)T[s] * N + x];
            if (stamp[y] != curstamp) { stamp[y] = curstamp; dist[y] = dist[x] + 1; queue[tail++] = y; }
        }
    }
    return tail;
}

/* state: kind[s] 0 = involution (index into invol), 1 = pair (index into pairr) */
static int kind[6], cur[6], nslots;
static void build(void) {
    int t = 0;
    for (int s = 0; s < nslots; s++) {
        if (kind[s] == 0) T[t++] = invol[cur[s]];
        else { T[t++] = pairr[cur[s]]; T[t++] = inv[pairr[cur[s]]]; }
    }
}
static int in_state(int k, int idx, int skip) {
    for (int s = 0; s < nslots; s++) if (s != skip && kind[s] == k && cur[s] == idx) return 1;
    return 0;
}

static int *tabu_inv, *tabu_pair;
#define SAMPLE 60
#define TENURE 7

/* returns 1 if a valid T found; best cost in *bestc */
static int tabu_run(double secs, long *iters_out, int *bestc_out, int stall_limit) {
    clock_t c0 = clock();
    int bestc = N + 1, found = 0;
    long it = 0;
    int nrest = 0;
    memset(tabu_inv, 0, sizeof(int) * (ninv + 1));
    memset(tabu_pair, 0, sizeof(int) * (npair + 1));
    while (!found) {
        /* random restart: f involutions (even, <= ninv), p = (6-f)/2 pairs */
        int fopts[4], nf = 0;
        for (int f = 0; f <= 6; f += 2) if (f <= ninv && (6 - f) / 2 <= npair) fopts[nf++] = f;
        if (nf == 0) break;
        int f = fopts[rndint(nf)];
        nslots = f + (6 - f) / 2;
        for (int s = 0; s < nslots; s++) {
            if (s < f) { kind[s] = 0; cur[s] = rndint(ninv); }
            else { kind[s] = 1; cur[s] = rndint(npair); }
        }
        /* ensure distinct */
        int ok = 1;
        for (int s = 0; s < nslots && ok; s++) if (in_state(kind[s], cur[s], s)) ok = 0;
        if (!ok) continue;
        build();
        int cost = N - ball();
        int runbest = cost, stall = 0;
        nrest++;
        while (1) {
            it++;
            if ((it & 255) == 0 && (double)(clock() - c0) / CLOCKS_PER_SEC > secs) goto done;
            int bc = 1 << 30, bs = -1, bidx = -1;
            for (int s = 0; s < nslots; s++) {
                int nl = kind[s] == 0 ? ninv : npair;
                int *tabu = kind[s] == 0 ? tabu_inv : tabu_pair;
                int old = cur[s];
                int trials = nl < SAMPLE ? nl : SAMPLE;
                for (int q = 0; q < trials; q++) {
                    int cand = nl <= SAMPLE ? q : rndint(nl);
                    if (cand == old || in_state(kind[s], cand, s)) continue;
                    cur[s] = cand; build();
                    int c = N - ball();
                    cur[s] = old;
                    if (tabu[cand] > it && c >= bestc) continue; /* tabu unless new global best */
                    if (c < bc || (c == bc && rndint(2))) { bc = c; bs = s; bidx = cand; }
                }
            }
            if (bs < 0) break;
            int *tabu = kind[bs] == 0 ? tabu_inv : tabu_pair;
            tabu[cur[bs]] = it + TENURE + rndint(4);
            cur[bs] = bidx;
            build();
            cost = bc;
            if (cost < runbest) { runbest = cost; stall = 0; } else stall++;
            if (cost < bestc) bestc = cost;
            if (cost == 0) { found = 1; break; }
            if (stall > stall_limit) break;
        }
    }
done:
    if (found) build();
    *iters_out = it; *bestc_out = bestc;
    (void)nrest;
    return found;
}

static int setup(int m, int k, int r, int mode) {
    M = m; K = k; R = r; MODE = mode; N = M * K;
    rp = malloc(sizeof(int) * K);
    rp[0] = 1 % M;
    for (int j = 1; j < K; j++) rp[j] = (rp[j - 1] * R) % M;
    MT = malloc(sizeof(uint16_t) * (size_t)N * N);
    for (int x = 0; x < N; x++) for (int y = 0; y < N; y++) MT[(size_t)x * N + y] = (uint16_t)mul_slow(x, y);
    /* table is row-major by left factor: MT[t*N + x] = t*x */
    inv = malloc(sizeof(int) * N);
    for (int x = 0; x < N; x++) {
        inv[x] = -1;
        for (int y = 0; y < N; y++) if (mul_slow(x, y) == 0) { inv[x] = y; break; }
        if (inv[x] < 0) { fprintf(stderr, "no inverse\n"); exit(1); }
    }
    invol = malloc(sizeof(int) * N); pairr = malloc(sizeof(int) * N);
    ninv = 0; npair = 0;
    for (int x = 0; x < N; x++) {
        if (!par(x)) continue;
        if (inv[x] == x) invol[ninv++] = x;
        else if (x < inv[x]) pairr[npair++] = x;
    }
    stamp = calloc(N, sizeof(int)); dist = malloc(sizeof(int) * N); queue = malloc(sizeof(int) * N);
    tabu_inv = calloc(ninv + 1, sizeof(int)); tabu_pair = calloc(npair + 1, sizeof(int));
    return 0;
}

static void teardown(void) {
    free(rp); free(MT); free(inv); free(invol); free(pairr); free(stamp); free(dist); free(queue);
    free(tabu_inv); free(tabu_pair);
}

static int write_edges(const char *path) {
    FILE *f = fopen(path, "w");
    if (!f) return 1;
    fprintf(f, "%d\n", N);
    for (int x = 0; x < N; x++)
        for (int s = 0; s < 6; s++) {
            int y = MT[(size_t)T[s] * N + x];
            if (x < y) fprintf(f, "%d %d\n", x, y);
        }
    fclose(f);
    return 0;
}

int main(int argc, char **argv) {
    if (argc < 2) { fprintf(stderr, "usage: see header\n"); return 1; }
    if (!strcmp(argv[1], "one")) {
        if (argc < 9) return 1;
        int m = atoi(argv[2]), k = atoi(argv[3]), r = atoi(argv[4]), mode = atoi(argv[5]);
        double secs = atof(argv[6]);
        rng ^= (uint64_t)atoll(argv[7]) * 0x9E3779B97F4A7C15ULL;
        setup(m, k, r, mode);
        long its; int bc;
        int found = tabu_run(secs, &its, &bc, 4000);
        printf("M=%d K=%d R=%d MODE=%d N=%d found=%d bestcost=%d iters=%ld ninv=%d npair=%d\n", M, K, R, mode, N, found, bc, its, ninv, npair);
        if (found) {
            printf("T:");
            for (int s = 0; s < 6; s++) printf(" (%d,%d)", T[s] / K, T[s] % K);
            printf("\n");
            write_edges(argv[8]);
        }
        teardown();
        return found ? 0 : 2;
    }
    if (!strcmp(argv[1], "sweep")) {
        int n = atoi(argv[2]); double secs = atof(argv[3]);
        rng ^= (uint64_t)atoll(argv[4]) * 0x9E3779B97F4A7C15ULL;
        int nvalid = 0, ngroups = 0;
        for (int mode = 0; mode < 2; mode++)
        for (int k = 1; k <= n; k++) {
            if (n % k) continue;
            int m = n / k;
            if (mode == 0 && (k % 2 || m < 2)) continue;
            if (mode == 1 && (m % 2 || k < 2)) continue;
            for (int r = 1; r < m || (m == 1 && r == 1); r++) {
                if (m == 1 && r != 1) break;
                int g = 1, a = r, b = m; while (b) { int t = a % b; a = b; b = t; g = a; } /* gcd */
                if (m > 1 && g != 1) continue;
                /* r^k == 1 mod m */
                long p = 1 % m; for (int j = 0; j < k; j++) p = (p * r) % m;
                if (m > 1 && p != 1) continue;
                if (mode == 1 && (r % 2 == 0)) continue;
                setup(m, k, r, mode);
                long its; int bc;
                int found = (ninv >= 0 && npair >= 0) ? tabu_run(secs, &its, &bc, 1500) : 0;
                ngroups++;
                if (found) {
                    nvalid++;
                    char fn[256]; sprintf(fn, "valid_N%d_M%d_K%d_R%d_MODE%d.txt", n, m, k, r, mode);
                    write_edges(fn);
                }
                printf("N=%d M=%d K=%d R=%d MODE=%d found=%d bestcost=%d iters=%ld\n", n, m, k, r, mode, found, bc, its);
                fflush(stdout);
                teardown();
                if (m == 1) break;
            }
        }
        printf("SUMMARY N=%d groups=%d valid=%d\n", n, ngroups, nvalid);
        return 0;
    }
    return 1;
}
