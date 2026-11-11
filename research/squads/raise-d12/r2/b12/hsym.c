/* b12: Haar graphs H(G,S) with inverse-closed S (S = S^{-1}), G = Z_m x|_r Z_k (metacyclic).
   Bipartite double cover of Cay(G,S). Target: diameter <= 12 (even D: every B-element within 11 of (e,A)).
   usage: hsym m k r Delta Q secs seed [mode] [cmpfile]
     Q     = number of involutions in S (Delta - Q must be even; Q = -1: sample Q uniformly over valid values)
     Q = 9 with Delta = 4 means random S (no symmetry), Q = 10 means random S with Delta... (see mode)
     mode  = 0 (default): symmetric S sampling; 1: unrestricted random S (control)
   prints histogram of costs, fraction of cost 0, and pairing stats of uncovered B-elements under h -> h^{-1}.
   cost = number of B-elements h with dist((e,A),(h,B)) > 11 (BFS limited to depth 11).
   Writes SOL file (S as element indices, group given by m k r) when cost 0 found: first one only.
   THREADS=1; memory ~ 3 bytes per group element. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <stdint.h>
#include <math.h>

static long m, k, r, N;
static long *pw;       /* r^y mod m */
static int *invtab;    /* inverse of element */
static uint8_t *dist;  /* 2N */
static int *queue;     /* 2N */

static uint64_t rs;
static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }

static inline long mul(long a, long b) {
    long ax = a / k, ay = a % k, bx = b / k, by = b % k;
    long x = (ax + pw[ay] * bx) % m;
    long y = (ay + by) % k;
    return x * k + y;
}

static void build_inv(void) {
    /* (x,y)^{-1} = (-r^{-y} x, -y): x + r^y * (-r^{-y} x) = 0 */
    for (long a = 0; a < N; a++) {
        long x = a / k, y = a % k;
        long yi = (k - y) % k;
        long x2 = (m - (pw[yi] * x) % m) % m;
        invtab[a] = (int)(x2 * k + yi);
        if (mul(a, invtab[a]) != 0) { fprintf(stderr, "inverse check failed\n"); exit(1); }
    }
}

static int is_inv(long g) { return invtab[g] == g; }

/* returns cost; fills hole list if holes != NULL (count in *nh) */
static long cost_of(const int *S, int D, int *holes, long *nh) {
    int Sinv[16];
    for (int i = 0; i < D; i++) Sinv[i] = invtab[S[i]];
    memset(dist, 255, 2 * N);
    long qh = 0, qt = 0;
    dist[0] = 0; queue[qt++] = 0;               /* node 0 = (e,A) */
    while (qh < qt) {
        int u = queue[qh++];
        int du = dist[u];
        if (du >= 11) continue;                 /* expand up to depth 10: B-nodes at distance <= 11 */
        long g = u >> 1;
        if ((u & 1) == 0) {                     /* (g,A) -> (s g, B) */
            for (int i = 0; i < D; i++) {
                int v = 2 * mul(S[i], g) + 1;
                if (dist[v] == 255) { dist[v] = du + 1; queue[qt++] = v; }
            }
        } else {                                /* (h,B) -> (s^{-1} h, A) */
            for (int i = 0; i < D; i++) {
                int v = 2 * mul(Sinv[i], g);
                if (dist[v] == 255) { dist[v] = du + 1; queue[qt++] = v; }
            }
        }
    }
    long c = 0, hc = 0;
    for (long h = 0; h < N; h++) {
        int d = dist[2 * h + 1];
        if (d == 255 || d > 11) { c++; if (holes && hc < 1000000) holes[hc++] = (int)h; }
    }
    if (nh) *nh = hc;
    return c;
}

int main(int argc, char **argv) {
    if (argc < 8) { fprintf(stderr, "usage: hsym m k r Delta Q secs seed [mode]\n"); return 1; }
    m = atol(argv[1]); k = atol(argv[2]); r = atol(argv[3]);
    int D = atoi(argv[4]);
    int Q = atoi(argv[5]);
    double secs = atof(argv[6]);
    rs = (uint64_t)atoll(argv[7]) * 2654435761ULL + 88172645463325252ULL;
    int mode = argc > 8 ? atoi(argv[8]) : 0;
    N = m * k;
    pw = malloc(sizeof(long) * k);
    pw[0] = 1 % m;
    for (long y = 1; y < k; y++) pw[y] = (pw[y - 1] * r) % m;
    if ((pw[0] * 1) % m != 1 % m || (pw[k - 1] * r) % m != 1 % m) { fprintf(stderr, "r^k != 1 mod m\n"); return 1; }
    invtab = malloc(sizeof(int) * N);
    dist = malloc(2 * N);
    queue = malloc(sizeof(int) * 2 * N);
    build_inv();
    /* involutions (g != e with g^2 = e) and non-involutions */
    int *invol = malloc(sizeof(int) * N); long ni = 0;
    for (long g = 1; g < N; g++) if (invtab[g] == g) invol[ni++] = (int)g;
    fprintf(stderr, "group Z%ld x|_%ld Z%ld N=%ld involutions=%ld\n", m, r, k, N, ni);

    time_t t0 = time(NULL);
    long samples = 0, zero = 0, bestc = 1L << 40; double sumc = 0, sumlog = 0; long lowc[8]; for (int i = 0; i < 8; i++) lowc[i] = 1L << 40;
    long hist[64]; memset(hist, 0, sizeof hist);
    long pair_hits = 0, hole_total = 0, paired_total = 0, fixed_total = 0, samp_holes = 0;
    int *holes = malloc(sizeof(int) * N);
    int S[16];
    long nh = 0;
    int Qs[16], nq = 0;
    if (mode == 0) {
        /* symmetric S: Q involutions and (D-Q)/2 inverse pairs */
        if (Q < 0) { for (int q = D % 2; q <= D; q += 2) Qs[nq++] = q; }
        else Qs[nq++] = Q;
    }
    if (getenv("SFORCE")) {
        /* debug: evaluate one given S (indices), print cost, exit */
        char *p = getenv("SFORCE"); int i = 0;
        while (i < D && *p) { S[i++] = (int)strtol(p, &p, 10); }
        long c = cost_of(S, D, NULL, NULL);
        printf("forced cost %ld\n", c);
        return 0;
    }
    /* mode 2: symmetric annealing (Q = 0 only): replace one inverse pair per move, SA acceptance */
    if (mode == 2) {
        int cur[16]; long curc = 1L << 40; double T = 3.0; long steps = 0, acc = 0;
        for (int i = 0; i < D; i += 2) {
            for (;;) {
                long a = 1 + (long)(rnd() % (uint64_t)(N - 1));
                if (invtab[a] == a) continue;
                cur[i] = (int)a; cur[i + 1] = invtab[a]; break;
            }
        }
        curc = cost_of(cur, D, NULL, NULL);
        long bestseen = curc;
        while (difftime(time(NULL), t0) < secs) {
            int cand[16];
            memcpy(cand, cur, sizeof cand);
            int pi = (int)(rnd() % (uint64_t)(D / 2)) * 2;
            long a;
            for (;;) {
                a = 1 + (long)(rnd() % (uint64_t)(N - 1));
                if (invtab[a] == a) continue;
                int dup = 0;
                for (int j = 0; j < D; j++) if (j != pi && j != pi + 1 && (cand[j] == a || cand[j] == invtab[a])) dup = 1;
                if (!dup) break;
            }
            cand[pi] = (int)a; cand[pi + 1] = invtab[a];
            long c = cost_of(cand, D, NULL, NULL);
            steps++;
            double dlt = (double)c - (double)curc;
            if (dlt <= 0 || (double)(rnd() % 1000000) / 1e6 < exp(-dlt / T)) {
                memcpy(cur, cand, sizeof cur); curc = c; acc++;
                if (c < bestseen) bestseen = c;
                if (c == 0) {
                    char fn[256]; sprintf(fn, "sol_sym_m%ld_k%ld_r%ld.txt", m, k, r);
                    FILE *f = fopen(fn, "w");
                    if (f) { fprintf(f, "%ld %ld %ld %d\n", m, k, r, D); for (int i = 0; i < D; i++) fprintf(f, "%d\n", cur[i]); fclose(f); }
                    printf("FOUND cost 0 at step %ld -> %s\n", steps, fn);
                    return 0;
                }
            }
            T *= 0.9995; if (T < 0.3) T = 0.3;
        }
        printf("annealing steps %ld accepted %ld final T %.2f cur cost %ld best seen %ld\n", steps, acc, T, curc, bestseen);
        {   /* where do the holes sit? histogram of hole y-coordinates (abelian image in Z_k) and x-parity */
            long hn = 0; cost_of(cur, D, holes, &hn);
            long hy[64]; memset(hy, 0, sizeof hy);
            for (long i = 0; i < hn; i++) hy[holes[i] % k]++;
            printf("state S:"); for (int i = 0; i < D; i++) printf(" %d(x%ld,y%d)", cur[i], cur[i] / k, cur[i] % k); printf("\n");
            printf("holes %ld, y-histogram (k=%ld):", hn, k); for (long y = 0; y < k; y++) printf(" %ld", hy[y]); printf("\n");
        }
        return 0;
    }
    while (difftime(time(NULL), t0) < secs) {
        int ok = 1;
        int nS = 0;
        if (mode == 1) {
            /* unrestricted random S: D distinct non-identity elements */
            while (nS < D) {
                long g = 1 + (long)(rnd() % (uint64_t)(N - 1));
                int dup = 0;
                for (int i = 0; i < nS; i++) if (S[i] == g) dup = 1;
                if (!dup) S[nS++] = (int)g;
            }
        } else {
            int q = Qs[rnd() % nq];
            int p = (D - q) / 2;
            if (q > ni) continue;
            /* involutions */
            while (q > 0) {
                int g = invol[rnd() % ni];
                int dup = 0;
                for (int i = 0; i < nS; i++) if (S[i] == g) dup = 1;
                if (!dup) { S[nS++] = g; q--; }
            }
            /* inverse pairs {a, a^-1} with a non-involution */
            while (p > 0) {
                long a = 1 + (long)(rnd() % (uint64_t)(N - 1));
                if (invtab[a] == a) continue;
                long b = invtab[a];
                int dup = 0;
                for (int i = 0; i < nS; i++) if (S[i] == a || S[i] == b) dup = 1;
                if (!dup) { S[nS++] = (int)a; S[nS++] = (int)b; p--; }
            }
        }
        (void)ok;
        samples++;
        long c = cost_of(S, D, holes, &nh);
        if (c < 64) hist[c]++; else hist[63]++;
        if (c < bestc) bestc = c;
        sumc += (double)c;
        { int ins = -1; for (int i = 0; i < 8; i++) if (c < lowc[i]) { ins = i; break; }
          if (ins >= 0) { for (int i = 7; i > ins; i--) lowc[i] = lowc[i-1]; lowc[ins] = c; } }
        if (c == 0) {
            zero++;
            if (zero == 1) {
                char fn[256]; sprintf(fn, "sol_m%ld_k%ld_r%ld_D%d_Q%d.txt", m, k, r, D, Q);
                FILE *f = fopen(fn, "w");
                if (f) { fprintf(f, "%ld %ld %ld %d\n", m, k, r, D); for (int i = 0; i < D; i++) fprintf(f, "%d\n", S[i]); fclose(f); }
                fprintf(stderr, "FOUND cost 0 at sample %ld, wrote %s\n", samples, fn);
            }
        } else {
            /* pairing statistics: holes h with h^{-1} also a hole */
            static char *isH = NULL;
            if (!isH) isH = calloc(N, 1);
            for (long i = 0; i < nh; i++) isH[holes[i]] = 1;
            long pr = 0, fx = 0;
            for (long i = 0; i < nh; i++) {
                long h = holes[i];
                long hi = invtab[h];
                if (hi == h) fx++;
                else if (isH[hi]) pr++;
            }
            for (long i = 0; i < nh; i++) isH[holes[i]] = 0;
            pair_hits += pr; paired_total += nh - fx - pr; fixed_total += fx; hole_total += nh; samp_holes++;
        }
    }
    double el = difftime(time(NULL), t0);
    printf("samples %ld in %.0fs (%.2f ms each), zero-cost %ld, best cost %ld\n", samples, el, samples ? 1000.0 * el / samples : 0.0, zero, bestc);
    printf("mean cost %.1f, 8 lowest costs:", samples ? sumc / samples : 0.0); for (int i = 0; i < 8; i++) printf(" %ld", lowc[i] < (1L<<40) ? lowc[i] : -1); printf("\n");
    printf("cost histogram (0..15):");
    for (int c = 0; c < 16; c++) printf(" %ld", hist[c]);
    printf("\n");
    if (hole_total)
        printf("pairing: holes %ld over %ld costly samples; paired with inverse %.3f, self-inverse %.4f, unpaired %.3f\n",
               hole_total, samp_holes, (double)pair_hits / hole_total, (double)fixed_total / hole_total,
               (double)paired_total / hole_total);
    return 0;
}
