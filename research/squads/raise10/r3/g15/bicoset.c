/* bicoset m k r d Delta D seconds seed OUTPREFIX [L]
   Bipartite COSET graphs (not Haar graphs) on G = Z_m x|_r Z_k, elements (a,b),
   (a1,b1)(a2,b2) = (a1 + r^{b1} a2 mod m, b1 + b2 mod k), r^k = 1 mod m.
   H = {(0, j d) : j} of order h = k/d, NON-normal iff r^d != 1 mod m (else the graph is a Haar quotient).
   Vertices: A = G/H and B = G/H (left cosets), 2M with M = N/h.
   xH ~ yH iff x^{-1} y in T, T = union of double cosets H t H with |T| = Delta*h (so HTH = T, well defined).
   Each side is a single G-orbit, so vertex-transitive per side: diameter <= D  iff  BFS from A-rep and B-rep
   reach everything within D. cost = far(A-rep) + far(B-rep).
   Simulated annealing over unions of double cosets (same-size swaps). On cost 0 writes OUTPREFIX.edges and OUTPREFIX.T.
   Compile: gcc -O2 -o bicoset bicoset.c -lm */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

static uint64_t rs = 88172645463325252ULL;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }

static int m, k, r, d, h, Dl, D;
static long N, M;
static long long *pw, *ipw;
static int *cid, *crep, *dcid, *dcsz, *dcoff, *dcel, ndc;
static int *mark, markc = 0;
static int *adj, *dcnt, *dist, *queue, *stamp2;
static int gs = 0;
static int *tl, Th;
static int *chosen, *clist, nch;

static inline int mul(int g1, int g2) {
    int a1 = g1 / k, b1 = g1 - a1 * k, a2 = g2 / k, b2 = g2 - a2 * k;
    long long a = (a1 + pw[b1] * (long long)a2) % m;
    int b = b1 + b2; if (b >= k) b -= k;
    return (int)a * k + b;
}
static inline int hel(int j) { return j * d; } /* element (0, j d) */

static long long modinv(long long a, long long mod) {
    long long t = 0, nt = 1, rr = mod, nr = a % mod;
    while (nr) { long long q = rr / nr, tmp; tmp = t - q * nt; t = nt; nt = tmp; tmp = rr - q * nr; rr = nr; nr = tmp; }
    if (t < 0) t += mod; return t;
}

/* build T from chosen double cosets, graph, and return cost */
static long eval_cost(void) {
    int cnt = 0;
    for (int c = 0; c < nch; c++) { int q = clist[c]; for (int e = 0; e < dcsz[q]; e++) tl[cnt++] = dcel[dcoff[q] + e]; }
    if (cnt != Th) { fprintf(stderr, "bad T size %d vs %d\n", cnt, Th); exit(4); }
    for (long i = 0; i < M; i++) {
        int x = crep[i]; gs++; int c2 = 0;
        for (int t = 0; t < cnt; t++) {
            int j = cid[mul(x, tl[t])];
            if (stamp2[j] != gs) { stamp2[j] = gs; if (c2 >= Dl) { fprintf(stderr, "degree error\n"); exit(5); } adj[i * Dl + c2] = (int)(M + j); c2++; }
        }
        if (c2 != Dl) { fprintf(stderr, "degree %d != %d\n", c2, Dl); exit(6); }
    }
    for (long j = 0; j < M; j++) dcnt[j] = 0;
    for (long i = 0; i < M; i++) for (int s = 0; s < Dl; s++) {
        long j = adj[i * Dl + s] - M;
        if (dcnt[j] >= Dl) { fprintf(stderr, "B degree error\n"); exit(7); }
        adj[(M + j) * Dl + dcnt[j]++] = (int)i;
    }
    long cost = 0;
    for (int src = 0; src < 2; src++) {
        long s0 = src == 0 ? 0 : M;
        for (long v = 0; v < 2 * M; v++) dist[v] = -1;
        long head = 0, tail = 0; queue[tail++] = (int)s0; dist[s0] = 0; long within = 1;
        while (head < tail) {
            int u = queue[head++];
            if (dist[u] >= D) continue;
            for (int s = 0; s < Dl; s++) { int w = adj[(long)u * Dl + s]; if (dist[w] < 0) { dist[w] = dist[u] + 1; queue[tail++] = w; within++; } }
        }
        cost += 2 * M - within; /* vertices at distance > D or unreached */
    }
    return cost;
}

static int init_random(void) {
    int *perm = malloc(sizeof(int) * ndc);
    for (int att = 0; ; att++) {
        if (att > 20000) { free(perm); return 0; }
        for (int q = 0; q < ndc; q++) perm[q] = q;
        for (int q = ndc - 1; q > 0; q--) { int j = (int)(rnd() % (q + 1)); int t = perm[q]; perm[q] = perm[j]; perm[j] = t; }
        for (int q = 0; q < ndc; q++) chosen[q] = 0;
        nch = 0; int sum = 0;
        for (int p = 0; p < ndc && sum < Th; p++) { int q = perm[p]; if (sum + dcsz[q] <= Th) { chosen[q] = 1; clist[nch++] = q; sum += dcsz[q]; } }
        if (sum == Th) break;
    }
    free(perm);
    return 1;
}

static void write_result(const char *prefix) {
    char fn[512];
    snprintf(fn, sizeof fn, "%s.edges", prefix);
    FILE *f = fopen(fn, "w");
    fprintf(f, "%ld\n", 2 * M);
    for (long i = 0; i < M; i++) for (int s = 0; s < Dl; s++) fprintf(f, "%ld %d\n", i, adj[i * Dl + s]);
    fclose(f);
    snprintf(fn, sizeof fn, "%s.T", prefix);
    f = fopen(fn, "w");
    fprintf(f, "m %d k %d r %d d %d Delta %d D %d N %ld M %ld\n", m, k, r, d, Dl, D, N, M);
    for (int c = 0; c < nch; c++) { int q = clist[c]; for (int e = 0; e < dcsz[q]; e++) { int g = dcel[dcoff[q] + e]; fprintf(f, "%d %d\n", g / k, g % k); } }
    fclose(f);
}

int main(int argc, char **argv) {
    if (argc < 10) { fprintf(stderr, "usage: bicoset m k r d Delta D seconds seed OUTPREFIX [L]\n"); return 1; }
    m = atoi(argv[1]); k = atoi(argv[2]); r = atoi(argv[3]); d = atoi(argv[4]);
    Dl = atoi(argv[5]); D = atoi(argv[6]);
    double secs = atof(argv[7]); rs = strtoull(argv[8], 0, 10) * 2654435761ULL + 88172645463325252ULL;
    const char *outp = argv[9]; long L = argc > 10 ? atol(argv[10]) : 3000;
    if (k % d != 0) { fprintf(stderr, "d must divide k\n"); return 1; }
    h = k / d; N = (long)m * k; M = N / h;
    pw = malloc(sizeof(long long) * (k + 1)); ipw = malloc(sizeof(long long) * (k + 1));
    pw[0] = 1 % m; for (int b = 1; b < k; b++) pw[b] = pw[b - 1] * r % m;
    if ((pw[k - 1] * r) % m != 1 % m) { fprintf(stderr, "r^k != 1 mod m\n"); return 2; }
    if (pw[d] == 1 % m) { printf("NORMAL H (Haar quotient), skip\n"); return 3; }
    long long rinv = modinv(r, m); ipw[0] = 1 % m; for (int b = 1; b < k; b++) ipw[b] = ipw[b - 1] * rinv % m;
    Th = Dl * h;
    cid = malloc(sizeof(int) * N); crep = malloc(sizeof(int) * M); mark = calloc(N, sizeof(int));
    for (long g = 0; g < N; g++) cid[g] = -1;
    int c = 0;
    for (long g = 0; g < N; g++) if (cid[g] < 0) {
        for (int j = 0; j < h; j++) cid[mul((int)g, hel(j))] = c;
        crep[c] = (int)g; c++;
    }
    if (c != M) { fprintf(stderr, "coset count %d != %ld\n", c, M); return 2; }
    dcid = malloc(sizeof(int) * N); for (long g = 0; g < N; g++) dcid[g] = -1;
    dcsz = malloc(sizeof(int) * N); dcoff = malloc(sizeof(int) * N); dcel = malloc(sizeof(int) * N);
    ndc = 0; long pos = 0;
    for (long g = 0; g < N; g++) if (dcid[g] < 0) {
        markc++; int cnt = 0; int start = (int)pos;
        for (int i = 0; i < h; i++) { int x0 = mul(hel(i), (int)g);
            for (int j = 0; j < h; j++) { int x = mul(x0, hel(j));
                if (mark[x] != markc) { mark[x] = markc; dcel[pos++] = x; cnt++; } } }
        for (int e = start; e < pos; e++) dcid[dcel[e]] = ndc;
        dcoff[ndc] = start; dcsz[ndc] = cnt; ndc++;
    }
    chosen = calloc(ndc, sizeof(int)); clist = malloc(sizeof(int) * ndc);
    tl = malloc(sizeof(int) * (Th + 1));
    adj = malloc(sizeof(int) * 2 * M * Dl); dcnt = malloc(sizeof(int) * M);
    dist = malloc(sizeof(int) * 2 * M); queue = malloc(sizeof(int) * 2 * M); stamp2 = calloc(M, sizeof(int));
    int nsz = 0; for (int q = 0; q < ndc; q++) if (dcsz[q] <= Th) nsz++;
    printf("G order %ld, H order %d, cosets M=%ld (vertices %ld), double cosets %d, target |T|=%d\n", N, h, M, 2 * M, ndc, Th);
    if (nsz == 0) { printf("no usable double cosets\n"); return 0; }
    double t0 = now(); double bestc = 1e18; long steps = 0; int restarts = 0;
    int *bestclist = malloc(sizeof(int) * ndc); int bestn = 0;
    double T0 = 2.0, T1 = 0.1;
    while (now() - t0 < secs) {
        if (!init_random()) { printf("no exact-size composition found (Delta*h=%d)\n", Th); break; }
        restarts++;
        long cur = eval_cost();
        for (long st = 0; st < L && now() - t0 < secs; st++) {
            steps++;
            double temp = T0 * pow(T1 / T0, (double)st / L);
            int ci = (int)(rnd() % nch); int q = clist[ci]; int s = dcsz[q];
            int q2 = -1;
            for (int tries = 0; tries < 200; tries++) { int cand = (int)(rnd() % ndc); if (!chosen[cand] && dcsz[cand] == s) { q2 = cand; break; } }
            if (q2 < 0) continue;
            chosen[q] = 0; chosen[q2] = 1; clist[ci] = q2;
            long nc = eval_cost();
            if (nc <= cur || rnd01() < exp(-(double)(nc - cur) / temp)) {
                cur = nc;
                if (cur < bestc) { bestc = cur; bestn = nch; memcpy(bestclist, clist, sizeof(int) * nch);
                    printf("  restart %d step %ld best cost %.0f\n", restarts, steps, bestc); fflush(stdout); }
                if (cur == 0) break;
            } else { chosen[q2] = 0; chosen[q] = 1; clist[ci] = q; }
        }
        if (bestc == 0) break;
    }
    printf("RESULT vertices %ld best_cost %.0f restarts %d steps %ld secs %.1f\n", 2 * M, bestc, restarts, steps, now() - t0);
    if (bestc == 0) {
        /* rebuild best state and write */
        for (int q = 0; q < ndc; q++) chosen[q] = 0;
        nch = bestn; memcpy(clist, bestclist, sizeof(int) * nch); for (int c2 = 0; c2 < nch; c2++) chosen[clist[c2]] = 1;
        long cc = eval_cost();
        printf("rebuilt cost %ld\n", cc);
        write_result(outp);
        printf("WROTE %s.edges %s.T\n", outp, outp);
    }
    return 0;
}
