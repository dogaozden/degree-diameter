/* e15: Haar graph H(G,S), G = F_p^2 x|_M Z_k, M = companion matrix of (x-z)(x-z^J), z a primitive k-th root of 1 in F_p.
   Element (t,v), t in Z_k, v in F_p^2; (t1,v1)(t2,v2) = (t1+t2, v1 + M^t1 v2). N = 2|G| vertices (g,side).
   Edges (g,0) ~ (g s,1), s in S. Diameter via BFS from (e,0) and (e,1) (both sides vertex-transitive).
   Local search on S (|S| = DEG) minimising the number of vertices at distance > D.
   usage: zpk P K J DEG D seconds seed OUT */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

static long long P, K, JE, DEG, D, PP, NG;
static long long Mt[64][4];
static uint64_t rs;
static unsigned char *dist;
static long long *qu;
static long long St[16], Sa[16], Sb[16], Sit[16], Sia[16], Sib[16];
static long long evals = 0;

static uint64_t rnd(void) {
    uint64_t z = (rs += 0x9E3779B97F4A7C15ULL);
    z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ULL;
    z = (z ^ (z >> 27)) * 0x94D049BB133111EBULL;
    return z ^ (z >> 31);
}
static long long powmod(long long b, long long e, long long m) {
    long long r = 1; b %= m;
    while (e > 0) { if (e & 1) r = r * b % m; b = b * b % m; e >>= 1; }
    return r;
}
static int isprime(int q) { if (q < 2) return 0; for (int d = 2; d * d <= q; d++) if (q % d == 0) return 0; return 1; }

static inline long long rmul(long long g, long long st, long long sa, long long sb) {
    long long t1 = g / PP, r = g - t1 * PP, a1 = r / P, b1 = r - a1 * P;
    long long *m = Mt[t1];
    long long na = (a1 + m[0] * sa + m[1] * sb) % P;
    long long nb = (b1 + m[2] * sa + m[3] * sb) % P;
    long long nt = t1 + st; if (nt >= K) nt -= K;
    return nt * PP + na * P + nb;
}

static void set_inverses(void) {
    for (int i = 0; i < DEG; i++) {
        long long ti = (K - St[i]) % K;
        long long *m = Mt[(K - St[i]) % K];
        long long va = (m[0] * Sa[i] + m[1] * Sb[i]) % P, vb = (m[2] * Sa[i] + m[3] * Sb[i]) % P;
        Sit[i] = ti; Sia[i] = (P - va) % P; Sib[i] = (P - vb) % P;
    }
}

/* returns number of holes: vertices at distance > D from (e,0) plus from (e,1) */
static long long cost(void) {
    long long NV = 2 * NG, holes = 0;
    evals++;
    set_inverses();
    for (int src = 0; src < 2; src++) {
        memset(dist, 255, NV);
        long long head = 0, tail = 0, s0 = src;
        qu[tail++] = s0; dist[s0] = 0;
        while (head < tail) {
            long long v = qu[head++];
            int d = dist[v];
            if (d >= D) continue;
            long long g = v >> 1; int side = (int)(v & 1);
            for (int i = 0; i < DEG; i++) {
                long long w = side ? rmul(g, Sit[i], Sia[i], Sib[i]) : rmul(g, St[i], Sa[i], Sb[i]);
                long long nv = 2 * w + (1 - side);
                if (dist[nv] == 255) { dist[nv] = (unsigned char)(d + 1); qu[tail++] = nv; }
            }
        }
        holes += NV - tail;
    }
    return holes;
}

static void rand_elt(int i) {
    St[i] = rnd() % K; Sa[i] = rnd() % P; Sb[i] = rnd() % P;
}

int main(int argc, char **argv) {
    if (argc < 9) { fprintf(stderr, "usage: zpk P K J DEG D seconds seed OUT\n"); return 1; }
    P = atoll(argv[1]); K = atoll(argv[2]); JE = atoll(argv[3]); DEG = atoll(argv[4]); D = atoll(argv[5]);
    double secs = atof(argv[6]);
    rs = strtoull(argv[7], 0, 10) * 2654435761ULL + 977;
    const char *out = argv[8];
    PP = P * P; NG = K * PP;
    /* primitive K-th root of unity z */
    long long z = -1;
    for (long long h = 2; h < P && z < 0; h++) {
        long long c = powmod(h, (P - 1) / K, P);
        if (powmod(c, K, P) != 1) continue;
        int ok = 1;
        for (int q = 2; q <= K; q++) if (K % q == 0 && isprime(q) && powmod(c, K / q, P) == 1) ok = 0;
        if (ok) z = c;
    }
    if (z < 0 || (P - 1) % K) { fprintf(stderr, "K must divide P-1\n"); return 1; }
    long long al = z, be = powmod(z, JE, P);
    if (be == al) { fprintf(stderr, "J gives equal eigenvalues\n"); return 1; }
    long long M[4] = {0, (P - al * be % P) % P, 1, (al + be) % P};
    long long I[4] = {1, 0, 0, 1};
    memcpy(Mt[0], I, sizeof I);
    for (int t = 1; t < K; t++) {
        long long *A = Mt[t - 1];
        Mt[t][0] = (A[0] * M[0] + A[1] * M[2]) % P;
        Mt[t][1] = (A[0] * M[1] + A[1] * M[3]) % P;
        Mt[t][2] = (A[2] * M[0] + A[3] * M[2]) % P;
        Mt[t][3] = (A[2] * M[1] + A[3] * M[3]) % P;
    }
    /* check M^K = I */
    {
        long long *A = Mt[K - 1];
        long long c0 = (A[0] * M[0] + A[1] * M[2]) % P, c1 = (A[0] * M[1] + A[1] * M[3]) % P;
        long long c2 = (A[2] * M[0] + A[3] * M[2]) % P, c3 = (A[2] * M[1] + A[3] * M[3]) % P;
        if (c0 != 1 || c1 || c2 || c3 != 1) { fprintf(stderr, "M^K != I\n"); return 1; }
    }
    long long NV = 2 * NG;
    dist = malloc(NV);
    qu = malloc(sizeof(long long) * NV);
    if (!dist || !qu) { fprintf(stderr, "alloc\n"); return 1; }
    fprintf(stderr, "P=%lld K=%lld J=%lld z=%lld |G|=%lld N=%lld DEG=%lld D=%lld\n", P, K, JE, z, NG, NV, DEG, D);

    struct timespec t0, t1;
    clock_gettime(CLOCK_MONOTONIC, &t0);
    long long bestAll = -1; long long bS_t[16], bS_a[16], bS_b[16];
    int restarts = 0;
    const int CAND = 8, STALL = 40;
    while (1) {
        for (int i = 0; i < DEG; i++) rand_elt(i);
        long long cur = cost();
        int stall = 0;
        while (stall < STALL) {
            long long bc = -1; int bi = -1; long long bt = 0, ba = 0, bb = 0;
            for (int c = 0; c < CAND; c++) {
                int i = rnd() % DEG;
                long long ot = St[i], oa = Sa[i], ob = Sb[i];
                rand_elt(i);
                long long cc = cost();
                if (bc < 0 || cc < bc) { bc = cc; bi = i; bt = St[i]; ba = Sa[i]; bb = Sb[i]; }
                St[i] = ot; Sa[i] = oa; Sb[i] = ob;
            }
            if (bc <= cur) {
                if (bc < cur) stall = 0; else stall++;
                St[bi] = bt; Sa[bi] = ba; Sb[bi] = bb; cur = bc;
            } else stall++;
            if (bestAll < 0 || cur < bestAll) {
                bestAll = cur;
                for (int i = 0; i < DEG; i++) { bS_t[i] = St[i]; bS_a[i] = Sa[i]; bS_b[i] = Sb[i]; }
            }
            if (cur == 0) break;
            clock_gettime(CLOCK_MONOTONIC, &t1);
            if ((t1.tv_sec - t0.tv_sec) + 1e-9 * (t1.tv_nsec - t0.tv_nsec) > secs) break;
        }
        clock_gettime(CLOCK_MONOTONIC, &t1);
        double el = (t1.tv_sec - t0.tv_sec) + 1e-9 * (t1.tv_nsec - t0.tv_nsec);
        if (cur == 0 || el > secs) break;
        restarts++;
    }
    clock_gettime(CLOCK_MONOTONIC, &t1);
    double el = (t1.tv_sec - t0.tv_sec) + 1e-9 * (t1.tv_nsec - t0.tv_nsec);
    /* write best S */
    for (int i = 0; i < DEG; i++) { St[i] = bS_t[i]; Sa[i] = bS_a[i]; Sb[i] = bS_b[i]; }
    long long fc = cost();
    FILE *f = fopen(out, "w");
    fprintf(f, "%lld %lld %lld %lld %lld\n", P, K, JE, DEG, D);
    for (int i = 0; i < DEG; i++) fprintf(f, "%lld %lld %lld\n", St[i], Sa[i], Sb[i]);
    fclose(f);
    printf("RESULT P=%lld K=%lld J=%lld DEG=%lld D=%lld N=%lld best=%lld evals=%lld restarts=%d time=%.1f valid_candidate=%d sol=%s\n",
           P, K, JE, DEG, D, NV, fc, evals, restarts, el, fc == 0, out);
    return 0;
}
