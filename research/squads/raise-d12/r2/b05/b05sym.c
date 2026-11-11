/* b05sym: Haar graph H(G,S), G = D7^5 (order 537,824), 5-element S.
 * Vertices (g,A) = id g, (g,B) = id NG+g. Edges (g,A)~(s g,B) for s in S.
 * Diameter <= 12 iff ecc((e,A)) <= 12 and ecc((e,B)) <= 12 (right mult. is transitive on each side).
 * cost = number of vertices not within 12 of (e,A) + number not within 12 of (e,B).
 *
 * MODE=orbit : S = orbit {x, ax, ..., a^4 x} of alpha(h1..h5) = (h5,h1,h2,h3,h4)
 * MODE=rand  : S = 5 random distinct elements (no symmetry)
 * MODE=anneal: simulated annealing over orbit representatives x (orbit mode only)
 * usage: b05sym MODE SECS SEED OUT [INIT_X]
 *   env TEMP (anneal, default 2.0)
 * OUT.state holds best x (anneal/orbit), OUT.sol is written only on cost 0.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define K 5
#define HN 14
#define NG 537824u
#define DMAX 12

static int hm[HN][HN], hinv[HN];
static uint32_t pk[NG];        /* packed 4-bit digits */
static uint32_t alp[NG];       /* alpha map */
static uint32_t P[2 * K][K][16]; /* P[t][i][d]: t<5 left mult by s_t, t>=5 by s_{t-5}^{-1} */
static uint32_t S[K];
static uint8_t dist[2 * NG];
static uint32_t Q[2 * NG];
static uint64_t rs = 88172645463325252ull;

static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }

static void init_H(void) {
    for (int x = 0; x < HN; x++)
        for (int y = 0; y < HN; y++) {
            int a1 = x % 7, b1 = x / 7, a2 = y % 7, b2 = y / 7;
            int a = (a1 + (b1 ? (7 - a2) : a2)) % 7; /* (r^a1 s^b1)(r^a2 s^b2) = r^(a1 + (-1)^b1 a2) s^(b1+b2) */
            hm[x][y] = a + 7 * (b1 ^ b2);
        }
    for (int x = 0; x < HN; x++)
        for (int y = 0; y < HN; y++)
            if (hm[x][y] == 0) hinv[x] = y;
}

static void init_tables(void) {
    uint32_t w[K] = {1, 14, 196, 2744, 38416};
    for (uint32_t g = 0; g < NG; g++) {
        uint32_t d[K], p = 0, a = 0;
        uint32_t t = g;
        for (int i = 0; i < K; i++) { d[i] = t % HN; t /= HN; p |= d[i] << (4 * i); }
        pk[g] = p;
        /* alpha: new digit i = old digit i-1 (mod 5) */
        for (int i = 0; i < K; i++) a += d[(i + K - 1) % K] * w[i];
        alp[g] = a;
    }
}

static uint32_t encode(const int *d) {
    uint32_t w = 1, g = 0;
    for (int i = 0; i < K; i++) { g += d[i] * w; w *= HN; }
    return g;
}

static void set_S_from_x(uint32_t x) {
    S[0] = x;
    for (int k = 1; k < K; k++) S[k] = alp[S[k - 1]];
}

static void set_tables(void) {
    uint32_t w = 1;
    for (int t = 0; t < 2 * K; t++) {
        int sd[K];
        uint32_t g;
        if (t < K) g = S[t];
        else {
            /* inverse of S[t-K] componentwise */
            uint32_t s = S[t - K];
            int dd[K];
            for (int i = 0; i < K; i++) dd[i] = (pk[s] >> (4 * i)) & 15;
            for (int i = 0; i < K; i++) dd[i] = hinv[dd[i]];
            g = encode(dd);
        }
        for (int i = 0; i < K; i++) sd[i] = (pk[g] >> (4 * i)) & 15;
        w = 1;
        for (int i = 0; i < K; i++) {
            for (int d = 0; d < 16; d++) P[t][i][d] = (d < HN) ? (uint32_t)hm[sd[i]][d] * w : 0;
            w *= HN;
        }
    }
}

static inline uint32_t lmul(int t, uint32_t g) {
    uint32_t p = pk[g];
    return P[t][0][p & 15] + P[t][1][(p >> 4) & 15] + P[t][2][(p >> 8) & 15] +
           P[t][3][(p >> 12) & 15] + P[t][4][(p >> 16) & 15];
}

/* BFS from src to depth DMAX; returns number of vertices NOT reached */
static uint32_t bfs_unreached(uint32_t src) {
    memset(dist, 255, 2 * NG);
    uint32_t qh = 0, qt = 0;
    Q[qt++] = src;
    dist[src] = 0;
    while (qh < qt) {
        uint32_t v = Q[qh++];
        uint8_t d = dist[v];
        if (d >= DMAX) continue;
        uint8_t nd = d + 1;
        if (v < NG) {
            uint32_t g = v;
            for (int t = 0; t < K; t++) {
                uint32_t u = NG + lmul(t, g);
                if (dist[u] == 255) { dist[u] = nd; Q[qt++] = u; }
            }
        } else {
            uint32_t g = v - NG;
            for (int t = K; t < 2 * K; t++) {
                uint32_t u = lmul(t, g);
                if (dist[u] == 255) { dist[u] = nd; Q[qt++] = u; }
            }
        }
    }
    return 2 * NG - qt;
}

static uint32_t uA, uB; /* last components */

static uint32_t cost_S(void) {
    set_tables();
    uA = bfs_unreached(0);
    uB = bfs_unreached(NG);
    return uA + uB;
}

static int distinct_S(void) {
    for (int i = 0; i < K; i++)
        for (int j = i + 1; j < K; j++)
            if (S[i] == S[j]) return 0;
    return 1;
}

static void write_sol(const char *path, const char *tag) {
    FILE *f = fopen(path, "w");
    if (!f) return;
    fprintf(f, "# b05sym solution (%s): G = D7^5, alpha = coordinate shift, elements as 5 coords (a,b) = r^a s^b\n", tag);
    fprintf(f, "N %u\nS %d\n", NG, K);
    for (int k = 0; k < K; k++) {
        for (int i = 0; i < K; i++) {
            uint32_t d = (pk[S[k]] >> (4 * i)) & 15;
            fprintf(f, "(%u,%u)%s", d % 7, d / 7, i < K - 1 ? " " : "\n");
        }
    }
    fclose(f);
}

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

int main(int argc, char **argv) {
    if (argc < 5) { fprintf(stderr, "usage: %s MODE SECS SEED OUT [INIT_X]\n", argv[0]); return 1; }
    const char *mode = argv[1];
    double secs = atof(argv[2]);
    rs ^= (uint64_t)atoll(argv[3]) * 0x9E3779B97F4A7C15ull + 1;
    for (int i = 0; i < 10; i++) rnd();
    const char *out = argv[4];
    double T0 = getenv("TEMP") ? atof(getenv("TEMP")) : 2.0;
    init_H();
    init_tables();
    double t0 = now();
    long evals = 0;
    uint32_t best = 0xffffffffu, bestx = 0;
    char path[1024];

    if (strcmp(mode, "rand") == 0) {
        int hist[64] = {0};
        uint32_t bestc = 0xffffffffu;
        while (now() - t0 < secs) {
            for (int k = 0; k < K;) {
                uint32_t c = (uint32_t)(rnd() % NG);
                S[k] = c;
                int dup = 0;
                for (int j = 0; j < k; j++) if (S[j] == c) dup = 1;
                if (!dup) k++;
            }
            uint32_t c = cost_S();
            evals++;
            if (c < 63) hist[c]++;
            if (c < bestc) bestc = c;
            if (c == 0) { snprintf(path, sizeof path, "%s.sol", out); write_sol(path, "random S, cost 0"); break; }
        }
        printf("rand evals %ld best %u hist(<=20):", evals, bestc);
        for (int c = 0; c <= 20; c++) printf(" %d", hist[c]);
        printf("\n");
        return 0;
    }

    if (strcmp(mode, "orbit") == 0) {
        int hist[400] = {0};
        while (now() - t0 < secs) {
            uint32_t x = (uint32_t)(rnd() % NG);
            if (alp[x] == x) continue;
            set_S_from_x(x);
            if (!distinct_S()) continue;
            uint32_t c = cost_S();
            evals++;
            if (c < 400) hist[c]++;
            if (c < best) { best = c; bestx = x; }
            if (c == 0) {
                snprintf(path, sizeof path, "%s.sol", out); write_sol(path, "orbit, cost 0");
                snprintf(path, sizeof path, "%s.state", out);
                FILE *f = fopen(path, "w"); if (f) { fprintf(f, "%u %u\n", x, 0u); fclose(f); }
                break;
            }
        }
        printf("orbit evals %ld best %u (x=%u) hist:", evals, best, bestx);
        for (int c = 0; c < 60; c++) if (hist[c]) printf(" %d:%d", c, hist[c]);
        printf("\n");
        snprintf(path, sizeof path, "%s.state", out);
        FILE *f = fopen(path, "w"); if (f) { fprintf(f, "%u %u\n", bestx, best); fclose(f); }
        return 0;
    }

    if (strcmp(mode, "anneal") == 0) {
        uint32_t x;
        if (argc > 5) x = (uint32_t)atol(argv[5]);
        else {
            do { x = (uint32_t)(rnd() % NG); } while (alp[x] == x);
        }
        set_S_from_x(x);
        if (!distinct_S()) { fprintf(stderr, "degenerate start\n"); return 1; }
        uint32_t cur = cost_S(); evals++;
        best = cur; bestx = x;
        uint32_t cx = x;
        long acc = 0;
        while (now() - t0 < secs && cur > 0) {
            /* move: change one coordinate of x */
            int d[K];
            uint32_t p = pk[cx];
            for (int i = 0; i < K; i++) d[i] = (p >> (4 * i)) & 15;
            int i = (int)(rnd() % K);
            int nv = (int)(rnd() % (HN - 1));
            if (nv >= d[i]) nv++;
            d[i] = nv;
            uint32_t nx = encode(d);
            if (alp[nx] == nx) continue;
            set_S_from_x(nx);
            if (!distinct_S()) continue;
            uint32_t c = cost_S(); evals++;
            double dlt = (double)c - (double)cur;
            int ok = dlt <= 0 || ((double)(rnd() % 1000000) / 1e6) < __builtin_exp(-dlt / T0);
            if (ok) { cx = nx; cur = c; acc++; }
            if (cur < best) {
                best = cur; bestx = cx;
                snprintf(path, sizeof path, "%s.state", out);
                FILE *f = fopen(path, "w"); if (f) { fprintf(f, "%u %u\n", bestx, best); fclose(f); }
            }
        }
        if (cur == 0) {
            set_S_from_x(cx); cost_S();
            snprintf(path, sizeof path, "%s.sol", out); write_sol(path, "anneal orbit, cost 0");
        }
        snprintf(path, sizeof path, "%s.state", out);
        FILE *f = fopen(path, "w"); if (f) { fprintf(f, "%u %u\n", bestx, best); fclose(f); }
        printf("anneal evals %ld (%.1f/s) accepted %ld best %u cur %u T %.2f\n",
               evals, evals / (now() - t0), acc, best, cur, T0);
        return 0;
    }

    if (strcmp(mode, "annealS") == 0) {
        /* annealing over unrestricted 5-subsets S (no symmetry) */
        uint32_t cur_S[K];
        if (argc > 5) {
            FILE *f = fopen(argv[5], "r");
            for (int k = 0; k < K; k++) if (fscanf(f, "%u", &cur_S[k]) != 1) return 1;
            fclose(f);
        } else {
            for (int k = 0; k < K;) {
                uint32_t c = (uint32_t)(rnd() % NG); int dup = 0;
                for (int j = 0; j < k; j++) if (cur_S[j] == c) dup = 1;
                if (!dup) cur_S[k++] = c;
            }
        }
        memcpy(S, cur_S, sizeof S);
        uint32_t cur = cost_S(); evals++;
        uint32_t bestS[K]; memcpy(bestS, S, sizeof S);
        best = cur;
        long acc = 0;
        while (now() - t0 < secs && cur > 0) {
            int k = (int)(rnd() % K);
            uint32_t c = (uint32_t)(rnd() % NG);
            uint32_t old = S[k];
            int dup = 0;
            for (int j = 0; j < K; j++) if (S[j] == c) dup = 1;
            if (dup) continue;
            S[k] = c;
            uint32_t nc = cost_S(); evals++;
            double dlt = (double)nc - (double)cur;
            int ok = dlt <= 0 || ((double)(rnd() % 1000000) / 1e6) < __builtin_exp(-dlt / T0);
            if (ok) { cur = nc; acc++; if (cur < best) { best = cur; memcpy(bestS, S, sizeof S); } }
            else S[k] = old;
        }
        if (cur == 0) {
            memcpy(S, bestS, sizeof S); cost_S();
            snprintf(path, sizeof path, "%s.sol", out); write_sol(path, "free S, cost 0");
        }
        snprintf(path, sizeof path, "%s.S", out);
        FILE *f = fopen(path, "w");
        if (f) { for (int k = 0; k < K; k++) fprintf(f, "%u\n", bestS[k]); fclose(f); }
        printf("annealS evals %ld (%.1f/s) accepted %ld best %u cur %u T %.2f\n",
               evals, evals / (now() - t0), acc, best, cur, T0);
        return 0;
    }
    fprintf(stderr, "unknown mode\n");
    return 1;
}
