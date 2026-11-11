/* cay3.c: cubic Cayley graphs Cay(G,{a,b,c}) with a,b,c involutions of G.
 * Graph is bipartite iff BFS level parities alternate on every edge (checked per candidate).
 * Vertex-transitive: diameter = eccentricity of identity (index 0).
 * Cost = number of vertices at distance > D from identity (0 = diameter <= D).
 *
 * usage: cay3 FAM PAR D SECS SEED MODE [OUTPREFIX]
 *   FAM: pgl q | psl q | pglz2 q | pslz2 q | sym n   (q prime)
 *   MODE: rand | anneal | exh
 * env: T0, T1 (anneal temperatures in cost units, defaults 20, 0.5)
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXM 40
static int m, N, K;
static unsigned char *el;
static int *htab;
static uint64_t HS;
static int *invl;
static uint16_t **R;
static unsigned char *dist;
static int *qu;
static int D;
static int last_ecc;

static uint64_t hp(const unsigned char *p) {
    uint64_t h = 1469598103934665603ULL;
    for (int i = 0; i < m; i++) { h ^= p[i]; h *= 1099511628211ULL; }
    return h;
}
static int lookup(const unsigned char *p) {
    uint64_t h = hp(p) & (HS - 1);
    for (;;) {
        int v = htab[h];
        if (!v) return -1;
        if (!memcmp(el + (size_t)(v - 1) * m, p, m)) return v - 1;
        h = (h + 1) & (HS - 1);
    }
}
static void ins(const unsigned char *p, int idx) {
    uint64_t h = hp(p) & (HS - 1);
    while (htab[h]) h = (h + 1) & (HS - 1);
    htab[h] = idx + 1;
}
/* r = g o s (apply s first) */
static void comp(const unsigned char *g, const unsigned char *s, unsigned char *r) {
    for (int i = 0; i < m; i++) r[i] = g[s[i]];
}

static int build(int ng, unsigned char gens[][MAXM], int maxN) {
    el = malloc((size_t)maxN * m);
    HS = 1; while (HS < 4ULL * maxN) HS <<= 1;
    htab = calloc(HS, sizeof(int));
    N = 1;
    for (int i = 0; i < m; i++) el[i] = i;
    ins(el, 0);
    unsigned char tmp[MAXM];
    for (int h = 0; h < N; h++) {
        for (int s = 0; s < ng; s++) {
            comp(el + (size_t)h * m, gens[s], tmp);
            if (lookup(tmp) < 0) {
                if (N >= maxN) { fprintf(stderr, "group overflow\n"); exit(1); }
                memcpy(el + (size_t)N * m, tmp, m);
                ins(tmp, N);
                N++;
            }
        }
    }
    return N;
}

static int evalc(int a, int b, int c) {
    uint16_t *ra = R[a], *rb = R[b], *rc = R[c];
    memset(dist, 255, N);
    int h = 0, t = 0;
    qu[t++] = 0; dist[0] = 0;
    while (h < t) {
        int g = qu[h++];
        unsigned char dg = dist[g] + 1;
        int x;
        x = ra[g]; if (dist[x] == 255) { dist[x] = dg; qu[t++] = x; }
        x = rb[g]; if (dist[x] == 255) { dist[x] = dg; qu[t++] = x; }
        x = rc[g]; if (dist[x] == 255) { dist[x] = dg; qu[t++] = x; }
    }
    /* bipartite check on the reached component */
    for (int i = 0; i < t; i++) {
        int g = qu[i];
        unsigned char dg = dist[g];
        if (((dist[ra[g]] ^ dg) & 1) == 0) return 2 * N;
        if (((dist[rb[g]] ^ dg) & 1) == 0) return 2 * N;
        if (((dist[rc[g]] ^ dg) & 1) == 0) return 2 * N;
    }
    int cnt = 0;
    for (int i = 0; i < t; i++) if (dist[qu[i]] <= D) cnt++;
    last_ecc = dist[qu[t - 1]];
    if (t < N) last_ecc = 999;
    return N - cnt;
}

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + 1e-9 * ts.tv_nsec;
}
static int rnd(int n) { return (int)(drand48() * n); }

static int powmod(int b, int e, int mod) {
    long r = 1, x = b % mod;
    while (e) { if (e & 1) r = r * x % mod; x = x * x % mod; e >>= 1; }
    return (int)r;
}
static int primroot(int q) {
    for (int g = 2; g < q; g++) {
        int x = 1, ord = 0;
        do { x = x * g % q; ord++; } while (x != 1);
        if (ord == q - 1) return g;
    }
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 7) {
        fprintf(stderr, "usage: cay3 FAM PAR D SECS SEED MODE [OUTPREFIX]\n");
        return 1;
    }
    const char *fam = argv[1];
    int par = atoi(argv[2]);
    D = atoi(argv[3]);
    double secs = atof(argv[4]);
    long seed = atol(argv[5]);
    const char *mode = argv[6];
    const char *outp = argc > 7 ? argv[7] : NULL;
    double T0 = getenv("T0") ? atof(getenv("T0")) : 20.0;
    double T1 = getenv("T1") ? atof(getenv("T1")) : 0.5;

    unsigned char gens[4][MAXM];
    int ng = 0;
    if (!strcmp(fam, "sym")) {
        m = par;
        for (int i = 0; i < m; i++) gens[0][i] = i;
        gens[0][0] = 1; gens[0][1] = 0;
        for (int i = 0; i < m; i++) gens[1][i] = (i + 1) % m;
        ng = 2;
    } else {
        int q = par;
        int z2 = (!strcmp(fam, "pglz2") || !strcmp(fam, "pslz2"));
        int psl = (!strcmp(fam, "psl") || !strcmp(fam, "pslz2"));
        m = q + 1 + (z2 ? 2 : 0);
        int lam = primroot(q);
        int mu = psl ? (lam * lam) % q : lam;
        for (int i = 0; i < m; i++) gens[0][i] = i;
        for (int x = 0; x < q; x++) gens[0][x] = (x + 1) % q;
        for (int i = 0; i < m; i++) gens[1][i] = i;
        for (int x = 0; x < q; x++) gens[1][x] = (x * mu) % q;
        for (int i = 0; i < m; i++) gens[2][i] = i;
        gens[2][0] = q; gens[2][q] = 0;
        for (int x = 1; x < q; x++) gens[2][x] = (q - powmod(x, q - 2, q)) % q;
        ng = 3;
        if (z2) {
            for (int i = 0; i < m; i++) gens[3][i] = i;
            gens[3][q + 1] = q + 2; gens[3][q + 2] = q + 1;
            ng = 4;
        }
    }
    int maxN = 60000;
    build(ng, gens, maxN);
    unsigned char tmp[MAXM];
    int *ti = malloc(sizeof(int) * N);
    K = 0;
    for (int g = 1; g < N; g++) {
        comp(el + (size_t)g * m, el + (size_t)g * m, tmp);
        int id = 1;
        for (int i = 0; i < m; i++) if (tmp[i] != i) { id = 0; break; }
        if (id) ti[K++] = g;
    }
    invl = ti;
    R = malloc(sizeof(uint16_t *) * K);
    for (int k = 0; k < K; k++) {
        R[k] = malloc(sizeof(uint16_t) * N);
        for (int g = 0; g < N; g++) {
            comp(el + (size_t)g * m, el + (size_t)invl[k] * m, tmp);
            R[k][g] = (uint16_t)lookup(tmp);
        }
    }
    dist = malloc(N);
    qu = malloc(sizeof(int) * N);
    fprintf(stderr, "group %s %d: N=%d involutions K=%d D=%d\n", fam, par, N, K, D);
    if (K < 3) { printf("too few involutions\n"); return 0; }

    srand48(seed);
    int best = 1 << 30, ba = -1, bb = -1, bc = -1, bestecc = -1;
    long evals = 0;
    double t0 = now();
    if (!strcmp(mode, "exhc")) {
        /* WLOG a = class representative (conjugation keeps the Cayley graph isomorphic).
         * Conjugacy classes of involutions computed by orbits under conjugation by the generators. */
        int *kidx = malloc(sizeof(int) * N), *lab = malloc(sizeof(int) * K), *queue = malloc(sizeof(int) * N);
        unsigned char ginv[4][MAXM], t1[MAXM], t2[MAXM];
        for (int s = 0; s < ng; s++) for (int i = 0; i < m; i++) ginv[s][gens[s][i]] = i;
        for (int g = 0; g < N; g++) kidx[g] = -1;
        for (int k = 0; k < K; k++) kidx[invl[k]] = k;
        for (int k = 0; k < K; k++) lab[k] = -1;
        int ncls = 0, *rep = malloc(sizeof(int) * K), *csz = malloc(sizeof(int) * K);
        for (int k = 0; k < K; k++) {
            if (lab[k] >= 0) continue;
            int qh = 0, qt = 0; queue[qt++] = invl[k]; lab[k] = ncls; int sz = 0;
            while (qh < qt) {
                int y = queue[qh++]; sz++;
                for (int s = 0; s < ng; s++) {
                    comp(el + (size_t)y * m, gens[s], t1);
                    comp(ginv[s], t1, t2);
                    int z = lookup(t2);
                    int kz = kidx[z];
                    if (kz >= 0 && lab[kz] < 0) { lab[kz] = ncls; queue[qt++] = z; }
                }
            }
            rep[ncls] = k; csz[ncls] = sz; ncls++;
        }
        for (int c = 0; c < ncls; c++) fprintf(stderr, "class %d: rep %d size %d\n", c, rep[c], csz[c]);
        for (int c = 0; c < ncls && now() - t0 < secs; c++) {
            int a = rep[c];
            for (int b = 0; b < K && now() - t0 < secs; b++)
                for (int cc = b + 1; cc < K; cc++) {
                    if (b == a || cc == a) continue;
                    int cost = evalc(a, b, cc); evals++;
                    if (cost < best) { best = cost; ba = a; bb = b; bc = cc; bestecc = last_ecc; }
                }
            fprintf(stderr, "class %d done, best so far %d\n", c, best);
        }
    } else if (!strcmp(mode, "exh")) {
        for (int a = 0; a < K && now() - t0 < secs; a++)
            for (int b = a + 1; b < K && now() - t0 < secs; b++)
                for (int c = b + 1; c < K; c++) {
                    int cost = evalc(a, b, c); evals++;
                    if (cost < best) { best = cost; ba = a; bb = b; bc = c; bestecc = last_ecc; }
                }
    } else {
        double tr = !strcmp(mode, "anneal") ? 0.3 * secs : secs;
        while (now() - t0 < tr) {
            int a = rnd(K), b = rnd(K), c = rnd(K);
            if (a == b || b == c || a == c) continue;
            int cost = evalc(a, b, c); evals++;
            if (cost < best) { best = cost; ba = a; bb = b; bc = c; bestecc = last_ecc; }
        }
        if (!strcmp(mode, "anneal") && ba >= 0) {
            int cur = best, t[3] = {ba, bb, bc};
            double ts = now(), tot = 0.7 * secs;
            while (1) {
                double el_t = now() - ts;
                if (el_t >= tot) break;
                double T = T0 * pow(T1 / T0, el_t / tot);
                int p = rnd(3), x = rnd(K);
                if (x == t[0] || x == t[1] || x == t[2]) continue;
                int nt[3] = {t[0], t[1], t[2]};
                nt[p] = x;
                int cost = evalc(nt[0], nt[1], nt[2]); evals++;
                if (cost <= cur || drand48() < exp(-(cost - cur) / T)) {
                    t[0] = nt[0]; t[1] = nt[1]; t[2] = nt[2];
                    cur = cost;
                    if (cost < best) { best = cost; ba = t[0]; bb = t[1]; bc = t[2]; bestecc = last_ecc; }
                }
            }
        }
    }
    printf("RESULT fam=%s par=%d N=%d K=%d D=%d mode=%s best_cost=%d ecc=%d a=%d b=%d c=%d evals=%ld secs=%.1f\n",
           fam, par, N, K, D, mode, best, bestecc, ba, bb, bc, evals, now() - t0);
    if (best == 0 && outp) {
        char fn[512];
        snprintf(fn, sizeof fn, "%s.edges", outp);
        FILE *f = fopen(fn, "w");
        fprintf(f, "%d\n", N);
        int ks[3] = {ba, bb, bc};
        for (int j = 0; j < 3; j++)
            for (int g = 0; g < N; g++) {
                int h = R[ks[j]][g];
                if (g < h) fprintf(f, "%d %d\n", g, h);
            }
        fclose(f);
        printf("wrote %s\n", fn);
    }
    return 0;
}
