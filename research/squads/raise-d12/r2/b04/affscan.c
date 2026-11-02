/* affscan.c: exhaustive scan of cubic Haar graphs H(G,S), S = {e,x,y}, over G = F_q x| C_k
 * (C_k <= F_q^* acting on F_q by multiplication; elements (v,a) = v in F_q, a in Z_k,
 * (v,a)(w,b) = (v + mu^a w, a+b), mu a generator of C_k).
 * Haar graph: A-vertex g ~ B-vertex s g for s in S. |V| = 2N, N = q k.
 * Cost of S = number of B-vertices not within distance 11 of A(e) (right-multiplication
 * by G is transitive on each side). For cost 0 the exact diameter is max(ecc A(e), ecc B(e)).
 * usage: affscan p e k OUTPREFIX
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

static int p, e, q, k, N;
static int c[16];
static int *expt, *logt;
static uint16_t *addt;      /* q*q */
static uint16_t *mult;      /* N*N : mult[X*N+Y] = X*Y */
static int *inv_;
static int *vis, *dist, *queue_, stamp = 0;
static int DIAM = 12;

static int math_gcd(int a, int b) { while (b) { int t = a % b; a = b; b = t; } return a; }
static int ipow(int b, int n) { int r = 1; while (n--) r *= b; return r; }

static int addf(int a, int b) {
    int r = 0, pw = 1;
    for (int i = 0; i < e; i++) {
        int da = a % p, db = b % p;
        r += ((da + db) % p) * pw;
        a /= p; b /= p; pw *= p;
    }
    return r;
}

static int mulx(int v) {
    int dd[16], nd[16];
    for (int i = 0; i < e; i++) { dd[i] = v % p; v /= p; }
    int top = dd[e - 1];
    for (int i = e - 1; i >= 0; i--) {
        int lower = (i == 0) ? 0 : dd[i - 1];
        int val = (lower - top * c[i]) % p;
        if (val < 0) val += p;
        nd[i] = val;
    }
    int r = 0, pw = 1;
    for (int i = 0; i < e; i++) { r += nd[i] * pw; pw *= p; }
    return r;
}

static int fmul(int a, int b) {
    if (a == 0 || b == 0) return 0;
    return expt[(logt[a] + logt[b]) % (q - 1)];
}

static int build_field(void) {
    expt = malloc(sizeof(int) * q);
    logt = malloc(sizeof(int) * q);
    int *seen = malloc(sizeof(int) * q);
    for (int t = 0; t < q; t++) {
        int tt = t;
        for (int i = 0; i < e; i++) { c[i] = tt % p; tt /= p; }
        memset(seen, 0, sizeof(int) * q);
        int cur = 1, ok = 1;
        for (int i = 0; i < q - 1; i++) {
            if (cur == 0 || seen[cur]) { ok = 0; break; }
            seen[cur] = 1; expt[i] = cur; cur = mulx(cur);
        }
        if (ok && cur == 1) {
            for (int i = 0; i < q - 1; i++) logt[expt[i]] = i;
            free(seen);
            return 1;
        }
    }
    free(seen);
    return 0;
}

static int bfs(int start, const int *sl, const int *sil, int ns, int maxexp, int *maxd_out) {
    /* sl: multipliers s (A -> B: s g); sil: inverses (B -> A: s^{-1} h). Expands nodes with dist < maxexp. */
    stamp++;
    int head = 0, tail = 0, maxd = 0, cnt = 0;
    vis[start] = stamp; dist[start] = 0; queue_[tail++] = start; cnt = 1;
    while (head < tail) {
        int u = queue_[head++];
        int du = dist[u];
        if (du >= maxexp) continue;
        if (du > maxd) maxd = du;
        if (u < N) {
            for (int j = 0; j < ns; j++) {
                int w = N + mult[(size_t)sl[j] * N + u];
                if (vis[w] != stamp) { vis[w] = stamp; dist[w] = du + 1; queue_[tail++] = w; cnt++; }
            }
        } else {
            int h = u - N;
            for (int j = 0; j < ns; j++) {
                int w = mult[(size_t)sil[j] * N + h];
                if (vis[w] != stamp) { vis[w] = stamp; dist[w] = du + 1; queue_[tail++] = w; cnt++; }
            }
        }
    }
    if (maxd_out) *maxd_out = maxd;
    return cnt;
}

int main(int argc, char **argv) {
    if (argc < 5) { fprintf(stderr, "usage: affscan p e k OUTPREFIX\n"); return 1; }
    p = atoi(argv[1]); e = atoi(argv[2]); k = atoi(argv[3]);
    const char *outp = argv[4];
    q = ipow(p, e); N = q * k;
    if (!build_field()) { fprintf(stderr, "no primitive poly\n"); return 1; }
    addt = malloc(sizeof(uint16_t) * (size_t)q * q);
    for (int a = 0; a < q; a++) for (int b = 0; b < q; b++) addt[(size_t)a * q + b] = addf(a, b);
    mult = malloc(sizeof(uint16_t) * (size_t)N * N);
    inv_ = malloc(sizeof(int) * N);
    int step = (q - 1) / k;
    int *ma = malloc(sizeof(int) * k);
    for (int a = 0; a < k; a++) ma[a] = expt[(a * step) % (q - 1)];
    for (int v = 0; v < q; v++) for (int a = 0; a < k; a++) {
        int g = v * k + a;
        for (int w = 0; w < q; w++) for (int b = 0; b < k; b++) {
            int h = w * k + b;
            int v2 = addt[(size_t)v * q + fmul(ma[a], w)];
            int a2 = (a + b) % k;
            mult[(size_t)g * N + h] = (uint16_t)(v2 * k + a2);
        }
    }
    for (int g = 0; g < N; g++) {
        int found = 0;
        for (int h = 0; h < N; h++) if (mult[(size_t)g * N + h] == 0) { inv_[g] = h; found = 1; break; }
        if (!found) { fprintf(stderr, "no inverse\n"); return 1; }
    }
    /* orbit representatives of x under <scaling v->lambda v, conjugations by (1,0),(0,1), Frobenius (v,a)->(v^p,p a)> */
    int *par = malloc(sizeof(int) * N);
    for (int i = 0; i < N; i++) par[i] = i;
#define FIND(z) ({ int _z = (z); while (par[_z] != _z) { par[_z] = par[par[_z]]; _z = par[_z]; } _z; })
    int *fr = malloc(sizeof(int) * q);
    for (int v = 0; v < q; v++) { int r = 1; for (int t = 0; t < p; t++) r = fmul(r, v); fr[v] = (v == 0) ? 0 : r; }
    int lam = expt[1];
    int gens[2] = { 1 * k + 0, 0 * k + 1 };   /* (1,0) and (0,1) */
    for (int x = 0; x < N; x++) {
        int v = x / k, a = x % k;
        int imgs[4];
        imgs[0] = fmul(lam, v) * k + a;
        imgs[1] = (math_gcd(p, k) == 1) ? fr[v] * k + ((p % k) * a) % k : x;   /* Frobenius only if gcd(p,k)=1 */
        for (int t = 0; t < 2; t++) {
            int g = gens[t]; int ig = inv_[g];
            imgs[2 + t] = mult[(size_t)g * N + mult[(size_t)x * N + ig]];
        }
        for (int t = 0; t < 4; t++) {
            int r1 = FIND(x), r2 = FIND(imgs[t]);
            if (r1 != r2) par[r1] = r2;
        }
    }
    int nreps = 0;
    int *isrep = calloc(N, sizeof(int));
    for (int x = 0; x < N; x++) if (FIND(x) == x) { isrep[x] = 1; nreps++; }

    fprintf(stderr, "orbits under scaling/conjugation/Frobenius: %d (of N=%d)\n", nreps, N);
    if (getenv("FULL")) for (int x = 0; x < N; x++) isrep[x] = 1;   /* sanity mode: no reduction */
    /* sanity: associativity on random triples */
    for (int t = 0; t < 2000; t++) {
        int a = rand() % N, b = rand() % N, cc = rand() % N;
        int l = mult[(size_t)mult[(size_t)a * N + b] * N + cc];
        int r = mult[(size_t)a * N + mult[(size_t)b * N + cc]];
        if (l != r) { fprintf(stderr, "assoc fail\n"); return 1; }
    }
    vis = calloc(2 * N, sizeof(int)); dist = calloc(2 * N, sizeof(int)); queue_ = malloc(sizeof(int) * 2 * N);

    int bestcost = 1 << 30, nbest = 0, nzero = 0, bx = -1, by = -1;
    long hist[64]; memset(hist, 0, sizeof(hist));
    int sl[3], sil[3];
    long npairs = 0;
    for (int x = 1; x < N; x++) if (isrep[x]) for (int y = 1; y < N; y++) if (y != x) {
        sl[0] = 0; sl[1] = x; sl[2] = y;
        sil[0] = 0; sil[1] = inv_[x]; sil[2] = inv_[y];
        bfs(0, sl, sil, 3, 11, NULL);
        int cost = 0;
        for (int h = 0; h < N; h++) {
            int id = N + h;
            if (vis[id] != stamp || dist[id] > 11) cost++;
        }
        npairs++;
        if (cost < 64) hist[cost]++;
        if (cost < bestcost) { bestcost = cost; nbest = 0; bx = x; by = y; }
        if (cost == bestcost) nbest++;
        if (cost == 0) {
            nzero++;
            /* exact diameter: full BFS from A(e) and B(e) */
            int dA, dB;
            int cA = bfs(0, sl, sil, 3, 1 << 20, &dA);
            int cB = bfs(N, sl, sil, 3, 1 << 20, &dB);
            int full = (cA == 2 * N && cB == 2 * N);
            int dmax = dA > dB ? dA : dB;
            /* eccentricity over all reached nodes (bfs returns maxd of expanded nodes only; recompute) */
            printf("COST0 x=%d y=%d reachedA=%d reachedB=%d maxdA_expanded=%d maxdB_expanded=%d full=%d\n",
                   x, y, cA, cB, dA, dB, full);
            fflush(stdout);
            if (full && dmax <= DIAM) {
                char fn[512];
                snprintf(fn, sizeof fn, "%s_q%d_k%d_x%d_y%d.edges", outp, q, k, x, y);
                FILE *f = fopen(fn, "w");
                fprintf(f, "%d\n", 2 * N);
                for (int g = 0; g < N; g++) {
                    for (int j = 0; j < 3; j++) {
                        int h = mult[(size_t)sl[j] * N + g];
                        fprintf(f, "%d %d\n", g, N + h);
                    }
                }
                fclose(f);
                printf("WROTE %s\n", fn);
                fflush(stdout);
            }
        }
    }
    printf("RESULT p=%d e=%d k=%d q=%d N=%d vertices=%d pairs=%ld bestcost=%d (count %d, pair x=%d y=%d) zero=%d\n",
           p, e, k, q, N, 2 * N, npairs, bestcost, nbest, bx, by, nzero);
    printf("HIST");
    for (int i = 0; i < 16; i++) printf(" %d:%ld", i, hist[i]);
    printf("\n");
    return 0;
}
