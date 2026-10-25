/* Two-cycle lift search (card c1).
   Vertices (i,0)=i and (i,1)=n+i, i in Z_n. Edges: both n-cycles, plus matching (j,0)~(j+F[j mod s] mod n, 1).
   F must make a -> (a+F[a]) mod s a permutation of Z_s; par=0 means all F even, par=1 all F odd (n even).
   Symmetry j->j+s, so BFS from the 2s representatives (a,0),(a,1), a<s. Cost = #(rep,vertex) pairs at distance > D.
   Usage:
     lift2cyc anneal n s D par iters restarts seed outprefix
     lift2cyc eval n s D outfile F0 ... F(s-1)                       */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>

#define MAXN 1024
#define MAXS 1024

static uint64_t rs = 88172645463325252ULL;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline int rndi(int m) { return (int)(rnd() % (uint64_t)m); }
static inline double rndu(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int n, s, D, par;
static int F[MAXS];
static int mm[MAXN], inv[MAXN];

static int cost(void) {
    for (int j = 0; j < n; j++) mm[j] = (j + F[j % s]) % n;
    for (int j = 0; j < n; j++) inv[mm[j]] = j;
    int V = 2 * n, total = 0;
    static int dist[2 * MAXN], q[2 * MAXN];
    for (int a = 0; a < s; a++) for (int b = 0; b < 2; b++) {
        int src = b * n + a;
        for (int v = 0; v < V; v++) dist[v] = -1;
        int h = 0, t = 0, reached = 1;
        dist[src] = 0; q[t++] = src;
        while (h < t) {
            int x = q[h++], dx = dist[x];
            if (dx >= D) continue;
            int nb[3], k = 0;
            if (x < n) { int i = x; nb[k++] = (i + 1) % n; nb[k++] = (i + n - 1) % n; nb[k++] = n + mm[i]; }
            else { int i = x - n; nb[k++] = n + (i + 1) % n; nb[k++] = n + (i + n - 1) % n; nb[k++] = inv[i]; }
            for (int z = 0; z < k; z++) { int y = nb[z]; if (dist[y] < 0) { dist[y] = dx + 1; q[t++] = y; reached++; } }
        }
        total += V - reached;
    }
    return total;
}

static int md(int x, int m) { x %= m; return x < 0 ? x + m : x; }

/* random valid F: permutation p of Z_s with parity constraint, then shifts */
static void random_init(void) {
    int p[MAXS], idx = 0;
    if (s % 2 == 0) {
        int ev[MAXS], od[MAXS], ne = 0, no = 0;
        for (int x = 0; x < s; x++) { if (x % 2 == 0) ev[ne++] = x; else od[no++] = x; }
        /* shuffle helper */
        for (int i = ne - 1; i > 0; i--) { int j = rndi(i + 1), t = ev[i]; ev[i] = ev[j]; ev[j] = t; }
        for (int i = no - 1; i > 0; i--) { int j = rndi(i + 1), t = od[i]; od[i] = od[j]; od[j] = t; }
        if (par == 0) {
            for (int a = 0; a < s; a++) p[a] = (a % 2 == 0) ? 0 : 0;
            int ie = 0, io = 0;
            for (int a = 0; a < s; a++) { if (a % 2 == 0) p[a] = ev[ie++]; }
            for (int a = 0; a < s; a++) { if (a % 2 == 1) p[a] = od[io++]; }
        } else {
            int ie = 0, io = 0;
            for (int a = 0; a < s; a++) { if (a % 2 == 0) p[a] = od[io++]; }
            for (int a = 0; a < s; a++) { if (a % 2 == 1) p[a] = ev[ie++]; }
        }
    } else {
        for (int a = 0; a < s; a++) p[a] = a;
        for (int i = s - 1; i > 0; i--) { int j = rndi(i + 1), t = p[i]; p[i] = p[j]; p[j] = t; }
    }
    (void)idx;
    for (int a = 0; a < s; a++) {
        int v = md(p[a] - a, s) + s * rndi(n / s);
        if (v % 2 != par) v = (v + s) % n;
        F[a] = v;
    }
}

/* move: returns 1 and fills undo info if applied */
static int propose(int *ua, int *uoa, int *ub, int *uob) {
    if (s == 1 || rndi(2) == 0) {
        int a = rndi(s);
        int base = md(F[a], s);
        int v = base + s * rndi(n / s);
        if (v % 2 != par) { if (s % 2 == 0) return 0; v = (v + s) % n; }
        *ua = a; *uoa = F[a]; *ub = -1;
        F[a] = v;
        return 1;
    } else {
        int a = rndi(s), b = rndi(s);
        if (a == b) return 0;
        int ra = md(a + F[a], s), rb = md(b + F[b], s);
        int ba = md(rb - a, s), bb = md(ra - b, s);
        int va = ba + s * rndi(n / s), vb = bb + s * rndi(n / s);
        if (va % 2 != par) { if (s % 2 == 0) return 0; va = (va + s) % n; }
        if (vb % 2 != par) { if (s % 2 == 0) return 0; vb = (vb + s) % n; }
        *ua = a; *uoa = F[a]; *ub = b; *uob = F[b];
        F[a] = va; F[b] = vb;
        return 1;
    }
}

static void write_graph(const char *fn) {
    cost();
    FILE *f = fopen(fn, "w");
    if (!f) { perror("fopen"); exit(1); }
    fprintf(f, "%d\n", 2 * n);
    for (int i = 0; i < n; i++) {
        fprintf(f, "%d %d\n", i, (i + 1) % n);
        fprintf(f, "%d %d\n", n + i, n + (i + 1) % n);
        fprintf(f, "%d %d\n", i, n + mm[i]);
    }
    fclose(f);
}

int main(int argc, char **argv) {
    if (argc < 2) { fprintf(stderr, "usage\n"); return 2; }
    if (!strcmp(argv[1], "eval")) {
        n = atoi(argv[2]); s = atoi(argv[3]); D = atoi(argv[4]);
        const char *out = argv[5];
        for (int a = 0; a < s; a++) F[a] = atoi(argv[6 + a]);
        int c = cost();
        printf("cost=%d n=%d s=%d D=%d\n", c, n, s, D);
        write_graph(out);
        return 0;
    }
    if (!strcmp(argv[1], "anneal")) {
        n = atoi(argv[2]); s = atoi(argv[3]); D = atoi(argv[4]); par = atoi(argv[5]);
        long iters = atol(argv[6]); int restarts = atoi(argv[7]);
        rs ^= (uint64_t)atoll(argv[8]) * 0x9E3779B97F4A7C15ULL; if (!rs) rs = 1;
        const char *pref = argv[9];
        if (n % s || n % 2) { fprintf(stderr, "bad n/s\n"); return 2; }
        int bestover = 1 << 30;
        for (int r = 0; r < restarts; r++) {
            random_init();
            int cur = cost(), best = cur;
            double T0 = 2.0, T1 = 0.05;
            for (long it = 0; it < iters; it++) {
                double T = T0 * pow(T1 / T0, (double)it / (double)iters);
                int ua, ub = -1, uoa, uob = 0;
                if (!propose(&ua, &uoa, &ub, &uob)) continue;
                int nc = cost();
                int delta = nc - cur;
                if (delta <= 0 || rndu() < exp(-delta / T)) {
                    cur = nc;
                    if (cur < best) best = cur;
                    if (cur == 0) break;
                } else {
                    F[ua] = uoa; if (ub >= 0) F[ub] = uob;
                }
            }
            if (best < bestover) bestover = best;
            fprintf(stderr, "restart %d best=%d final=%d\n", r, best, cur);
            if (cur == 0) {
                char fn[512]; snprintf(fn, sizeof fn, "%s_n%d_s%d_D%d.txt", pref, n, s, D);
                write_graph(fn);
                printf("FOUND n=%d s=%d D=%d par=%d file=%s F=", n, s, D, par, fn);
                for (int a = 0; a < s; a++) printf("%d%s", F[a], a + 1 < s ? "," : "\n");
                return 0;
            }
        }
        printf("NOTFOUND n=%d s=%d D=%d par=%d bestcost=%d\n", n, s, D, par, bestover);
        return 1;
    }
    return 2;
}
