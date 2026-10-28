/* wls.c: weighted local search for large relaxed sets of a graph (squad d5relax-r1, card c1).
   A relaxed set T: every vertex of T has at most one neighbour in T (induced subgraph = matching + isolated points).
   Penalty f = sum_{v in T} w(v) * max(0, nbT[v] - 1), with a weight w(v) >= 1 on every vertex (weights persist).
   Fixed size k, one swap per step: remove x in T (largest drop of f), then add y outside T (smallest rise of f).
   f == 0: the set is recorded and the cheapest outside point is added (k grows).
   Stall (a swap that does not lower f): every violated T-point (nbT >= 2) gets w += 1 (NuMVC-style weighting).
   Configuration checking (-c 1, default): a point removed from T may not be re-added until one of its neighbours
   changed state.  -c 0: plain tabu of -T steps on re-adding instead.  The point added in the last step may not be
   removed in the next step.
   Forgetting: when the mean weight exceeds gamma, w <- max(1, floor(rho*w)).
   -m 0: remove the globally best T-point.  -m 1: pick a random violated T-point v and remove the best of {v} and its
   T-neighbours (focused removal).
   usage: wls ADJ seconds seed out [-i START] [-t target] [-m mode] [-g gamma] [-r rho] [-c cc] [-T tt]
   ADJ: n, then per vertex: degree, neighbours.  out: size, then the vertices (same as rtabu). */
#include <limits.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

static int n, *deg, **nb;
static int *w, *nbT, *inT, *Tl, *pos, *conf, *viol, k;
static long *A1, *R2, *age, *tabuUntil, f, Wsum, it;
static int use_cc = 1, tt = 10, mode = 0, tabuRem = -1;
static double rho = 0.3, gam = 100.0;
static unsigned long long rs = 88172645463325252ULL;
static inline unsigned rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return (unsigned)(rs >> 11); }

static inline long excess(int v) { return nbT[v] > 1 ? nbT[v] - 1 : 0; }
static inline long drop(int x) { return (long)w[x] * excess(x) + R2[x]; } /* f decrease if x leaves T */
static inline long rise(int u) { return (long)w[u] * excess(u) + A1[u]; } /* f increase if u joins T */
static inline int allowed(int u) { return use_cc ? conf[u] : (tabuUntil[u] <= it); }

/* A1[z] = sum of w(v) over v in T, v ~ z, nbT[v] >= 1.   R2[z] = same over nbT[v] >= 2. (maintained for all z) */
static void addv(int y) {
    f += rise(y);
    for (int i = 0; i < deg[y]; i++) {
        int u = nb[y][i], old = nbT[u];
        nbT[u] = old + 1;
        if (inT[u]) {
            if (old == 0) for (int j = 0; j < deg[u]; j++) A1[nb[u][j]] += w[u];
            else if (old == 1) for (int j = 0; j < deg[u]; j++) R2[nb[u][j]] += w[u];
        }
    }
    inT[y] = 1; pos[y] = k; Tl[k++] = y;
    if (nbT[y] >= 1) for (int j = 0; j < deg[y]; j++) A1[nb[y][j]] += w[y];
    if (nbT[y] >= 2) for (int j = 0; j < deg[y]; j++) R2[nb[y][j]] += w[y];
}

static void remv(int x) {
    f -= drop(x);
    if (nbT[x] >= 1) for (int j = 0; j < deg[x]; j++) A1[nb[x][j]] -= w[x];
    if (nbT[x] >= 2) for (int j = 0; j < deg[x]; j++) R2[nb[x][j]] -= w[x];
    inT[x] = 0;
    int p = pos[x]; Tl[p] = Tl[--k]; pos[Tl[p]] = p;
    for (int i = 0; i < deg[x]; i++) {
        int u = nb[x][i], old = nbT[u];
        nbT[u] = old - 1;
        if (inT[u]) {
            if (old == 1) for (int j = 0; j < deg[u]; j++) A1[nb[u][j]] -= w[u];
            else if (old == 2) for (int j = 0; j < deg[u]; j++) R2[nb[u][j]] -= w[u];
        }
    }
}

/* full recomputation of nbT, A1, R2, f from T and w */
static void rebuild(void) {
    memset(nbT, 0, n * sizeof(int)); memset(A1, 0, n * sizeof(long)); memset(R2, 0, n * sizeof(long));
    for (int i = 0; i < k; i++) { int v = Tl[i]; for (int j = 0; j < deg[v]; j++) nbT[nb[v][j]]++; }
    f = 0;
    for (int i = 0; i < k; i++) f += (long)w[Tl[i]] * excess(Tl[i]);
    for (int i = 0; i < k; i++) {
        int v = Tl[i];
        if (nbT[v] >= 1) for (int j = 0; j < deg[v]; j++) A1[nb[v][j]] += w[v];
        if (nbT[v] >= 2) for (int j = 0; j < deg[v]; j++) R2[nb[v][j]] += w[v];
    }
}

/* every violated T-point gets weight +1 (its excess grows by nbT-1 in f) */
static long bump(void) {
    long cnt = 0;
    for (int i = 0; i < k; i++) {
        int v = Tl[i];
        if (nbT[v] < 2) continue;
        cnt++;
        w[v]++; Wsum++; f += nbT[v] - 1;
        for (int j = 0; j < deg[v]; j++) { A1[nb[v][j]]++; R2[nb[v][j]]++; }
    }
    return cnt;
}

static void forget(void) {
    Wsum = 0;
    for (int v = 0; v < n; v++) { int x = (int)(w[v] * rho); w[v] = x < 1 ? 1 : x; Wsum += w[v]; }
    rebuild();
}

static int pick_remove(void) {
    if (mode == 0) {
        long bd = -1, ba = LONG_MAX; int bx = -1;
        for (int i = 0; i < k; i++) {
            int x = Tl[i];
            if (x == tabuRem) continue;
            long d = drop(x);
            if (d > bd || (d == bd && age[x] < ba)) { bd = d; ba = age[x]; bx = x; }
        }
        return bx >= 0 ? bx : Tl[rnd() % k];
    }
    int nv = 0;
    for (int i = 0; i < k; i++) if (nbT[Tl[i]] >= 2) viol[nv++] = Tl[i];
    if (nv == 0) return Tl[rnd() % k];
    int v = viol[rnd() % nv];
    long bd = -1, ba = LONG_MAX; int bx = -1;
    for (int c = -1; c < deg[v]; c++) {
        int x = c < 0 ? v : nb[v][c];
        if (!inT[x] || x == tabuRem) continue;
        long d = drop(x);
        if (d > bd || (d == bd && age[x] < ba)) { bd = d; ba = age[x]; bx = x; }
    }
    return bx >= 0 ? bx : v;
}

static int pick_add(int useconf) {
    long bs = LONG_MAX, ba = LONG_MAX; int bu = -1;
    int start = rnd() % n;
    for (int t = 0; t < n; t++) {
        int u = start + t; if (u >= n) u -= n;
        if (inT[u]) continue;
        if (useconf && !allowed(u)) continue;
        long s = rise(u);
        if (s < bs || (s == bs && age[u] < ba)) { bs = s; ba = age[u]; bu = u; }
    }
    if (bu < 0 && useconf) return pick_add(0);
    return bu;
}

static void save(const char *fn) {
    FILE *o = fopen(fn, "w"); if (!o) return;
    fprintf(o, "%d\n", k);
    for (int i = 0; i < k; i++) fprintf(o, "%d\n", Tl[i]);
    fclose(o);
}

int main(int argc, char **argv) {
    if (argc < 5) { fprintf(stderr, "usage: wls ADJ seconds seed out [-i START] [-t target] [-m mode] [-g gamma] [-r rho] [-c cc] [-T tt]\n"); return 1; }
    FILE *g = fopen(argv[1], "r"); if (!g || fscanf(g, "%d", &n) != 1) return 1;
    deg = malloc(n * sizeof(int)); nb = malloc(n * sizeof(int *));
    for (int i = 0; i < n; i++) {
        if (fscanf(g, "%d", &deg[i]) != 1) return 1;
        nb[i] = malloc(deg[i] * sizeof(int));
        for (int j = 0; j < deg[i]; j++) if (fscanf(g, "%d", &nb[i][j]) != 1) return 1;
    }
    fclose(g);
    double secs = atof(argv[2]);
    rs ^= (unsigned long long)atoll(argv[3]) * 0x9E3779B97F4A7C15ULL;
    for (int i = 0; i < 20; i++) rnd();
    const char *outf = argv[4], *startf = 0; long target = LONG_MAX;
    for (int a = 5; a + 1 < argc; a += 2) {
        if (!strcmp(argv[a], "-i")) startf = argv[a + 1];
        else if (!strcmp(argv[a], "-t")) target = atol(argv[a + 1]);
        else if (!strcmp(argv[a], "-m")) mode = atoi(argv[a + 1]);
        else if (!strcmp(argv[a], "-g")) gam = atof(argv[a + 1]);
        else if (!strcmp(argv[a], "-r")) rho = atof(argv[a + 1]);
        else if (!strcmp(argv[a], "-c")) use_cc = atoi(argv[a + 1]);
        else if (!strcmp(argv[a], "-T")) tt = atoi(argv[a + 1]);
    }
    w = malloc(n * sizeof(int)); nbT = calloc(n, sizeof(int)); inT = calloc(n, sizeof(int));
    Tl = malloc(n * sizeof(int)); pos = malloc(n * sizeof(int)); viol = malloc(n * sizeof(int));
    conf = malloc(n * sizeof(int)); A1 = calloc(n, sizeof(long)); R2 = calloc(n, sizeof(long));
    age = calloc(n, sizeof(long)); tabuUntil = calloc(n, sizeof(long));
    for (int v = 0; v < n; v++) { w[v] = 1; conf[v] = 1; }
    Wsum = n; k = 0; f = 0; it = 0;
    if (startf) {
        FILE *st = fopen(startf, "r"); int m, v;
        if (st && fscanf(st, "%d", &m) == 1) while (fscanf(st, "%d", &v) == 1) if (!inT[v]) addv(v);
        if (st) fclose(st);
    }
    {   /* greedy fill with zero-cost additions in random order */
        int *perm = malloc(n * sizeof(int));
        for (int i = 0; i < n; i++) perm[i] = i;
        for (int i = n - 1; i > 0; i--) { int j = rnd() % (i + 1); int t = perm[i]; perm[i] = perm[j]; perm[j] = t; }
        if (f == 0) for (int i = 0; i < n; i++) { int v = perm[i]; if (!inT[v] && rise(v) == 0) addv(v); }
        free(perm);
    }
    long best = 0;
    if (f == 0) { best = k; save(outf); }
    clock_t t0 = clock();
    long nbump = 0, nforget = 0, lastimp = 0;
    while (1) {
        it++;
        if ((it & 1023) == 0 && (double)(clock() - t0) / CLOCKS_PER_SEC > secs) break;
        if (f == 0) {
            if (k > best) {
                best = k; save(outf); lastimp = it;
                fprintf(stderr, "size %ld at it %ld, %.1f s\n", best, it, (double)(clock() - t0) / CLOCKS_PER_SEC);
                if (best >= target) break;
            }
            int u = pick_add(0);
            addv(u); age[u] = it; tabuRem = u;
            for (int j = 0; j < deg[u]; j++) conf[nb[u][j]] = 1;
            continue;
        }
        long f0 = f;
        int x = pick_remove();
        remv(x); age[x] = it;
        if (use_cc) conf[x] = 0; else tabuUntil[x] = it + tt;
        for (int j = 0; j < deg[x]; j++) conf[nb[x][j]] = 1;
        int y = pick_add(1);
        addv(y); age[y] = it; tabuRem = y;
        for (int j = 0; j < deg[y]; j++) conf[nb[y][j]] = 1;
        if (f >= f0) {                    /* stall: no improving swap */
            bump(); nbump++;
            if ((double)Wsum > gam * n) { forget(); nforget++; }
        }
    }
    /* consistency check of the incremental bookkeeping */
    long fi = f; rebuild();
    if (fi != f) fprintf(stderr, "INTERNAL: penalty drift %ld vs %ld\n", fi, f);
    printf("best %ld  (iterations %ld, %.1f s, bumps %ld, forgets %ld, mean weight %.2f)\n", best, it,
           (double)(clock() - t0) / CLOCKS_PER_SEC, nbump, nforget, (double)Wsum / n);
    (void)lastimp;
    return 0;
}
