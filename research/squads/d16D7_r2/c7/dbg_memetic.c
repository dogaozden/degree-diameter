/* memetic.c: card c7 (wildcard) of squad d16D7_r2.
 * Memetic search for a maximum independent set of an orbit graph (format of og_pts.txt / og_lines.txt).
 * Population of P independent sets. Offspring = vertices common to two random parents, completed by random
 * greedy insertion, then an ARW-style iterated local search of fixed length: (1,2)-swaps driven by a dirty queue,
 * perturbation by forced insertion of a 1-tight vertex (oldest of 4 samples), undo log for rejected steps.
 * Replacement is crowding: the child replaces its most similar member if that member is not larger; identical
 * sets are dropped. CPU budget is measured with clock(). Every improvement of the global best is written at once.
 * usage: memetic GRAPH OUT_SOL CPU_SEC SEED [INIT_ITERS GEN_ITERS POP SEED_SOL]
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <limits.h>
#include <time.h>

static int n, W, maxdeg;
static int *off, *adj, *Lbuf;
static uint64_t *bits;
static uint64_t rs = 88172645463325252ULL;
static long long gIt = 0;
static double P_T1 = 0.9;   /* probability that a perturbation picks a 1-tight vertex */
static long RESTART = 3000; /* ILS restarts from its best after this many non-improving steps */
static int DBG = 0;

static inline uint64_t rnd64(void) {
    rs ^= rs >> 12; rs ^= rs << 25; rs ^= rs >> 27;
    return rs * 2685821657736338717ULL;
}
static inline int rndint(int k) { return (int)((rnd64() >> 33) % (uint64_t)k); }
static inline double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }
static inline int isadj(int u, int v) { return (int)((bits[(size_t)u * W + (v >> 6)] >> (v & 63)) & 1ULL); }
static double cpu(void) { return (double)clock() / CLOCKS_PER_SEC; }

static void *xmalloc(size_t b) { void *p = malloc(b ? b : 1); if (!p) { fprintf(stderr, "out of memory\n"); exit(1); } return p; }
static void *xcalloc(size_t c, size_t b) { void *p = calloc(c ? c : 1, b ? b : 1); if (!p) { fprintf(stderr, "out of memory\n"); exit(1); } return p; }

/* ---------- search state: independent set S, tightness = number of S-neighbours ---------- */
typedef struct {
    unsigned char *in, *inq;
    int *tight, *sumS;          /* sumS[u] = sum of ids of S-neighbours of u (= the S-neighbour when tight==1) */
    int *sol, sz, *spos;        /* S as a list */
    int *fre, nf, *fpos;        /* free list: not in S and tight 0 */
    int *t1, nt, *t1pos;        /* 1-tight list: not in S and tight 1 */
    int *q, qh, qt;             /* queue of S-vertices whose (1,2)-swap neighbourhood may have changed */
    long long *age;             /* iteration of last change (perturbation tie-break) */
    int *ulog;                  /* undo log: (v<<1)|isInsert */
    long nlog, logcap;
    int logon, logover;
} St;

static St *st_new(void) {
    St *s = xcalloc(1, sizeof(St));
    s->in = xcalloc(n, 1); s->inq = xcalloc(n, 1);
    s->tight = xcalloc(n, sizeof(int)); s->sumS = xcalloc(n, sizeof(int));
    s->sol = xmalloc(n * sizeof(int)); s->spos = xmalloc(n * sizeof(int));
    s->fre = xmalloc(n * sizeof(int)); s->fpos = xmalloc(n * sizeof(int));
    s->t1 = xmalloc(n * sizeof(int)); s->t1pos = xmalloc(n * sizeof(int));
    s->q = xmalloc((n + 1) * sizeof(int));
    s->age = xcalloc(n, sizeof(long long));
    s->logcap = 1L << 20; s->ulog = xmalloc(s->logcap * sizeof(int));
    return s;
}

static void st_clear(St *s) {
    memset(s->in, 0, n); memset(s->inq, 0, n);
    memset(s->tight, 0, n * sizeof(int)); memset(s->sumS, 0, n * sizeof(int));
    s->sz = 0;
    for (int i = 0; i < n; i++) { s->fre[i] = i; s->fpos[i] = i; }
    s->nf = n;
    memset(s->t1pos, 0xff, n * sizeof(int)); s->nt = 0;
    s->qh = s->qt = 0;
    s->nlog = 0; s->logon = 0; s->logover = 0;
}

static inline void fl_add(St *s, int v) { s->fpos[v] = s->nf; s->fre[s->nf++] = v; }
static inline void fl_del(St *s, int v) {
    int p = s->fpos[v], w = s->fre[--s->nf];
    s->fre[p] = w; s->fpos[w] = p; s->fpos[v] = -1;
}
static inline void t1_add(St *s, int v) { s->t1pos[v] = s->nt; s->t1[s->nt++] = v; }
static inline void t1_del(St *s, int v) {
    int p = s->t1pos[v], w = s->t1[--s->nt];
    s->t1[p] = w; s->t1pos[w] = p; s->t1pos[v] = -1;
}
static inline void q_push(St *s, int x) {
    if (s->inq[x]) return;
    s->inq[x] = 1; s->q[s->qt] = x; if (++s->qt == n + 1) s->qt = 0;
}
static inline int q_pop(St *s) {
    int x = s->q[s->qh]; if (++s->qh == n + 1) s->qh = 0; s->inq[x] = 0; return x;
}
#define Q_EMPTY(s) ((s)->qh == (s)->qt)
static inline void logop(St *s, int v, int ins) {
    if (!s->logon) return;
    if (s->nlog >= s->logcap) { s->logover = 1; return; }
    s->ulog[s->nlog++] = (v << 1) | ins;
}

/* v must be free (not in S, tight 0) */
static void st_insert(St *s, int v) {
    fl_del(s, v);
    s->in[v] = 1; s->spos[v] = s->sz; s->sol[s->sz++] = v;
    logop(s, v, 1);
    for (int k = off[v]; k < off[v + 1]; k++) {
        int u = adj[k], t = s->tight[u];
        if (t == 0) { fl_del(s, u); t1_add(s, u); q_push(s, v); }   /* u becomes 1-tight, its S-neighbour is v */
        else if (t == 1) t1_del(s, u);
        s->tight[u] = t + 1; s->sumS[u] += v;
    }
    q_push(s, v);
}

/* v must be in S */
static void st_remove(St *s, int v) {
    int p = s->spos[v], w = s->sol[--s->sz];
    s->sol[p] = w; s->spos[w] = p; s->spos[v] = -1;
    s->in[v] = 0;
    logop(s, v, 0);
    fl_add(s, v);                       /* v has no S-neighbour, so it is free */
    for (int k = off[v]; k < off[v + 1]; k++) {
        int u = adj[k], t = s->tight[u];
        s->tight[u] = t - 1; s->sumS[u] -= v;
        if (t == 1) { t1_del(s, u); fl_add(s, u); }
        else if (t == 2) { t1_add(s, u); q_push(s, s->sumS[u]); }  /* remaining S-neighbour gains a candidate */
    }
}

static void ls_fill(St *s) {
    while (s->nf > 0) st_insert(s, s->fre[rndint(s->nf)]);
}

/* (1,2)-swap around x: x out, two non-adjacent 1-tight neighbours of x in */
static int try_swap(St *s, int x) {
    int nl = 0;
    for (int k = off[x]; k < off[x + 1]; k++) { int u = adj[k]; if (s->tight[u] == 1) Lbuf[nl++] = u; }
    if (nl < 2) return 0;
    int r = rndint(nl);
    for (int i = 0; i < nl; i++) {
        int a = Lbuf[(i + r) % nl];
        for (int j = i + 1; j < nl; j++) {
            int b = Lbuf[(j + r) % nl];
            if (!isadj(a, b)) { st_remove(s, x); st_insert(s, a); st_insert(s, b); return 1; }
        }
    }
    return 0;
}

static void local_search(St *s) {
    ls_fill(s);
    while (!Q_EMPTY(s)) {
        int x = q_pop(s);
        if (s->in[x] && try_swap(s, x)) ls_fill(s);
    }
}

static void perturb(St *s) {
    int v = -1;
    long long ba = LLONG_MAX;
    if (s->nt > 0 && rnd01() < P_T1) {
        for (int c = 0; c < 4; c++) {
            int cand = s->t1[rndint(s->nt)];
            if (s->age[cand] < ba) { ba = s->age[cand]; v = cand; }
        }
    } else {
        int bt = INT_MAX;
        for (int c = 0; c < 4; c++) {
            int cand;
            do { cand = rndint(n); } while (s->in[cand]);
            if (s->tight[cand] < bt || (s->tight[cand] == bt && s->age[cand] < ba)) {
                bt = s->tight[cand]; ba = s->age[cand]; v = cand;
            }
        }
    }
    for (int k = off[v]; k < off[v + 1]; k++) {
        int u = adj[k];
        if (s->in[u]) { st_remove(s, u); s->age[u] = gIt; }
    }
    st_insert(s, v);
    s->age[v] = gIt;
}

static void undo(St *s) {
    s->logon = 0;
    for (long i = s->nlog - 1; i >= 0; i--) {
        int e = s->ulog[i], v = e >> 1;
        if (e & 1) st_remove(s, v); else st_insert(s, v);
    }
    s->nlog = 0;
    while (!Q_EMPTY(s)) q_pop(s);
}

/* DEBUG: full invariant check of the state (tight, sumS, free and 1-tight lists, independence) */
static void check_state(St *s, const char *where) {
    int *tt = xcalloc(n, sizeof(int));
    int cnt = 0;
    for (int v = 0; v < n; v++) if (s->in[v]) {
        cnt++;
        if (s->sol[s->spos[v]] != v) { fprintf(stderr, "%s: spos broken %d\n", where, v); exit(3); }
        for (int k = off[v]; k < off[v + 1]; k++) {
            int u = adj[k];
            if (s->in[u]) { fprintf(stderr, "%s: S not independent %d %d\n", where, v, u); exit(3); }
            tt[u]++;
        }
    }
    if (cnt != s->sz) { fprintf(stderr, "%s: sz mismatch %d %d\n", where, cnt, s->sz); exit(3); }
    int nf = 0, nt = 0;
    for (int v = 0; v < n; v++) {
        if (tt[v] != s->tight[v]) { fprintf(stderr, "%s: tight v=%d %d vs %d\n", where, v, tt[v], s->tight[v]); exit(3); }
        int ss = 0;
        for (int k = off[v]; k < off[v + 1]; k++) if (s->in[adj[k]]) ss += adj[k];
        if (ss != s->sumS[v]) { fprintf(stderr, "%s: sumS v=%d\n", where, v); exit(3); }
        int isfree = !s->in[v] && tt[v] == 0, ist1 = !s->in[v] && tt[v] == 1;
        if (isfree) { nf++; if (s->fpos[v] < 0 || s->fre[s->fpos[v]] != v) { fprintf(stderr, "%s: F list v=%d\n", where, v); exit(3); } }
        else if (s->fpos[v] != -1) { fprintf(stderr, "%s: F stale v=%d\n", where, v); exit(3); }
        if (ist1) { nt++; if (s->t1pos[v] < 0 || s->t1[s->t1pos[v]] != v) { fprintf(stderr, "%s: T1 list v=%d\n", where, v); exit(3); } }
        else if (s->t1pos[v] != -1) { fprintf(stderr, "%s: T1 stale v=%d\n", where, v); exit(3); }
    }
    if (nf != s->nf || nt != s->nt) { fprintf(stderr, "%s: list sizes nf %d/%d nt %d/%d\n", where, nf, s->nf, nt, s->nt); exit(3); }
    if (!Q_EMPTY(s)) { fprintf(stderr, "%s: queue not empty\n", where); exit(3); }
    free(tt);
}

/* DEBUG: local optimality: no free vertex and no (1,2)-swap */
static void check_opt(St *s, const char *where) {
    if (s->nf) { fprintf(stderr, "%s: free vertices left\n", where); exit(3); }
    for (int x = 0; x < n; x++) {
        if (!s->in[x]) continue;
        int nl = 0; int L[4096];
        for (int k = off[x]; k < off[x + 1]; k++) if (s->tight[adj[k]] == 1) L[nl++] = adj[k];
        for (int i = 0; i < nl; i++) for (int j = i + 1; j < nl; j++)
            if (!isadj(L[i], L[j])) { fprintf(stderr, "%s: missed (1,2)-swap at %d\n", where, x); exit(3); }
    }
}

/* ARW-style ILS for `iters` perturbation steps from the state s. Returns the best size; the best set goes to best. */
static int ils(St *s, long iters, int *best, int *bsz_out) {
    local_search(s);
    int bsz = s->sz;
    memcpy(best, s->sol, bsz * sizeof(int));
    long since = 0;
    for (long it = 0; it < iters; it++) {
        gIt++;
        int before = s->sz;
        s->nlog = 0; s->logover = 0; s->logon = 1;
        perturb(s);
        local_search(s);
        s->logon = 0;
        int ns = s->sz;
        if (ns > bsz) { bsz = ns; memcpy(best, s->sol, ns * sizeof(int)); since = 0; }
        else since++;
        int acc = 1;
        if (ns < before && !s->logover) {
            double p = 1.0 / (1.0 + (double)(before - ns) * (double)(bsz - ns));
            acc = rnd01() < p;
        }
        if (!acc) undo(s);
        if (DBG) { check_state(s, "after step"); check_opt(s, "after step"); }
        if (since > RESTART) {
            st_clear(s);
            for (int i = 0; i < bsz; i++) st_insert(s, best[i]);
            local_search(s);
            since = 0;
        }
    }
    *bsz_out = bsz;
    return bsz;
}

/* ---------- global best, checks, I/O ---------- */
static int *chkmark, chkstamp = 0;
static int gsz = 0, *gbest;
static const char *outpath;

static int is_indep(const int *sol, int sz) {
    chkstamp++;
    for (int i = 0; i < sz; i++) {
        if (sol[i] < 0 || sol[i] >= n || chkmark[sol[i]] == chkstamp) return 0;
        chkmark[sol[i]] = chkstamp;
    }
    for (int i = 0; i < sz; i++)
        for (int j = i + 1; j < sz; j++)
            if (isadj(sol[i], sol[j])) return 0;
    return 1;
}

static void offer_global(const int *sol, int sz) {
    if (sz <= gsz) return;
    if (!is_indep(sol, sz)) { fprintf(stderr, "BUG: dependent set rejected\n"); return; }
    gsz = sz; memcpy(gbest, sol, sz * sizeof(int));
    char tmp[4096];
    snprintf(tmp, sizeof tmp, "%s.tmp", outpath);
    FILE *g = fopen(tmp, "w");
    if (!g) return;
    for (int i = 0; i < sz; i++) fprintf(g, "%d\n", sol[i]);
    fclose(g);
    rename(tmp, outpath);
    fprintf(stderr, "[%.1f s cpu] new best %d\n", cpu(), gsz);
}

static int load_sol(const char *path, int *out) {
    FILE *g = fopen(path, "r");
    if (!g) return -1;
    int c = 0; char line[256];
    while (fgets(line, sizeof line, g)) {
        if (line[0] == '#' || line[0] == '\n') continue;
        int v;
        if (sscanf(line, "%d", &v) == 1 && v >= 0 && v < n && c < n) out[c++] = v;
    }
    fclose(g);
    return c;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s GRAPH OUT_SOL CPU_SEC SEED [INIT_ITERS GEN_ITERS POP SEED_SOL]\n", argv[0]);
        return 1;
    }
    const char *gf = argv[1];
    outpath = argv[2];
    double budget = atof(argv[3]);
    uint64_t sd = strtoull(argv[4], NULL, 10);
    rs = (0x9E3779B97F4A7C15ULL * (sd + 1)) ^ 0xD1B54A32D192ED03ULL;
    if (!rs) rs = 1;
    long init_iters = argc > 5 ? atol(argv[5]) : 20000;
    long gen_iters = argc > 6 ? atol(argv[6]) : 3000;
    int P = argc > 7 ? atoi(argv[7]) : 10;
    const char *seedf = argc > 8 ? argv[8] : NULL;
    if (P < 2) P = 2;
    DBG = getenv("MEMDBG") != NULL;

    /* ---- load graph, symmetrize, build bitset and CSR ---- */
    FILE *f = fopen(gf, "r");
    if (!f) { perror(gf); return 1; }
    int M, E;
    if (fscanf(f, "%d %d", &M, &E) != 2) { fprintf(stderr, "bad header\n"); return 1; }
    n = M; W = (n + 63) / 64;
    bits = xcalloc((size_t)n * W, sizeof(uint64_t));
    int **nb = xmalloc(n * sizeof(int *));
    int *dg = xcalloc(n, sizeof(int));
    for (int i = 0; i < n; i++) {
        int idx, rep, d;
        if (fscanf(f, "%d %d %d", &idx, &rep, &d) != 3 || idx < 0 || idx >= n || d < 0) {
            fprintf(stderr, "bad vertex line %d\n", i); return 1;
        }
        nb[idx] = xmalloc((d + 1) * sizeof(int)); dg[idx] = d;
        for (int k = 0; k < d; k++)
            if (fscanf(f, "%d", &nb[idx][k]) != 1) { fprintf(stderr, "bad neighbour\n"); return 1; }
    }
    fclose(f);
    for (int v = 0; v < n; v++)
        for (int k = 0; k < dg[v]; k++) {
            int u = nb[v][k];
            if (u < 0 || u >= n || u == v) continue;
            bits[(size_t)v * W + (u >> 6)] |= 1ULL << (u & 63);
            bits[(size_t)u * W + (v >> 6)] |= 1ULL << (v & 63);
        }
    off = xmalloc((n + 1) * sizeof(int));
    long tot = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += __builtin_popcountll(bits[(size_t)v * W + w]);
        off[v] = (int)tot; tot += c;
        if (c > maxdeg) maxdeg = c;
    }
    off[n] = (int)tot;
    adj = xmalloc((size_t)tot * sizeof(int));
    for (int v = 0; v < n; v++) {
        int k = off[v];
        for (int w = 0; w < W; w++) {
            uint64_t x = bits[(size_t)v * W + w];
            while (x) { adj[k++] = w * 64 + __builtin_ctzll(x); x &= x - 1; }
        }
    }
    Lbuf = xmalloc(maxdeg * sizeof(int));
    chkmark = xcalloc(n, sizeof(int));
    gbest = xmalloc(n * sizeof(int));
    fprintf(stderr, "graph n=%d edges=%ld (file E=%d) maxdeg=%d P=%d init=%ld gen=%ld\n",
            n, tot / 2, E, maxdeg, P, init_iters, gen_iters);

    /* ---- population ---- */
    St *s = st_new();
    int **pop = xmalloc(P * sizeof(int *));
    int *psz = xcalloc(P, sizeof(int));
    for (int i = 0; i < P; i++) pop[i] = xmalloc(n * sizeof(int));
    int *child = xmalloc(n * sizeof(int));
    int csz = 0;
    int *mark = xcalloc(n, sizeof(int));
    int stamp = 0;

    int start = 0;
    if (seedf) {
        int c0 = load_sol(seedf, child);
        if (c0 > 0 && is_indep(child, c0)) {
            st_clear(s);
            for (int i = 0; i < c0; i++) st_insert(s, child[i]);
            ils(s, init_iters, pop[0], &psz[0]);
            offer_global(pop[0], psz[0]);
            start = 1;
        } else {
            fprintf(stderr, "seed file ignored (missing or not independent)\n");
        }
    }
    for (int i = start; i < P && cpu() < budget; i++) {
        st_clear(s);
        ils(s, init_iters, pop[i], &psz[i]);
        offer_global(pop[i], psz[i]);
    }
    fprintf(stderr, "[%.1f s cpu] initial population done\n", cpu());

    /* ---- generations: common-core crossover + ILS, crowding replacement ---- */
    long long gens = 0;
    double next_report = 10.0;
    while (cpu() < budget) {
        int a = rndint(P), b = rndint(P - 1);
        if (b >= a) b++;
        stamp++;
        for (int i = 0; i < psz[b]; i++) mark[pop[b][i]] = stamp;
        st_clear(s);
        for (int i = 0; i < psz[a]; i++) {
            int v = pop[a][i];
            if (mark[v] == stamp) st_insert(s, v);
        }
        ils(s, gen_iters, child, &csz);
        offer_global(child, csz);

        stamp++;
        for (int i = 0; i < csz; i++) mark[child[i]] = stamp;
        int dup = 0, bj = -1, bov = -1;
        for (int j = 0; j < P; j++) {
            int ov = 0;
            for (int i = 0; i < psz[j]; i++) if (mark[pop[j][i]] == stamp) ov++;
            if (ov == csz && psz[j] == csz) { dup = 1; break; }
            if (psz[j] <= csz && ov > bov) { bov = ov; bj = j; }
        }
        if (!dup && bj >= 0) { memcpy(pop[bj], child, csz * sizeof(int)); psz[bj] = csz; }
        gens++;
        if (cpu() >= next_report) {
            int mn = INT_MAX, mx = 0;
            for (int j = 0; j < P; j++) { if (psz[j] < mn) mn = psz[j]; if (psz[j] > mx) mx = psz[j]; }
            fprintf(stderr, "[%.0f s] gens=%lld ils_steps=%lld best=%d pop=[%d..%d] child=%d\n",
                    cpu(), gens, gIt, gsz, mn, mx, csz);
            next_report += 10.0;
        }
    }
    printf("BEST %d gens=%lld ils_steps=%lld cpu=%.1f\n", gsz, gens, gIt, cpu());
    return 0;
}
