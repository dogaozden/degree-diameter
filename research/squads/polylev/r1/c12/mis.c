/* mis.c: iterated local search for a maximum independent set in a D-regular graph (ARW-style:
 * (1,2)-swaps, random perturbation with k forced insertions, acceptance 1/(1+d*d*), undo log).
 * usage: mis ADJ.bin DIMS.bin SECONDS SEED OUT.txt [RESTART_ITERS]
 * ADJ.bin: int32 n x D neighbour lists (symmetric). DIMS.bin: int32 {n, L, D}.
 * OUT.txt: one vertex id per line for the best independent set found (written periodically and at the end). */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

static int n, D;
static int32_t *adj;
static unsigned char *inS, *inq;
static int32_t *tight;
static int32_t *sol, *solpos; static int nsol;
static int32_t *fre, *frepos; static int nfree;
static int64_t *age; static int64_t iter_no;
static int32_t *qbuf; static int qhead, qtail, qcnt;
static int32_t *ulog_v; static int8_t *ulog_op; static int64_t nlog, logcap;
static int logging;
static uint64_t rs;
static int32_t *mark; static int32_t stampc;

static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline int rndint(int m) { return (int)(rnd() % (uint64_t)m); }
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }

static void logop(int v, int op) {
    if (nlog == logcap) {
        logcap = logcap ? 2 * logcap : (1 << 20);
        ulog_v = realloc(ulog_v, logcap * sizeof(int32_t));
        ulog_op = realloc(ulog_op, logcap);
        if (!ulog_v || !ulog_op) { fprintf(stderr, "oom log\n"); exit(1); }
    }
    ulog_v[nlog] = v; ulog_op[nlog] = (int8_t)op; nlog++;
}
static void push(int v) { if (inq[v]) return; inq[v] = 1; qbuf[qtail] = v; qtail = (qtail + 1) % n; qcnt++; }
static int pop(void) { int v = qbuf[qhead]; qhead = (qhead + 1) % n; qcnt--; inq[v] = 0; return v; }
static void fset_add(int v) { frepos[v] = nfree; fre[nfree++] = v; }
static void fset_del(int v) { int p = frepos[v]; int last = fre[--nfree]; fre[p] = last; frepos[last] = p; frepos[v] = -1; }
static void sol_add(int v) { solpos[v] = nsol; sol[nsol++] = v; }
static void sol_del(int v) { int p = solpos[v]; int last = sol[--nsol]; sol[p] = last; solpos[last] = p; solpos[v] = -1; }
static inline int adjacent(int a, int b) {
    const int32_t *x = adj + (size_t)a * D;
    for (int i = 0; i < D; i++) if (x[i] == b) return 1;
    return 0;
}

/* v must be free (not in S, no S-neighbour) */
static void do_insert(int v) {
    inS[v] = 1;
    fset_del(v);
    sol_add(v);
    age[v] = iter_no;
    const int32_t *a = adj + (size_t)v * D;
    for (int i = 0; i < D; i++) {
        int u = a[i];
        if (tight[u] == 0 && !inS[u]) fset_del(u);
        tight[u]++;
    }
    push(v);
    if (logging) logop(v, 1);
}

/* v must be in S */
static void do_remove(int v) {
    inS[v] = 0;
    sol_del(v);
    age[v] = iter_no;
    const int32_t *a = adj + (size_t)v * D;
    for (int i = 0; i < D; i++) {
        int u = a[i];
        tight[u]--;
        if (!inS[u]) {
            if (tight[u] == 0) fset_add(u);
            else if (tight[u] == 1) {
                const int32_t *b = adj + (size_t)u * D;
                for (int j = 0; j < D; j++) if (inS[b[j]]) { push(b[j]); break; }
            }
        }
    }
    fset_add(v);
    if (logging) logop(v, -1);
}

/* (1,2)-swap around solution vertex x: remove x, insert two non-adjacent 1-tight neighbours */
static int try_swap(int x) {
    int L[256], m = 0;
    const int32_t *a = adj + (size_t)x * D;
    for (int i = 0; i < D; i++) { int u = a[i]; if (!inS[u] && tight[u] == 1) L[m++] = u; }
    if (m < 2) return 0;
    for (int i = m - 1; i > 0; i--) { int j = rndint(i + 1); int t = L[i]; L[i] = L[j]; L[j] = t; }
    for (int i = 0; i < m; i++) {
        stampc++;
        const int32_t *b = adj + (size_t)L[i] * D;
        for (int t = 0; t < D; t++) mark[b[t]] = stampc;
        for (int j = i + 1; j < m; j++)
            if (mark[L[j]] != stampc) {
                do_remove(x);
                do_insert(L[i]);
                do_insert(L[j]);
                return 1;
            }
    }
    return 0;
}

static void local_search(void) {
    for (;;) {
        while (nfree > 0) { int v = fre[rndint(nfree)]; do_insert(v); }
        if (qcnt == 0) break;
        int x = pop();
        if (!inS[x]) continue;
        try_swap(x);
    }
}

static void perturb(int k) {
    for (int t = 0; t < k; t++) {
        int best = -1;
        for (int s = 0; s < 4; s++) {
            int v = rndint(n);
            while (inS[v]) v = rndint(n);
            if (best < 0 || age[v] < age[best]) best = v;
        }
        int v = best;
        const int32_t *a = adj + (size_t)v * D;
        for (int i = 0; i < D; i++) if (inS[a[i]]) do_remove(a[i]);
        do_insert(v);
    }
}

static void drain_queue(void) { while (qcnt) pop(); }

static void undo(void) {
    int saved = logging;
    logging = 0;
    for (int64_t i = nlog - 1; i >= 0; i--) {
        int v = ulog_v[i];
        if (ulog_op[i] == 1) do_remove(v); else do_insert(v);
    }
    nlog = 0;
    drain_queue();
    logging = saved;
}

static void reset_state(void) {
    memset(inS, 0, n);
    memset(tight, 0, sizeof(int32_t) * n);
    memset(inq, 0, n);
    nsol = 0; nfree = 0; qhead = qtail = qcnt = 0;
    for (int v = 0; v < n; v++) fset_add(v);
}

static void load_solution(const int32_t *list, int cnt) {
    reset_state();
    int saved = logging; logging = 0;
    for (int i = 0; i < cnt; i++) do_insert(list[i]);
    logging = saved;
    drain_queue();
}

static void write_sol(const char *path, const int32_t *list, int cnt) {
    char tmp[4096];
    snprintf(tmp, sizeof tmp, "%s.tmp", path);
    FILE *f = fopen(tmp, "w");
    if (!f) { perror("open"); return; }
    for (int i = 0; i < cnt; i++) fprintf(f, "%d\n", list[i]);
    fclose(f);
    rename(tmp, path);
}

int main(int argc, char **argv) {
    if (argc < 6) { fprintf(stderr, "usage: mis ADJ.bin DIMS.bin SECONDS SEED OUT.txt [RESTART]\n"); return 1; }
    double secs = atof(argv[3]);
    uint64_t seed = strtoull(argv[4], NULL, 10);
    int64_t restart = argc > 6 ? atoll(argv[6]) : 0;
    int32_t dims[3];
    FILE *fd = fopen(argv[2], "rb");
    if (!fd || fread(dims, 4, 3, fd) != 3) { fprintf(stderr, "dims\n"); return 1; }
    fclose(fd);
    n = dims[0]; D = dims[2];
    adj = malloc((size_t)n * D * sizeof(int32_t));
    FILE *fa = fopen(argv[1], "rb");
    if (!fa || fread(adj, sizeof(int32_t), (size_t)n * D, fa) != (size_t)n * D) { fprintf(stderr, "adj\n"); return 1; }
    fclose(fa);
    inS = calloc(n, 1); inq = calloc(n, 1);
    tight = calloc(n, sizeof(int32_t));
    sol = malloc(n * sizeof(int32_t)); solpos = malloc(n * sizeof(int32_t));
    fre = malloc(n * sizeof(int32_t)); frepos = malloc(n * sizeof(int32_t));
    age = calloc(n, sizeof(int64_t));
    qbuf = malloc(n * sizeof(int32_t));
    mark = calloc(n, sizeof(int32_t)); stampc = 0;
    int32_t *best = malloc(n * sizeof(int32_t));
    rs = seed * 0x9E3779B97F4A7C15ULL + 88172645463325252ULL;
    for (int i = 0; i < 10; i++) rnd();

    reset_state();
    logging = 0;
    local_search();                       /* random greedy maximal set, then swaps */
    int bestn = nsol;
    memcpy(best, sol, nsol * sizeof(int32_t));
    write_sol(argv[5], best, bestn);
    int dirty = 0;
    double t0 = now(), lastsave = t0, lastprint = t0;
    int64_t lastImp = 0;
    fprintf(stderr, "init %d\n", bestn);

    for (;;) {
        if ((iter_no & 255) == 0) {
            double t = now();
            if (t - t0 > secs) break;
            if (dirty && t - lastsave > 2.0) { write_sol(argv[5], best, bestn); dirty = 0; lastsave = t; }
            if (t - lastprint > 10.0) { fprintf(stderr, "t=%.0f iter=%lld cur=%d best=%d\n", t - t0, (long long)iter_no, nsol, bestn); lastprint = t; }
        }
        iter_no++;
        logging = 1; nlog = 0;
        int before = nsol;
        int k = 1;
        while (k < 8 && (rnd() & 1)) k++;
        perturb(k);
        local_search();
        int after = nsol;
        int accept = 1;
        if (after < before) {
            int delta = before - after;
            int dstar = bestn - after;
            accept = (rnd() % (uint64_t)(1 + (uint64_t)delta * dstar)) == 0;
        }
        if (!accept) undo();
        logging = 0; nlog = 0;
        if (nsol > bestn) {
            bestn = nsol;
            memcpy(best, sol, nsol * sizeof(int32_t));
            lastImp = iter_no;
            dirty = 1;
        }
        if (restart > 0 && iter_no - lastImp > restart) {
            load_solution(best, bestn);
            lastImp = iter_no;
        }
    }
    write_sol(argv[5], best, bestn);
    fprintf(stderr, "final best %d after %lld iters\n", bestn, (long long)iter_no);
    printf("%d\n", bestn);
    return 0;
}
