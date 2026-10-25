/* symils.c -- card c5 (squad d16D7_r2): h-symmetric quotient search, then unrestricted ILS polish.
 * usage: symils og.txt q.txt T1 T2 seed sym_out.txt best_out.txt
 *   og.txt : orbit graph "M E" then "idx rep deg nbrs..." per vertex (og_pts.txt / og_lines.txt)
 *   q.txt  : h-quotient "NQ EQ" then per quotient vertex "w k members.. d nbrs..." (written by prep.py)
 * Phase 1: weighted ILS on the quotient (weight 3 per 3-cycle of P, 1 per P-fixed vertex), CPU budget T1 s.
 *          The best quotient solution is lifted to orbit-graph vertices and written to sym_out.txt.
 * Phase 2: unit-weight ILS on the orbit graph started from the lifted set, CPU budget T2 s; best -> best_out.txt.
 * ILS: (omega,1) and (1,2)-swap local search with incremental tightness; perturbation = force-insert of a
 * non-solution vertex (min tightness among 4 samples, oldest first); undo log for rejected moves (ARW-style
 * acceptance: worse solutions kept with probability 1/(1+d*d*)).
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

typedef uint64_t u64;

static u64 rs = 0x9E3779B97F4A7C15ULL;
static inline u64 rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline int rndint(int n) { return (int)(rnd() % (u64)n); }
static double cpu(void) { return (double)clock() / CLOCKS_PER_SEC; }

typedef struct {
    int n, WD;
    int *w, *deg, **adj;
    u64 *bits;
} Graph;

static Graph *new_graph(int n) {
    Graph *G = malloc(sizeof *G);
    G->n = n; G->WD = (n + 63) / 64;
    G->w = calloc(n, sizeof(int)); G->deg = calloc(n, sizeof(int));
    G->adj = calloc(n, sizeof(int *)); G->bits = calloc((size_t)n * G->WD, sizeof(u64));
    return G;
}
static inline int isadj(const Graph *G, int a, int b) {
    return (int)((G->bits[(size_t)a * G->WD + (b >> 6)] >> (b & 63)) & 1u);
}
static void build_bits(Graph *G) {
    for (int v = 0; v < G->n; v++)
        for (int j = 0; j < G->deg[v]; j++) {
            int u = G->adj[v][j];
            G->bits[(size_t)v * G->WD + (u >> 6)] |= (u64)1 << (u & 63);
        }
}
static int readint(FILE *f) {
    int x;
    if (fscanf(f, "%d", &x) != 1) { fprintf(stderr, "input read error\n"); exit(1); }
    return x;
}
static Graph *read_og(const char *fn) {
    FILE *f = fopen(fn, "r");
    if (!f) { perror(fn); exit(1); }
    int M = readint(f), E = readint(f);
    (void)E;
    Graph *G = new_graph(M);
    for (int i = 0; i < M; i++) {
        int idx = readint(f);
        (void)readint(f);
        int d = readint(f);
        G->w[idx] = 1; G->deg[idx] = d; G->adj[idx] = malloc(sizeof(int) * (d > 0 ? d : 1));
        for (int j = 0; j < d; j++) G->adj[idx][j] = readint(f);
    }
    fclose(f);
    build_bits(G);
    return G;
}
static Graph *read_q(const char *fn, int ***mem_out, int **nmem_out) {
    FILE *f = fopen(fn, "r");
    if (!f) { perror(fn); exit(1); }
    int NQ = readint(f), EQ = readint(f);
    (void)EQ;
    Graph *G = new_graph(NQ);
    int **mem = malloc(sizeof(int *) * NQ), *nmem = malloc(sizeof(int) * NQ);
    for (int i = 0; i < NQ; i++) {
        G->w[i] = readint(f);
        int k = readint(f);
        nmem[i] = k; mem[i] = malloc(sizeof(int) * k);
        for (int j = 0; j < k; j++) mem[i][j] = readint(f);
        int d = readint(f);
        G->deg[i] = d; G->adj[i] = malloc(sizeof(int) * (d > 0 ? d : 1));
        for (int j = 0; j < d; j++) G->adj[i][j] = readint(f);
    }
    fclose(f);
    build_bits(G);
    *mem_out = mem; *nmem_out = nmem;
    return G;
}

/* ---------------- ILS state ---------------- */
typedef struct {
    Graph *G;
    int n;
    char *inS, *inq;
    int *tight, *nbw, *sumS;      /* #S-neighbours, weight of S-neighbours, sum of ids of S-neighbours */
    int *sol, *pos, ns;           /* solution list */
    int W;                        /* solution weight */
    int *q, qh, qt, qcnt;         /* queue of vertices to examine */
    long *age; long it;           /* last-change stamps */
    int *logv, *logt; long nlog, logcap; int logging;
    int *lbuf;
} ILS;

static ILS *ils_new(Graph *G) {
    ILS *S = calloc(1, sizeof *S);
    int n = G->n;
    S->G = G; S->n = n;
    S->inS = calloc(n, 1); S->inq = calloc(n, 1);
    S->tight = calloc(n, sizeof(int)); S->nbw = calloc(n, sizeof(int)); S->sumS = calloc(n, sizeof(int));
    S->sol = malloc(sizeof(int) * n); S->pos = malloc(sizeof(int) * n);
    S->q = malloc(sizeof(int) * n); S->age = calloc(n, sizeof(long)); S->lbuf = malloc(sizeof(int) * n);
    return S;
}
static inline void qpush(ILS *S, int v) {
    if (S->inq[v]) return;
    S->inq[v] = 1;
    S->q[S->qt] = v;
    S->qt = (S->qt + 1 == S->n) ? 0 : S->qt + 1;
    S->qcnt++;
}
static inline int qpop(ILS *S) {
    int v = S->q[S->qh];
    S->qh = (S->qh + 1 == S->n) ? 0 : S->qh + 1;
    S->qcnt--; S->inq[v] = 0;
    return v;
}
static void raw_add(ILS *S, int v) {
    Graph *G = S->G;
    const int wv = G->w[v];
    S->inS[v] = 1; S->pos[v] = S->ns; S->sol[S->ns++] = v;
    S->W += wv;
    for (int j = 0; j < G->deg[v]; j++) {
        int u = G->adj[v][j];
        S->tight[u]++; S->nbw[u] += wv; S->sumS[u] += v;
    }
    qpush(S, v);
}
static void raw_remove(ILS *S, int v) {
    Graph *G = S->G;
    const int wv = G->w[v];
    S->inS[v] = 0;
    int p = S->pos[v], last = S->sol[--S->ns];
    S->sol[p] = last; S->pos[last] = p;
    S->W -= wv;
    for (int j = 0; j < G->deg[v]; j++) {
        int u = G->adj[v][j];
        S->tight[u]--; S->nbw[u] -= wv; S->sumS[u] -= v;
        if (!S->inS[u]) {
            if (S->tight[u] == 0) qpush(S, u);
            else if (S->tight[u] == 1) qpush(S, S->sumS[u]);
            if (G->w[u] > S->nbw[u]) qpush(S, u);
        }
    }
}
static void log_op(ILS *S, int v, int t) {
    if (S->nlog == S->logcap) {
        S->logcap = S->logcap * 2 + 4096;
        S->logv = realloc(S->logv, sizeof(int) * S->logcap);
        S->logt = realloc(S->logt, sizeof(int) * S->logcap);
    }
    S->logv[S->nlog] = v; S->logt[S->nlog] = t; S->nlog++;
}
static void op_add(ILS *S, int v) {
    raw_add(S, v); S->age[v] = S->it;
    if (S->logging) log_op(S, v, 0);
}
static void op_remove(ILS *S, int v) {
    raw_remove(S, v); S->age[v] = S->it;
    if (S->logging) log_op(S, v, 1);
}
static void undo(ILS *S) {
    for (long i = S->nlog - 1; i >= 0; i--) {
        if (S->logt[i] == 0) raw_remove(S, S->logv[i]);
        else raw_add(S, S->logv[i]);
    }
    S->nlog = 0;
    while (S->qcnt) qpop(S);
}
/* insert non-solution v, removing its solution neighbours */
static void force_insert(ILS *S, int v) {
    Graph *G = S->G;
    for (int j = 0; j < G->deg[v]; j++) {
        int u = G->adj[v][j];
        if (S->inS[u]) op_remove(S, u);
    }
    op_add(S, v);
}
/* (1,2)-type swap around solution vertex x: x out, two non-adjacent 1-tight neighbours in (weight must grow) */
static void try12(ILS *S, int x) {
    Graph *G = S->G;
    int nl = 0, *L = S->lbuf;
    for (int j = 0; j < G->deg[x]; j++) {
        int u = G->adj[x][j];
        if (!S->inS[u] && S->tight[u] == 1) L[nl++] = u;
    }
    if (nl < 2) return;
    int bsum = G->w[x], ba = -1, bb = -1;
    for (int i = 0; i < nl; i++) {
        int a = L[i];
        for (int k = i + 1; k < nl; k++) {
            int b = L[k];
            int s = G->w[a] + G->w[b];
            if (s > bsum && !isadj(G, a, b)) { bsum = s; ba = a; bb = b; }
        }
    }
    if (ba >= 0) { op_remove(S, x); op_add(S, ba); op_add(S, bb); }
}
static void process_queue(ILS *S) {
    while (S->qcnt > 0) {
        int v = qpop(S);
        if (!S->inS[v]) {
            if (S->tight[v] == 0) op_add(S, v);
            else if (S->G->w[v] > S->nbw[v]) force_insert(S, v);
        } else {
            try12(S, v);
        }
    }
}
static void save_best(ILS *S, int *best, int *bestn) {
    *bestn = S->ns;
    memcpy(best, S->sol, sizeof(int) * S->ns);
}
static int ils_run(ILS *S, double tlim, int *best, int *bestn, const char *tag) {
    int Wcur = S->W, Wbest = S->W;
    save_best(S, best, bestn);
    double t0 = cpu();
    long it = 0;
    S->logging = 1;
    fprintf(stderr, "[%s] start W=%d\n", tag, Wbest);
    while (1) {
        if ((it & 127) == 0 && cpu() - t0 >= tlim) break;
        it++; S->it = it; S->nlog = 0;
        int k = 1;
        if (rndint(20) == 0) k = 2 + rndint(3);
        for (int t = 0; t < k; t++) {
            int bv = -1;
            for (int s = 0; s < 4; s++) {
                int v;
                do { v = rndint(S->n); } while (S->inS[v]);
                if (bv < 0 || S->tight[v] < S->tight[bv] ||
                    (S->tight[v] == S->tight[bv] && S->age[v] < S->age[bv])) bv = v;
            }
            force_insert(S, bv);
        }
        process_queue(S);
        int Wn = S->W, acc;
        if (Wn >= Wcur) acc = 1;
        else {
            double d = (double)(Wcur - Wn), db = (double)(Wbest - Wn);
            double p = 1.0 / (1.0 + d * db);
            acc = ((double)(rnd() >> 11) * (1.0 / 9007199254740992.0)) < p;
        }
        if (acc) {
            Wcur = Wn;
            if (Wcur > Wbest) {
                Wbest = Wcur; save_best(S, best, bestn);
                fprintf(stderr, "[%s] t=%.2f it=%ld W=%d n=%d\n", tag, cpu() - t0, it, Wbest, *bestn);
            }
        } else {
            undo(S);
        }
    }
    S->logging = 0; S->nlog = 0;
    fprintf(stderr, "[%s] done it=%ld best W=%d cpu=%.2f\n", tag, it, Wbest, cpu() - t0);
    return Wbest;
}
static int independent(const Graph *G, const int *s, int ns) {
    for (int i = 0; i < ns; i++)
        for (int j = i + 1; j < ns; j++)
            if (isadj(G, s[i], s[j]) || s[i] == s[j]) return 0;
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 8) { fprintf(stderr, "usage: symils og.txt q.txt T1 T2 seed sym_out.txt best_out.txt\n"); return 1; }
    double T1 = atof(argv[3]), T2 = atof(argv[4]);
    rs ^= (u64)atoll(argv[5]) * 0x2545F4914F6CDD1DULL + 1;
    for (int i = 0; i < 10; i++) rnd();
    Graph *Og = read_og(argv[1]);
    int **mem, *nmem;
    Graph *Gq = read_q(argv[2], &mem, &nmem);
    fprintf(stderr, "loaded orbit graph n=%d, quotient n=%d\n", Og->n, Gq->n);

    /* phase 1: quotient */
    ILS *Sq = ils_new(Gq);
    for (int v = 0; v < Gq->n; v++) qpush(Sq, v);
    process_queue(Sq);
    int *bq = malloc(sizeof(int) * Gq->n), nbq = 0;
    int Wq = ils_run(Sq, T1, bq, &nbq, "quot");
    int *lift = malloc(sizeof(int) * Og->n), nl = 0;
    for (int i = 0; i < nbq; i++)
        for (int j = 0; j < nmem[bq[i]]; j++) lift[nl++] = mem[bq[i]][j];
    int okl = independent(Og, lift, nl);
    fprintf(stderr, "lifted symmetric set: %d orbit vertices (quotient weight %d), independent=%d\n", nl, Wq, okl);
    if (!okl) { fprintf(stderr, "lift not independent: bug\n"); return 2; }
    FILE *fo = fopen(argv[6], "w");
    for (int i = 0; i < nl; i++) fprintf(fo, "%d\n", lift[i]);
    fclose(fo);

    /* phase 2: unrestricted ILS on the orbit graph from the lifted set */
    ILS *So = ils_new(Og);
    for (int i = 0; i < nl; i++) op_add(So, lift[i]);
    for (int v = 0; v < Og->n; v++) qpush(So, v);
    process_queue(So);
    int *bo = malloc(sizeof(int) * Og->n), nbo = 0;
    int Wo = ils_run(So, T2, bo, &nbo, "orbit");
    int oko = independent(Og, bo, nbo);
    fprintf(stderr, "final: sym=%d best=%d independent=%d cpu=%.2f\n", nl, Wo, oko, cpu());
    if (!oko) { fprintf(stderr, "final set not independent: bug\n"); return 3; }
    fo = fopen(argv[7], "w");
    for (int i = 0; i < nbo; i++) fprintf(fo, "%d\n", bo[i]);
    fclose(fo);
    printf("sym=%d best=%d\n", nl, Wo);
    return 0;
}
