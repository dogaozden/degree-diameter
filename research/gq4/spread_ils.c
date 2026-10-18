/* Iterated local search for maximum independent set, after Andrade, Resende and Werneck (2012).
 * Local search: (1,2)-swaps, i.e. drop one chosen vertex and add two of its 1-tight neighbours that are not adjacent,
 * then greedily fill every free vertex. Perturbation: force in 1 to 3 outside vertices (dropping their chosen
 * neighbours). Acceptance: a worse solution is kept with probability 1/(1 + d*d*), where d is the drop from the
 * current size and d* the drop from the best size. Rejected moves are undone from a log.
 *
 * usage: spread_ils graph.txt seconds seed out.txt
 * graph.txt: "n m", then m lines "u v" (0-based, undirected).
 * stdout: one line per improvement, then BEST, PERTURBS, SWAPS and RATE (perturbations per second).
 * out.txt: the best size on the first line, then the chosen vertices, one per line.
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

static int n;
static uint8_t *A;                   /* adjacency matrix */
static int *off, *adj;               /* CSR adjacency lists */
static int *inS, *tight, *xr;        /* in solution; number of chosen neighbours; xor of their ids */
static long *lastMove;               /* iteration of the last change, for choosing perturbation vertices */
static char *inQ, *inFree;
static int *queue, qHead, qTail, qCap;
static int *freeStack, freeTop;
static int *lbuf;
static int *logv;                    /* undo log: 2*v for a removal of v, 2*v+1 for an insertion of v */
static long logTop, logCap;
static int size, undoing, logOn;
static long iter, swaps;
static uint64_t rs;

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + 1e-9 * ts.tv_nsec;
}

static void die(const char *msg) {
    fprintf(stderr, "%s\n", msg);
    exit(1);
}

static void enqueue(int x) {
    if (undoing || inQ[x]) return;
    inQ[x] = 1;
    queue[qTail] = x;
    qTail = (qTail + 1) % qCap;
}

static void push_free(int u) {
    if (inFree[u]) return;
    inFree[u] = 1;
    freeStack[freeTop++] = u;
}

static void log_op(int code) {
    if (!logOn) return;
    if (logTop == logCap) {
        logCap = logCap ? 2 * logCap : 1 << 16;
        logv = realloc(logv, logCap * sizeof(int));
        if (!logv) die("out of memory in undo log");
    }
    logv[logTop++] = code;
}

static void insert_v(int v) {
    int i, u;
    inS[v] = 1;
    size++;
    lastMove[v] = iter;
    log_op(2 * v + 1);
    for (i = off[v]; i < off[v + 1]; i++) {
        u = adj[i];
        if (++tight[u] == 1) enqueue(v); /* u joined the 1-tight neighbourhood of v */
        xr[u] ^= v;
    }
    enqueue(v);
}

static void remove_v(int v) {
    int i, u;
    inS[v] = 0;
    size--;
    lastMove[v] = iter;
    log_op(2 * v);
    for (i = off[v]; i < off[v + 1]; i++) {
        u = adj[i];
        xr[u] ^= v;
        if (--tight[u] == 0)
            push_free(u);
        else if (tight[u] == 1)
            enqueue(xr[u]); /* the chosen neighbour of u now has a new 1-tight neighbour */
    }
    push_free(v); /* v has no chosen neighbour, since the solution is independent */
}

static void greedy(void) {
    while (freeTop > 0) {
        int u = freeStack[--freeTop];
        inFree[u] = 0;
        if (!inS[u] && tight[u] == 0) insert_v(u);
    }
}

static void local_search(void) {
    int x, i, j, u, nl, a, b;
    greedy();
    while (qHead != qTail) {
        x = queue[qHead];
        qHead = (qHead + 1) % qCap;
        inQ[x] = 0;
        if (!inS[x]) continue;
        nl = 0;
        for (i = off[x]; i < off[x + 1]; i++) {
            u = adj[i];
            if (tight[u] == 1) lbuf[nl++] = u;
        }
        if (nl < 2) continue;
        for (i = nl - 1; i > 0; i--) { /* random order, so swaps vary */
            j = rndint(i + 1);
            u = lbuf[i];
            lbuf[i] = lbuf[j];
            lbuf[j] = u;
        }
        a = -1;
        for (i = 0; i < nl && a < 0; i++)
            for (j = i + 1; j < nl; j++)
                if (!A[(size_t)lbuf[i] * n + lbuf[j]]) {
                    a = lbuf[i];
                    b = lbuf[j];
                    break;
                }
        if (a < 0) continue;
        remove_v(x);
        insert_v(a);
        insert_v(b);
        swaps++;
        greedy();
    }
}

#ifndef SAMPLES
#define SAMPLES 3
#endif

static void perturb(int k) {
    int t, c, v, pick, u, i;
    for (t = 0; t < k; t++) {
        pick = -1;
        for (c = 0; c < SAMPLES; c++) { /* few random outside vertices: least tight, then changed longest ago */
            do {
                v = rndint(n);
            } while (inS[v]);
            if (pick < 0 || tight[v] < tight[pick] || (tight[v] == tight[pick] && lastMove[v] < lastMove[pick]))
                pick = v;
        }
        v = pick;
        for (i = off[v]; i < off[v + 1]; i++) {
            u = adj[i];
            if (inS[u]) remove_v(u);
        }
        insert_v(v);
    }
}

static void record_best(double t0, long perturbs, int *bestSet, int *bestSize) {
    int i, k = 0;
    *bestSize = size;
    for (i = 0; i < n; i++)
        if (inS[i]) bestSet[k++] = i;
    printf("t=%.2f size=%d perturbs=%ld\n", now() - t0, *bestSize, perturbs);
    fflush(stdout);
}

static void undo(void) {
    long i;
    undoing = 1;
    logOn = 0;
    for (i = logTop - 1; i >= 0; i--) {
        int code = logv[i], v = code >> 1;
        if (code & 1)
            remove_v(v);
        else
            insert_v(v);
    }
    undoing = 0;
    logOn = 1;
    logTop = 0;
}

int main(int argc, char **argv) {
    FILE *f, *o;
    int m, mE = 0, *eu, *ev, *pos, *perm, *bestSet, bestSize, k, d, ds, cur, ns;
    int i, u, v;
    long perturbs = 0;
    double secs, t0, tEnd, p, elapsed;

    if (argc != 5) die("usage: spread_ils graph.txt seconds seed out.txt");
    f = fopen(argv[1], "r");
    if (!f) die("cannot open graph file");
    if (fscanf(f, "%d %d", &n, &m) != 2) die("bad graph header");
    secs = atof(argv[2]);
    rs = 88172645463325252ULL ^ (2654435761ULL * (uint64_t)strtoull(argv[3], NULL, 10));
    if (rs == 0) rs = 1;
    for (i = 0; i < 10; i++) rnd();

    A = calloc((size_t)n * n, 1);
    eu = malloc(sizeof(int) * (m + 1));
    ev = malloc(sizeof(int) * (m + 1));
    off = calloc(n + 1, sizeof(int));
    if (!A || !eu || !ev || !off) die("out of memory");
    for (i = 0; i < m; i++) {
        if (fscanf(f, "%d %d", &u, &v) != 2) die("bad edge line");
        if (u == v || A[(size_t)u * n + v]) continue; /* ignore loops and repeats */
        A[(size_t)u * n + v] = A[(size_t)v * n + u] = 1;
        eu[mE] = u;
        ev[mE] = v;
        mE++;
        off[u + 1]++;
        off[v + 1]++;
    }
    fclose(f);
    for (i = 0; i < n; i++) off[i + 1] += off[i];
    adj = malloc(sizeof(int) * (2 * (size_t)mE + 1));
    pos = malloc(sizeof(int) * (n + 1));
    memcpy(pos, off, sizeof(int) * n);
    for (i = 0; i < mE; i++) {
        adj[pos[eu[i]]++] = ev[i];
        adj[pos[ev[i]]++] = eu[i];
    }
    free(eu);
    free(ev);
    free(pos);

    inS = calloc(n, sizeof(int));
    tight = calloc(n, sizeof(int));
    xr = calloc(n, sizeof(int));
    lastMove = calloc(n, sizeof(long));
    inQ = calloc(n, 1);
    inFree = calloc(n, 1);
    queue = malloc(sizeof(int) * (n + 1));
    qCap = n + 1;
    freeStack = malloc(sizeof(int) * (n + 1));
    lbuf = malloc(sizeof(int) * (n + 1));
    bestSet = malloc(sizeof(int) * (n + 1));
    perm = malloc(sizeof(int) * (n + 1));
    if (!inS || !tight || !xr || !lastMove || !inQ || !inFree || !queue || !freeStack || !lbuf || !bestSet || !perm)
        die("out of memory");

    t0 = now();
    tEnd = t0 + secs;
    for (i = 0; i < n; i++) perm[i] = i;
    for (i = n - 1; i > 0; i--) {
        k = rndint(i + 1);
        u = perm[i];
        perm[i] = perm[k];
        perm[k] = u;
    }
    for (i = 0; i < n; i++)
        if (!inS[perm[i]] && tight[perm[i]] == 0) insert_v(perm[i]);
    local_search();

    bestSize = -1;
    record_best(t0, perturbs, bestSet, &bestSize);
    cur = size;
    logOn = 1;
    logTop = 0;

    while (now() < tEnd) {
        perturbs++;
        iter++;
        logTop = 0;
        perturb(1 + rndint(3));
        local_search();
        ns = size;
        if (ns >= cur) {
            cur = ns;
            if (cur > bestSize) record_best(t0, perturbs, bestSet, &bestSize);
        } else {
            d = cur - ns;
            ds = bestSize - ns;
            p = 1.0 / (1.0 + (double)d * ds);
            if ((double)(rnd() % 1000000000ULL) / 1e9 < p)
                cur = ns;
            else
                undo();
        }
    }
    elapsed = now() - t0;

    o = fopen(argv[4], "w");
    if (!o) die("cannot open output file");
    fprintf(o, "%d\n", bestSize);
    for (k = 0; k < bestSize; k++) fprintf(o, "%d\n", bestSet[k]);
    fclose(o);

    printf("BEST %d\nPERTURBS %ld\nSWAPS %ld\nSECONDS %.2f\nRATE %.0f\n", bestSize, perturbs, swaps, elapsed,
           perturbs / elapsed);
    return 0;
}
