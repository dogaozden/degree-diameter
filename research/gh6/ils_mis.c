/* ils_mis.c: iterated local search for a maximum independent set (ARW style: (1,2)-swaps, forced
 * insertion of a random outside vertex, undo log, accept a worse solution with probability 1/(1+d*d*)).
 *
 * Usage: ils_mis graph.txt seconds seed > result.txt
 * graph.txt: "n m" then m lines "u v" (0-based, simple undirected graph).
 * stdout: the best size, then the best vertex ids on one line. Progress goes to stderr.
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

static int n, words;
static int *off, *nb;   /* CSR adjacency */
static uint64_t *bits;  /* adjacency bit matrix, row u at bits + u*words */
static int *in_sol, *tight, *last, *Lbuf, *Rbuf;
static int sol_size;
static long iter;
static int *undo;
static long undo_n, undo_cap;
static int logging;
static int *stk;
static long stk_n;
static char *inq;
static uint64_t rs = 88172645463325252ULL;

static inline uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static inline int adjq(int u, int v) {
    return (int)((bits[(size_t)u * words + (v >> 6)] >> (v & 63)) & 1u);
}
static double now(void) {
    struct timespec t;
    clock_gettime(CLOCK_MONOTONIC, &t);
    return t.tv_sec + 1e-9 * t.tv_nsec;
}
static void log_op(int code) {
    if (!logging) return;
    if (undo_n == undo_cap) {
        undo_cap *= 2;
        undo = realloc(undo, undo_cap * sizeof *undo);
        if (!undo) abort();
    }
    undo[undo_n++] = code;
}
static void add_v(int v) {
    in_sol[v] = 1;
    sol_size++;
    last[v] = (int)iter;
    for (int k = off[v]; k < off[v + 1]; k++) tight[nb[k]]++;
    log_op(v);
}
static void rem_v(int v) {
    in_sol[v] = 0;
    sol_size--;
    last[v] = (int)iter;
    for (int k = off[v]; k < off[v + 1]; k++) tight[nb[k]]--;
    log_op(-v - 1);
}
static void push(int v) {
    if (!inq[v]) {
        inq[v] = 1;
        stk[stk_n++] = v;
    }
}
/* Queue the solution vertices within distance 2 of c: only they can gain a (1,2)-swap after c changed. */
static void push_around(int c) {
    if (in_sol[c]) push(c);
    for (int k = off[c]; k < off[c + 1]; k++) {
        int u = nb[k];
        for (int k2 = off[u]; k2 < off[u + 1]; k2++) {
            int y = nb[k2];
            if (in_sol[y]) push(y);
        }
    }
}
/* Apply (1,2)-swaps around queued solution vertices until none is left. */
static void improve(void) {
    while (stk_n > 0) {
        int x = stk[--stk_n];
        inq[x] = 0;
        if (!in_sol[x]) continue;
        int cnt = 0;
        for (int k = off[x]; k < off[x + 1]; k++) {
            int u = nb[k];
            if (!in_sol[u] && tight[u] == 1) Lbuf[cnt++] = u;
        }
        if (cnt < 2) continue;
        for (int i = cnt - 1; i > 0; i--) { /* shuffle candidates */
            int j = (int)(rnd() % (uint64_t)(i + 1));
            int t = Lbuf[i];
            Lbuf[i] = Lbuf[j];
            Lbuf[j] = t;
        }
        int a = -1, b = -1;
        for (int i = 0; i < cnt && a < 0; i++)
            for (int j = i + 1; j < cnt; j++)
                if (!adjq(Lbuf[i], Lbuf[j])) {
                    a = Lbuf[i];
                    b = Lbuf[j];
                    break;
                }
        if (a < 0) continue;
        rem_v(x);
        add_v(a);
        add_v(b);
        push_around(x);
        push_around(a);
        push_around(b);
        for (int k = off[x]; k < off[x + 1]; k++) {
            int u = nb[k];
            if (!in_sol[u] && tight[u] == 0) {
                add_v(u);
                push_around(u);
            }
        }
    }
}
/* Force v into the solution, dropping its solution neighbours, then refill and repair. */
static void perturb(int v) {
    int nr = 0;
    for (int k = off[v]; k < off[v + 1]; k++) {
        int u = nb[k];
        if (in_sol[u]) {
            rem_v(u);
            Rbuf[nr++] = u;
        }
    }
    add_v(v);
    push_around(v);
    for (int i = 0; i < nr; i++) {
        int u = Rbuf[i];
        for (int k = off[u]; k < off[u + 1]; k++) {
            int w = nb[k];
            if (!in_sol[w] && tight[w] == 0) {
                add_v(w);
                push_around(w);
            }
        }
    }
    improve();
}
static void undo_all(void) {
    int saved = logging;
    logging = 0;
    for (long i = undo_n - 1; i >= 0; i--) {
        int c = undo[i];
        if (c >= 0) rem_v(c);
        else add_v(-c - 1);
    }
    logging = saved;
    undo_n = 0;
}

int main(int argc, char **argv) {
    if (argc < 4) {
        fprintf(stderr, "usage: ils_mis graph.txt seconds seed\n");
        return 2;
    }
    FILE *f = fopen(argv[1], "r");
    if (!f) {
        perror("graph");
        return 1;
    }
    int m;
    if (fscanf(f, "%d %d", &n, &m) != 2) return 1;
    int *eu = malloc(sizeof(int) * (size_t)(m + 1)), *ev = malloc(sizeof(int) * (size_t)(m + 1));
    for (int i = 0; i < m; i++)
        if (fscanf(f, "%d %d", &eu[i], &ev[i]) != 2) return 1;
    fclose(f);
    words = (n + 63) / 64;
    bits = calloc((size_t)n * words, sizeof *bits);
    int *deg = calloc(n, sizeof *deg);
    for (int i = 0; i < m; i++) {
        int u = eu[i], v = ev[i];
        if (u == v || adjq(u, v)) continue;
        bits[(size_t)u * words + (v >> 6)] |= 1ULL << (v & 63);
        bits[(size_t)v * words + (u >> 6)] |= 1ULL << (u & 63);
        deg[u]++;
        deg[v]++;
    }
    off = malloc(sizeof(int) * (size_t)(n + 1));
    off[0] = 0;
    for (int v = 0; v < n; v++) off[v + 1] = off[v] + deg[v];
    nb = malloc(sizeof(int) * (size_t)(off[n] + 1));
    int *fill = calloc(n, sizeof *fill);
    for (int u = 0; u < n; u++)
        for (int v = 0; v < n; v++)
            if (adjq(u, v)) nb[off[u] + fill[u]++] = v;
    in_sol = calloc(n, sizeof *in_sol);
    tight = calloc(n, sizeof *tight);
    last = calloc(n, sizeof *last);
    Lbuf = malloc(sizeof(int) * (size_t)(n + 1));
    Rbuf = malloc(sizeof(int) * (size_t)(n + 1));
    stk = malloc(sizeof(int) * (size_t)(n + 1));
    inq = calloc(n, 1);
    undo_cap = 1 << 16;
    undo = malloc(sizeof(int) * (size_t)undo_cap);
    int *best_sol = calloc(n, sizeof *best_sol);
    double secs = atof(argv[2]);
    rs = (uint64_t)atoll(argv[3]) * 0x9E3779B97F4A7C15ULL + 12345;
    for (int i = 0; i < 10; i++) rnd();

    /* Randomized greedy start, then full repair. */
    int *perm = malloc(sizeof(int) * (size_t)n);
    for (int i = 0; i < n; i++) perm[i] = i;
    for (int i = n - 1; i > 0; i--) {
        int j = (int)(rnd() % (uint64_t)(i + 1));
        int t = perm[i];
        perm[i] = perm[j];
        perm[j] = t;
    }
    logging = 0;
    for (int i = 0; i < n; i++)
        if (!in_sol[perm[i]] && tight[perm[i]] == 0) add_v(perm[i]);
    for (int v = 0; v < n; v++)
        if (in_sol[v]) push(v);
    improve();
    int best = sol_size;
    memcpy(best_sol, in_sol, sizeof(int) * (size_t)n);
    logging = 1;
    undo_n = 0;

    double t0 = now(), t_report = t0;
    int prev = sol_size;
    long improvements = 0;
    iter = 0;
    while (1) {
        iter++;
        if ((iter & 1023) == 0) {
            double t = now();
            if (t - t0 > secs) break;
            if (t - t_report > 10.0) {
                fprintf(stderr, "t=%.0fs iters=%ld best=%d cur=%d\n", t - t0, iter, best, sol_size);
                t_report = t;
            }
        }
        if (sol_size >= n) break;
        undo_n = 0;
        /* Pick the least recently changed of 4 random outside vertices. */
        int v = -1;
        for (int t = 0; t < 4; t++) {
            int c;
            do c = (int)(rnd() % (uint64_t)n); while (in_sol[c]);
            if (v < 0 || last[c] < last[v]) v = c;
        }
        perturb(v);
        int cur = sol_size;
        if (cur > best) {
            best = cur;
            memcpy(best_sol, in_sol, sizeof(int) * (size_t)n);
            improvements++;
        }
        if (cur >= prev) {
            prev = cur;
        } else {
            long delta = prev - cur, dstar = best - cur;
            if ((long)(rnd() % 1000000ULL) < 1000000L / (1 + delta * dstar)) prev = cur;
            else undo_all();
        }
    }
    double secs_used = now() - t0;
    /* Verify the answer before printing it. */
    int count = 0;
    for (int v = 0; v < n; v++)
        if (best_sol[v]) {
            count++;
            for (int k = off[v]; k < off[v + 1]; k++)
                if (best_sol[nb[k]]) {
                    fprintf(stderr, "internal error: adjacent vertices in solution\n");
                    return 1;
                }
        }
    if (count != best) {
        fprintf(stderr, "internal error: count %d != best %d\n", count, best);
        return 1;
    }
    fprintf(stderr, "done: best=%d iters=%ld (%.0f iters/s) improvements=%ld time=%.1fs\n", best, iter,
            iter / secs_used, improvements, secs_used);
    printf("%d\n", best);
    for (int v = 0, first = 1; v < n; v++)
        if (best_sol[v]) {
            printf(first ? "%d" : " %d", v);
            first = 0;
        }
    printf("\n");
    return 0;
}
