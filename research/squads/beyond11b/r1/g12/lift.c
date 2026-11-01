/* Z_m voltage-lift annealer. Usage: lift BASE m D secs seed T0 T1 OUT
   BASE: "V0 n0 NE" then NE edges "u v" (u < n0 <= v). Spanning tree (BFS from 0) gets voltage 0.
   Cost = sum over base sources s of (#lift vertices not within distance D of (s,0)); BFS from (s,0) suffices
   since Z_m acts on fibres. Writes OUT (edge list "n" then "u v") and OUT.volt on cost 0; always OUT.best.
   Memory: O(V0*m). Single thread. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <time.h>
static int V0, n0, NE, M, D, DEG;
static int *eu, *ev, *volt, *isfree, *posu, *posv;
static int *nbr, *shf, *deg;
static unsigned *vis; static unsigned stamp = 0;
static int *q, *qv, *qi;
static double rnd(void) { return drand48(); }
static long cost_eval_lim(long lim) {
    long N = (long)V0 * M, total = 0;
    for (int s = 0; s < V0; s++) {
        stamp++;
        int head = 0, tail = 0, start = s * M;
        vis[start] = stamp; q[tail] = start; qv[tail] = s; qi[tail] = 0; tail++;
        for (int lev = 0; lev < D && head < tail; lev++) {
            int end = tail;
            while (head < end) {
                int v = qv[head], i = qi[head]; head++;
                int *nb = nbr + v * DEG, *sh = shf + v * DEG;
                for (int k = 0; k < deg[v]; k++) {
                    int j = i + sh[k]; if (j >= M) j -= M;
                    int w = nb[k];
                    int y = w * M + j;
                    if (vis[y] != stamp) { vis[y] = stamp; qv[tail] = w; qi[tail] = j; tail++; }
                }
            }
        }
        total += N - tail;
        if (total > lim) return total; /* early reject: exact Metropolis via pre-drawn threshold */
    }
    return total;
}
static long cost_eval(void) { return cost_eval_lim(1L << 60); }
static void set_volt(int e, int x) {
    volt[e] = x;
    shf[eu[e] * DEG + posu[e]] = x;
    shf[ev[e] * DEG + posv[e]] = (M - x) % M;
}
static void write_lift(const char *out) {
    char fn[512]; long N = (long)V0 * M;
    FILE *f = fopen(out, "w"); fprintf(f, "%ld\n", N);
    for (int e = 0; e < NE; e++) for (int i = 0; i < M; i++)
        fprintf(f, "%d %d\n", eu[e] * M + i, ev[e] * M + (i + volt[e]) % M);
    fclose(f);
    snprintf(fn, sizeof fn, "%s.volt", out); f = fopen(fn, "w");
    for (int e = 0; e < NE; e++) fprintf(f, "%d %d %d\n", eu[e], ev[e], volt[e]);
    fclose(f);
}
int main(int argc, char **argv) {
    if (argc < 9) { fprintf(stderr, "usage: lift BASE m D secs seed T0 T1 OUT [INIT.volt]\n"); return 1; }
    FILE *f = fopen(argv[1], "r");
    if (fscanf(f, "%d %d %d", &V0, &n0, &NE) != 3) return 2;
    eu = malloc(NE * sizeof(int)); ev = malloc(NE * sizeof(int));
    for (int e = 0; e < NE; e++) if (fscanf(f, "%d %d", &eu[e], &ev[e]) != 2) return 2;
    fclose(f);
    M = atoi(argv[2]); D = atoi(argv[3]); double secs = atof(argv[4]);
    srand48(atol(argv[5])); double T0 = atof(argv[6]), T1 = atof(argv[7]); const char *OUT = argv[8];
    /* degree bookkeeping */
    deg = calloc(V0, sizeof(int)); for (int e = 0; e < NE; e++) { deg[eu[e]]++; deg[ev[e]]++; }
    DEG = 0; for (int v = 0; v < V0; v++) if (deg[v] > DEG) DEG = deg[v];
    nbr = malloc(sizeof(int) * V0 * DEG); shf = malloc(sizeof(int) * V0 * DEG);
    memset(deg, 0, sizeof(int) * V0);
    posu = malloc(NE * sizeof(int)); posv = malloc(NE * sizeof(int));
    volt = calloc(NE, sizeof(int)); isfree = malloc(NE * sizeof(int));
    for (int e = 0; e < NE; e++) {
        int u = eu[e], v = ev[e];
        posu[e] = deg[u]; nbr[u * DEG + deg[u]++] = v;
        posv[e] = deg[v]; nbr[v * DEG + deg[v]++] = u;
    }
    /* spanning tree: BFS from 0, tree edges fixed to voltage 0 */
    int *seen = calloc(V0, sizeof(int)); int *bq = malloc(V0 * sizeof(int)); int bh = 0, bt = 0;
    seen[0] = 1; bq[bt++] = 0; int *intree = calloc(NE, sizeof(int));
    while (bh < bt) { int x = bq[bh++];
        for (int e = 0; e < NE; e++) {
            int y = -1;
            if (eu[e] == x) y = ev[e]; else if (ev[e] == x) y = eu[e];
            if (y >= 0 && !seen[y]) { seen[y] = 1; intree[e] = 1; bq[bt++] = y; }
        } }
    int nfree = 0; for (int e = 0; e < NE; e++) { isfree[e] = !intree[e]; nfree += isfree[e]; }
    /* all edges start at voltage 0 (set_volt fills shf) */
    for (int e = 0; e < NE; e++) set_volt(e, 0);
    if (argc >= 10) { /* init from file */
        FILE *g = fopen(argv[9], "r"); int a, b, x;
        while (g && fscanf(g, "%d %d %d", &a, &b, &x) == 3) for (int e = 0; e < NE; e++) if (eu[e] == a && ev[e] == b) set_volt(e, x);
        if (g) fclose(g);
    } else {
        for (int e = 0; e < NE; e++) if (isfree[e]) set_volt(e, (int)(rnd() * M) % M);
    }
    vis = calloc((size_t)V0 * M, sizeof(unsigned)); q = malloc(sizeof(int) * (size_t)V0 * M); qv = malloc(sizeof(int) * (size_t)V0 * M); qi = malloc(sizeof(int) * (size_t)V0 * M);
    long cur = cost_eval(), best = cur; int *bestv = malloc(NE * sizeof(int)); memcpy(bestv, volt, NE * sizeof(int));
    fprintf(stderr, "V0=%d n=%ld M=%d D=%d NE=%d free=%d DEG=%d start_cost=%ld mem~%ld KB\n", V0, (long)V0 * M, M, D, NE, nfree, DEG, cur, (long)(V0 * M * 8 / 1024));
    time_t t0 = time(NULL); long it = 0; double T = T0;
    int *freeidx = malloc(NE * sizeof(int)); int nf = 0; for (int e = 0; e < NE; e++) if (isfree[e]) freeidx[nf++] = e;
    while (cur > 0) {
        double el = difftime(time(NULL), t0); if (el >= secs) break;
        T = T0 * pow(T1 / T0, el / secs);
        int e = freeidx[(int)(rnd() * nf)]; int old = volt[e]; int nv;
        if (rnd() < 0.5) nv = (int)(rnd() * M) % M; else nv = (old + (rnd() < 0.5 ? 1 : M - 1)) % M;
        if (nv == old) continue;
        set_volt(e, nv);
        double u = rnd(); if (u < 1e-300) u = 1e-300;
        double thr = (double)cur - T * log(u); /* accept iff new cost <= thr */
        long lim = (long)floor(thr);
        long c = cost_eval_lim(lim);
        if (c <= lim) { cur = c; if (cur < best) { best = cur; memcpy(bestv, volt, NE * sizeof(int)); } }
        else set_volt(e, old);
        it++;
        if (it % 2000 == 0) fprintf(stderr, "it %ld t=%.0f cur=%ld best=%ld T=%.3f\n", it, el, cur, best, T);
    }
    fprintf(stderr, "done it=%ld cur=%ld best=%ld\n", it, cur, best);
    memcpy(volt, bestv, NE * sizeof(int));
    char fn[512]; snprintf(fn, sizeof fn, "%s.best", OUT);
    FILE *o = fopen(fn, "w"); fprintf(o, "%ld\n", best); fclose(o);
    { char fv[512]; snprintf(fv, sizeof fv, "%s.best.volt", OUT); FILE *w = fopen(fv, "w"); for (int e = 0; e < NE; e++) fprintf(w, "%d %d %d\n", eu[e], ev[e], bestv[e]); fclose(w); }
    if (best == 0) { write_lift(OUT); printf("SOLVED n=%ld M=%d D=%d out=%s\n", (long)V0 * M, M, D, OUT); }
    else printf("NOT_SOLVED best=%ld\n", best);
    return 0;
}
