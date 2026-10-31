/*
 * Z3 voltage lifts of the GQ(5,5) incidence graph (312 base vertices, 6-regular).
 * Lift has 936 vertices (w,h), h in Z3. Edge (a,b) with a<b carries voltage val[e]:
 * (a,g)-(b,g+val), traversing b->a subtracts it.
 *
 * Cost = sum over base u of uncovered(u), uncovered(u) = 936 - |ball_5((u,0))|.
 * ball_5((u,0)) = { (end(R), vol(R)) : R non-backtracking walk from u, length <= 5 }
 * (any walk reduces freely to an NB walk with the same endpoint and voltage).
 * Diameter 5 of the lift  <=>  cost == 0.
 *
 * Usage: lift_sa <edges.txt> <seed> <seconds> <out_voltages.txt> [T0] [T1]
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <time.h>

#define NB 312
#define DEG 6
#define NE 936
#define L 5
#define NL (NB * 3)

static int ea[NE], eb[NE];
static int nadj[NB];
static int adjv[NB][DEG], adje[NB][DEG], adjs[NB][DEG];
static int val[NE];
static int istree[NE];
static int freeedges[NE], nfree;
static int stampArr[NL];
static int curstamp = 0;
static int cnt;

static void dfs(int x, int prev, int depth, int vol)
{
    int key = x * 3 + vol;
    if (stampArr[key] != curstamp) {
        stampArr[key] = curstamp;
        cnt++;
    }
    if (depth == L)
        return;
    for (int i = 0; i < DEG; i++) {
        int y = adjv[x][i];
        if (y == prev)
            continue;
        int e = adje[x][i];
        int dv = (adjs[x][i] > 0) ? val[e] : (3 - val[e]) % 3;
        dfs(y, x, depth + 1, (vol + dv) % 3);
    }
}

static long cost_total(int *uncov_out)
{
    long total = 0;
    for (int u = 0; u < NB; u++) {
        curstamp = u + 1;
        cnt = 0;
        dfs(u, -1, 0, 0);
        int unc = NL - cnt;
        if (uncov_out)
            uncov_out[u] = unc;
        total += unc;
    }
    return total;
}

static unsigned long long rng_state;
static unsigned long long rng(void)
{
    rng_state ^= rng_state << 13;
    rng_state ^= rng_state >> 7;
    rng_state ^= rng_state << 17;
    return rng_state;
}
static double urand(void) { return (rng() >> 11) * (1.0 / 9007199254740992.0); }

int main(int argc, char **argv)
{
    if (argc < 5) {
        fprintf(stderr, "usage: %s edges.txt seed seconds out.txt [T0] [T1]\n", argv[0]);
        return 1;
    }
    FILE *f = fopen(argv[1], "r");
    if (!f) { perror("edges"); return 1; }
    int n, m;
    if (fscanf(f, "%d %d", &n, &m) != 2 || n != NB || m != NE) { fprintf(stderr, "bad header\n"); return 1; }
    for (int e = 0; e < NE; e++) {
        if (fscanf(f, "%d %d", &ea[e], &eb[e]) != 2) { fprintf(stderr, "bad edge\n"); return 1; }
    }
    fclose(f);
    for (int e = 0; e < NE; e++) {
        int a = ea[e], b = eb[e];
        adjv[a][nadj[a]] = b; adje[a][nadj[a]] = e; adjs[a][nadj[a]] = +1; nadj[a]++;
        adjv[b][nadj[b]] = a; adje[b][nadj[b]] = e; adjs[b][nadj[b]] = -1; nadj[b]++;
    }
    for (int v = 0; v < NB; v++)
        if (nadj[v] != DEG) { fprintf(stderr, "degree\n"); return 1; }

    /* spanning tree from 0 (BFS): tree edges get voltage 0 (gauge) */
    int queue[NB], qh = 0, qt = 0, seenv[NB];
    memset(seenv, 0, sizeof seenv);
    memset(istree, 0, sizeof istree);
    queue[qt++] = 0; seenv[0] = 1;
    while (qh < qt) {
        int x = queue[qh++];
        for (int i = 0; i < DEG; i++) {
            int y = adjv[x][i];
            if (!seenv[y]) { seenv[y] = 1; istree[adje[x][i]] = 1; queue[qt++] = y; }
        }
    }
    nfree = 0;
    for (int e = 0; e < NE; e++)
        if (!istree[e]) freeedges[nfree++] = e;

    rng_state = 88172645463325252ULL ^ (unsigned long long)atoll(argv[2]) * 2654435761ULL;
    double secs = atof(argv[3]);
    double T0 = argc > 5 ? atof(argv[5]) : 30.0;
    double T1 = argc > 6 ? atof(argv[6]) : 0.5;

    for (int e = 0; e < NE; e++) val[e] = istree[e] ? 0 : (int)(rng() % 3);

    long cur = cost_total(NULL);
    long best = cur;
    int bestval[NE];
    memcpy(bestval, val, sizeof val);
    printf("initial cost (sum over 312 sources) = %ld, forced floor = 312*74 = %d\n", cur, 312 * 74);
    fflush(stdout);

    clock_t t0 = clock();
    long it = 0;
    double elapsed = 0.0;
    while (1) {
        it++;
        if ((it & 15) == 0) {
            elapsed = (double)(clock() - t0) / CLOCKS_PER_SEC;
            if (elapsed > secs) break;
        }
        double frac = elapsed / secs;
        double T = T0 * pow(T1 / T0, frac);
        int e = freeedges[rng() % nfree];
        int old = val[e];
        int nv = (old + 1 + (int)(rng() % 2)) % 3;
        val[e] = nv;
        long c = cost_total(NULL);
        if (c <= cur || urand() < exp(-(double)(c - cur) / T)) {
            cur = c;
            if (cur < best) {
                best = cur;
                memcpy(bestval, val, sizeof val);
            }
        } else {
            val[e] = old;
        }
        if (it % 500 == 0) {
            printf("it=%ld t=%.0fs T=%.2f cur=%ld best=%ld\n", it, elapsed, T, cur, best);
            fflush(stdout);
        }
    }
    printf("done: iterations=%ld best=%ld\n", it, best);

    memcpy(val, bestval, sizeof val);
    int unc[NB];
    long chk = cost_total(unc);
    printf("recheck best=%ld\n", chk);
    int umin = 1 << 30, umax = 0;
    for (int u = 0; u < NB; u++) { if (unc[u] < umin) umin = unc[u]; if (unc[u] > umax) umax = unc[u]; }
    printf("per-source uncovered: min=%d max=%d\n", umin, umax);

    FILE *g = fopen(argv[4], "w");
    if (!g) { perror("out"); return 1; }
    fprintf(g, "%ld\n", best);
    for (int e = 0; e < NE; e++) fprintf(g, "%d %d %d %d\n", ea[e], eb[e], bestval[e], istree[e]);
    fclose(g);
    return 0;
}
