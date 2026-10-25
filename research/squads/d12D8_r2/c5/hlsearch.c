/* hlsearch.c (card c5): local search on the Z_c voltages of the hub lift of a base graph.
   usage: hlsearch BASE c m iters seed nsample VOLT_IN|- VOLT_OUT
   BASE: first line "NB NE", then NE lines "p L" (base ids; edge e has voltage G[e]).
   Lift: copies (b,x) = b*c+x; hub (b,j) = NB*c + b*h + j with h = 2m, class r = j/2, neighbours (b,x), x = r mod m.
   Objective F = number of (source, target) pairs at lift distance > 8 (or unreachable), summed over the sample of
   sources. Sources (orbit representatives under the Z_c shift): copies (b,0) and hubs (b,0), (b,1) for every b.
   Move: re-draw one base-edge voltage; 70% of moves pick an edge on a lift path from a failing source to a far target.
   Accept if F does not increase. At F = 0 on the sample the full source set is checked. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

#define DMAX 8

static int NB, NE, c, m, h;
static int *EP, *EL, *G;
static int N, M;
static int *eu, *ev, *ee;
static int *st, *fillp, *adj, *adje;
static int *dist, *par, *pare, *qu;
static int *src, nsrc, *samp, nsamp, *failing, nfail;

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd64(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndint(int n) { return (int)(rnd64() % (uint64_t)n); }

static void build(void) {
    M = 0;
    for (int e = 0; e < NE; e++)
        for (int x = 0; x < c; x++) {
            eu[M] = EP[e] * c + x; ev[M] = EL[e] * c + (x + G[e]) % c; ee[M] = e; M++;
        }
    for (int b = 0; b < NB; b++)
        for (int j = 0; j < h; j++) {
            int hub = NB * c + b * h + j, r = j / 2;
            for (int x = r; x < c; x += m) { eu[M] = b * c + x; ev[M] = hub; ee[M] = -1; M++; }
        }
    memset(st, 0, (N + 1) * sizeof(int));
    for (int i = 0; i < M; i++) { st[eu[i] + 1]++; st[ev[i] + 1]++; }
    for (int i = 0; i < N; i++) st[i + 1] += st[i];
    memcpy(fillp, st, N * sizeof(int));
    for (int i = 0; i < M; i++) {
        int a = fillp[eu[i]]++; adj[a] = ev[i]; adje[a] = ee[i];
        int b2 = fillp[ev[i]]++; adj[b2] = eu[i]; adje[b2] = ee[i];
    }
}

/* BFS from s; returns number of far (dist > DMAX or unreached) vertices; fills dist/par/pare. */
static int bfs(int s) {
    for (int i = 0; i < N; i++) dist[i] = -1;
    int hd = 0, tl = 0;
    dist[s] = 0; par[s] = -1; pare[s] = -1; qu[tl++] = s;
    while (hd < tl) {
        int x = qu[hd++];
        for (int i = st[x]; i < st[x + 1]; i++) {
            int y = adj[i];
            if (dist[y] < 0) { dist[y] = dist[x] + 1; par[y] = x; pare[y] = adje[i]; qu[tl++] = y; }
        }
    }
    int far = 0;
    for (int i = 0; i < N; i++) if (dist[i] < 0 || dist[i] > DMAX) far++;
    return far;
}

/* objective over a list of sources; records failing sources */
static long evaluate(int *S, int ns, int record) {
    long F = 0;
    if (record) nfail = 0;
    for (int i = 0; i < ns; i++) {
        int f = bfs(S[i]);
        F += f;
        if (record && f > 0) failing[nfail++] = S[i];
    }
    return F;
}

static void class_report(void) {
    long cnt[2][2] = {{0, 0}, {0, 0}};   /* [source type][target type]; 0 = copy, 1 = hub */
    long far_total = 0;
    for (int i = 0; i < nsrc; i++) {
        int s = src[i];
        bfs(s);
        int st_type = (s >= NB * c) ? 1 : 0;
        for (int v = 0; v < N; v++)
            if (dist[v] < 0 || dist[v] > DMAX) {
                int tt = (v >= NB * c) ? 1 : 0;
                cnt[st_type][tt]++; far_total++;
            }
    }
    printf("FULL far_pairs=%ld  copy-copy=%ld copy-hub=%ld hub-copy=%ld hub-hub=%ld\n",
           far_total, cnt[0][0], cnt[0][1], cnt[1][0], cnt[1][1]);
    fflush(stdout);
}

int main(int argc, char **argv) {
    if (argc < 9) { fprintf(stderr, "usage: hlsearch BASE c m iters seed nsample VOLT_IN|- VOLT_OUT\n"); return 1; }
    FILE *f = fopen(argv[1], "r");
    if (!f || fscanf(f, "%d %d", &NB, &NE) != 2) { fprintf(stderr, "bad base\n"); return 1; }
    EP = malloc(NE * sizeof(int)); EL = malloc(NE * sizeof(int)); G = malloc(NE * sizeof(int));
    for (int e = 0; e < NE; e++) if (fscanf(f, "%d %d", &EP[e], &EL[e]) != 2) return 1;
    fclose(f);
    c = atoi(argv[2]); m = atoi(argv[3]);
    long iters = atol(argv[4]); uint64_t seed = strtoull(argv[5], NULL, 10);
    nsamp = atoi(argv[6]);
    h = 2 * m;
    rs ^= seed * 0x9E3779B97F4A7C15ULL + 1; for (int i = 0; i < 10; i++) rnd64();
    if (strcmp(argv[7], "-") == 0) {
        for (int e = 0; e < NE; e++) G[e] = rndint(c);
    } else {
        FILE *vf = fopen(argv[7], "r");
        for (int e = 0; e < NE; e++) if (fscanf(vf, "%d", &G[e]) != 1) return 1;
        fclose(vf);
    }
    N = NB * c + NB * h;
    int MAXM = NE * c + NB * 2 * c + 4;
    eu = malloc(MAXM * sizeof(int)); ev = malloc(MAXM * sizeof(int)); ee = malloc(MAXM * sizeof(int));
    st = malloc((N + 1) * sizeof(int)); fillp = malloc((N + 1) * sizeof(int));
    adj = malloc(2 * MAXM * sizeof(int)); adje = malloc(2 * MAXM * sizeof(int));
    dist = malloc(N * sizeof(int)); par = malloc(N * sizeof(int)); pare = malloc(N * sizeof(int));
    qu = malloc(N * sizeof(int));
    /* sources: copies (b,0), hubs (b,0) and (b,1) */
    nsrc = NB + 2 * NB;
    src = malloc(nsrc * sizeof(int));
    int t = 0;
    for (int b = 0; b < NB; b++) src[t++] = b * c;
    for (int b = 0; b < NB; b++) { src[t++] = NB * c + b * h; src[t++] = NB * c + b * h + 1; }
    /* random sample for the search */
    samp = malloc(nsrc * sizeof(int)); failing = malloc(nsrc * sizeof(int));
    int *perm = malloc(nsrc * sizeof(int));
    for (int i = 0; i < nsrc; i++) perm[i] = i;
    for (int i = nsrc - 1; i > 0; i--) { int j = rndint(i + 1); int tmp = perm[i]; perm[i] = perm[j]; perm[j] = tmp; }
    if (nsamp > nsrc || nsamp <= 0) nsamp = nsrc;
    for (int i = 0; i < nsamp; i++) samp[i] = src[perm[i]];

    build();
    long F = evaluate(samp, nsamp, 1);
    printf("init: sample=%d sources, F=%ld\n", nsamp, F); fflush(stdout);
    long acc = 0, it;
    for (it = 1; it <= iters; it++) {
        if (F == 0) {  /* sample clean: check all sources, widen the sample if needed */
            long Ff = evaluate(src, nsrc, 1);
            if (Ff == 0) break;
            memcpy(samp, src, nsrc * sizeof(int)); nsamp = nsrc; F = Ff;
            printf("it %ld: widened sample to all %d sources, F=%ld\n", it, nsrc, F); fflush(stdout);
        }
        int e = -1;
        if (nfail > 0 && rndint(10) < 7) {
            /* targeted: trace a shortest lift path from a failing source to a far vertex; take a base edge on it */
            int s = failing[rndint(nfail)];
            bfs(s);
            int cand[64], nc = 0;
            for (int v = 0; v < N && nc < 64; v++) if (dist[v] < 0 || dist[v] > DMAX) cand[nc++] = v;
            if (nc > 0) {
                int w = cand[rndint(nc)];
                if (dist[w] >= 0) {
                    int nb = 0, bases[256];
                    for (int x = w; x != s && nb < 256; x = par[x]) if (pare[x] >= 0) bases[nb++] = pare[x];
                    if (nb > 0) e = bases[rndint(nb)];
                }
            }
        }
        if (e < 0) e = rndint(NE);
        int old = G[e], nw = rndint(c);
        if (nw == old) continue;
        G[e] = nw;
        build();
        long F2 = evaluate(samp, nsamp, 0);
        if (F2 <= F) { F = F2; acc++; evaluate(samp, nsamp, 1); }
        else { G[e] = old; build(); }
        if (it % 100 == 0) { printf("it %ld F=%ld acc=%ld\n", it, F, acc); fflush(stdout); }
    }
    /* full check on all sources */
    build();
    long Ffull = evaluate(src, nsrc, 0);
    printf("RESULT iters=%ld accepted=%ld F_sample=%ld F_full=%ld\n", it - 1, acc, F, Ffull);
    class_report();
    FILE *o = fopen(argv[8], "w");
    for (int e = 0; e < NE; e++) fprintf(o, "%d\n", G[e]);
    fclose(o);
    return 0;
}
