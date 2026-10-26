/* r2-c5: coset graphs with two vertex orbits per side.
 * White side: W1 = G (regular, H1 = 1) and W2 = G/<a> (|G|/2 left cosets x<a>).
 * Black side: B1 = G (regular) and B2 = G/<b>. n = 3|G|.
 * x H_i ~ y H_j iff x^-1 y in D_ij, D_ij a union of H_i D H_j double cosets.
 * Degree equations (d_ij = |D_ij|, H_1 = 1, H_2 = <a> or <b>):
 *   d11 + d12/2 = 3, d21 + d22/2 = 3, d11 + d21/2 = 3, d12 + d22/2 = 3
 * which force d12 = d21 = 2, d11 = 2, d22 = 2 (d12 = 0 is disconnected). D22 of size 2 needs a ~ b.
 * So D11 = {p,q}, D12 = {g1, g1 b}, D21 = {g2, a g2}, D22 = {g, a g} with g b = a g.
 * Usage: c5 GROUPS OUTPREFIX     (env CHECK=k: generic-definition check every k-th graph)
 * cost = #unordered same-side pairs at distance > 6 (cost 0 <=> diameter <= 7).
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAXN 128
#define MAXV 512

static int N, H, WSIZE, NV;
static int M[MAXN][MAXN], inv_[MAXN];
static int adj[MAXV][3];
static int dist[MAXV], que[MAXV];
static int cw[MAXN], cb[MAXN], rw[MAXN], rb[MAXN];
static int A, B;

static int bfs(int s) {
    int h = 0, t = 0;
    for (int v = 0; v < NV; v++) dist[v] = -1;
    dist[s] = 0; que[t++] = s;
    while (h < t) {
        int v = que[h++];
        for (int k = 0; k < 3; k++) {
            int u = adj[v][k];
            if (dist[u] < 0) { dist[u] = dist[v] + 1; que[t++] = u; }
        }
    }
    return t;
}

/* vertices: W1 x -> x; W2 k -> N + k; B1 y -> WSIZE + y; B2 k -> WSIZE + N + k */
static void buildAdj(int p, int q, int g1, int g2, int g) {
    int ip = inv_[p], iq = inv_[q], ig1 = inv_[g1], ig2 = inv_[g2], ig = inv_[g];
    int ag2 = M[A][g2], bg1i = M[B][ig1];
    int B1 = WSIZE, B2 = WSIZE + N, W2 = N;
    for (int x = 0; x < N; x++) {
        adj[x][0] = B1 + M[x][p];
        adj[x][1] = B1 + M[x][q];
        adj[x][2] = B2 + cb[M[x][g1]];
    }
    for (int k = 0; k < H; k++) {
        int x = rw[k];
        adj[W2 + k][0] = B1 + M[x][g2];
        adj[W2 + k][1] = B1 + M[x][ag2];
        adj[W2 + k][2] = B2 + cb[M[x][g]];
    }
    for (int y = 0; y < N; y++) {
        adj[B1 + y][0] = M[y][ip];
        adj[B1 + y][1] = M[y][iq];
        adj[B1 + y][2] = W2 + cw[M[y][ig2]];
    }
    for (int k = 0; k < H; k++) {
        int y = rb[k];
        adj[B2 + k][0] = M[y][ig1];
        adj[B2 + k][1] = M[y][bg1i];
        adj[B2 + k][2] = W2 + cw[M[y][ig]];
    }
}

/* generic check straight from the definition, all coset members */
static int generic_ok(int p, int q, int g1, int g2, int g) {
    int D[4][2] = {{p, q}, {g1, M[g1][B]}, {g2, M[A][g2]}, {g, M[A][g]}};
    for (int v = 0; v < WSIZE; v++) {
        int vi = v < N ? 0 : 1;
        int wm[2], nwm;
        if (vi == 0) { wm[0] = v; nwm = 1; }
        else { int k = v - N; wm[0] = rw[k]; wm[1] = M[rw[k]][A]; nwm = 2; }
        int ncount = 0;
        for (int u = WSIZE; u < NV; u++) {
            int ui = u < WSIZE + N ? 0 : 1;
            int bm[2], nbm;
            if (ui == 0) { bm[0] = u - WSIZE; nbm = 1; }
            else { int k = u - WSIZE - N; bm[0] = rb[k]; bm[1] = M[rb[k]][B]; nbm = 2; }
            int cnt = 0, t = vi * 2 + ui;
            for (int i = 0; i < nwm; i++) for (int j = 0; j < nbm; j++) {
                int e = M[inv_[wm[i]]][bm[j]];
                if (e == D[t][0] || e == D[t][1]) cnt++;
            }
            if (cnt != 0 && cnt != nwm * nbm) return 0;
            int gadj = cnt > 0;
            int inexp = 0;
            for (int k = 0; k < 3; k++) if (adj[v][k] == u) inexp = 1;
            if (gadj != inexp) return 0;
            ncount += gadj;
        }
        if (ncount != 3) return 0;
    }
    /* black side explicit lists must be exactly their white neighbours */
    for (int u = WSIZE; u < NV; u++) {
        int c = 0;
        for (int v = 0; v < WSIZE; v++) {
            for (int k = 0; k < 3; k++) if (adj[v][k] == u) c++;
        }
        if (c != 3) return 0;
    }
    return 1;
}

static void write_edges(const char *fn) {
    FILE *o = fopen(fn, "w");
    if (!o) return;
    fprintf(o, "%d\n", NV);
    for (int v = 0; v < WSIZE; v++) for (int k = 0; k < 3; k++) fprintf(o, "%d %d\n", v, adj[v][k]);
    fclose(o);
}

/* returns 0 if disconnected; cost = #same-side pairs at distance > 6, diam = diameter */
static int evaluate(long *costp, int *diamp) {
    int reps[4] = {0, N, WSIZE, WSIZE + N};
    long far[4];
    int diam = 0;
    for (int r = 0; r < 4; r++) {
        int cnt = bfs(reps[r]);
        if (cnt < NV) return 0;
        int lo = reps[r] < WSIZE ? 0 : WSIZE, hi = reps[r] < WSIZE ? WSIZE : NV;
        long fc = 0;
        for (int u = 0; u < NV; u++) if (dist[u] > diam) diam = dist[u];
        for (int u = lo; u < hi; u++) if (dist[u] > 6) fc++;
        far[r] = fc;
    }
    long ord = (long)N * far[0] + (long)H * far[1] + (long)N * far[2] + (long)H * far[3];
    if (ord & 1) { fprintf(stderr, "odd ordered count?!\n"); exit(9); }
    *costp = ord / 2; *diamp = diam;
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 3) { fprintf(stderr, "usage: c5 GROUPS OUTPREFIX\n"); return 1; }
    FILE *f = fopen(argv[1], "r");
    if (!f) { perror("groups"); return 1; }
    const char *prefix = argv[2];
    long checkevery = getenv("CHECK") ? atol(getenv("CHECK")) : 0;
    char tok[64], name[128];
    while (fscanf(f, "%63s", tok) == 1) {
        if (strcmp(tok, "G") != 0) { fprintf(stderr, "bad token %s\n", tok); return 2; }
        int n, id;
        fscanf(f, "%d %d %127s", &n, &id, name);
        N = n; H = N / 2; WSIZE = 3 * N / 2; NV = 3 * N;
        for (int x = 0; x < N; x++) for (int y = 0; y < N; y++) fscanf(f, "%d", &M[x][y]);
        for (int x = 0; x < N; x++) for (int y = 0; y < N; y++) if (M[x][y] == 0) inv_[x] = y;
        int cls[MAXN], clsrep[MAXN], ncls = 0;
        for (int x = 0; x < N; x++) cls[x] = -1;
        for (int x = 1; x < N; x++) if (M[x][x] == 0 && cls[x] < 0) {
            clsrep[ncls] = x;
            for (int g = 0; g < N; g++) cls[M[M[g][x]][inv_[g]]] = ncls;
            ncls++;
        }
        long tried = 0, conn = 0, valid = 0;
        long bestcost = -1; int bestdiam = 1000;
        long hist[64]; memset(hist, 0, sizeof hist);
        int bestA = -1, bestB = -1;
        for (int c = 0; c < ncls; c++) {
            A = clsrep[c];
            for (B = 1; B < N; B++) {
                if (!(M[B][B] == 0 && cls[B] == c)) continue;
                /* reduce b modulo conjugation by N(<a>) (fixes a) */
                int minimal = 1;
                for (int g = 0; g < N && minimal; g++) {
                    if (M[M[g][A]][inv_[g]] != A) continue;
                    if (M[M[g][B]][inv_[g]] < B) minimal = 0;
                }
                if (!minimal) continue;
                int nc = 0;
                for (int x = 0; x < N; x++) cw[x] = -1;
                for (int x = 0; x < N; x++) if (cw[x] < 0) { rw[nc] = x; cw[x] = nc; cw[M[x][A]] = nc; nc++; }
                nc = 0;
                for (int x = 0; x < N; x++) cb[x] = -1;
                for (int x = 0; x < N; x++) if (cb[x] < 0) { rb[nc] = x; cb[x] = nc; cb[M[x][B]] = nc; nc++; }
                int L12[MAXN], n12 = 0, L21[MAXN], n21 = 0, L22[MAXN], n22 = 0;
                for (int g = 0; g < N; g++) {
                    if (g < M[g][B]) L12[n12++] = g;
                    if (g < M[A][g]) L21[n21++] = g;
                    if (M[g][B] == M[A][g] && g < M[A][g]) L22[n22++] = g;
                }
                if (n22 == 0) continue; /* a, b not conjugate */
                int checked_ab = 0;
                for (int p = 0; p < N; p++) for (int q = p + 1; q < N; q++)
                for (int i1 = 0; i1 < n12; i1++) for (int i2 = 0; i2 < n21; i2++) for (int i3 = 0; i3 < n22; i3++) {
                    int g1 = L12[i1], g2 = L21[i2], g = L22[i3];
                    buildAdj(p, q, g1, g2, g);
                    tried++;
                    if (checkevery && ((tried % checkevery) == 0 || !checked_ab)) {
                        checked_ab = 1;
                        if (!generic_ok(p, q, g1, g2, g)) { fprintf(stderr, "CHECK FAILED a%d b%d\n", A, B); return 3; }
                    }
                    long cost; int diam;
                    if (!evaluate(&cost, &diam)) continue;
                    conn++;
                    if (diam < 64) hist[diam]++;
                    if (bestcost < 0 || cost < bestcost || (cost == bestcost && diam < bestdiam)) {
                        bestcost = cost; bestdiam = diam; bestA = A; bestB = B;
                        char fn[512];
                        sprintf(fn, "%s_%s_n%d_best.edges", prefix, name, NV);
                        write_edges(fn);
                    }
                    if (cost == 0) {
                        valid++;
                        if (valid == 1) {
                            char fn[512];
                            sprintf(fn, "%s_%s_n%d_VALID_a%d_b%d.edges", prefix, name, NV, A, B);
                            write_edges(fn);
                            printf("FOUND %s n=%d diam=%d a=%d b=%d p=%d q=%d g1=%d g2=%d g=%d\n",
                                   name, NV, diam, A, B, p, q, g1, g2, g);
                            fflush(stdout);
                        }
                    }
                }
            }
        }
        printf("GROUP %s n=%d tried %ld connected %ld valid %ld bestcost %ld bestdiam %d (a=%d b=%d) hist:",
               name, NV, tried, conn, valid, bestcost, bestdiam, bestA, bestB);
        for (int d = 0; d < 64; d++) if (hist[d]) printf(" %d:%ld", d, hist[d]);
        printf("\n");
        fflush(stdout);
    }
    fclose(f);
    return 0;
}
