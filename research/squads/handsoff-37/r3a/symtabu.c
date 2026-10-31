/* r2f: simulated annealing over G-invariant cubic bipartite graphs (G a permutation group on the vertices, given in a file).
 * Move: pick edges e1=(x,y), e2=(z,w) (x,z in A), form the switch (x,w),(z,y); apply the same switch to every g-image
 * (g in G); accept only if the result is simple, cubic and G-invariant (it is, by construction).
 * Cost: far = number of unordered same-side pairs at distance > 6 (diameter <= 7 iff far = 0 for cubic bipartite),
 * computed from one representative per G-orbit, weighted by orbit size.
 * usage: symloc GROUP GRAPH ITERS T0 T1 SECONDS SEED OUTPREFIX
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <time.h>

#define MAXN 400
#define MAXG 64
int n, ng;
int G[MAXG][MAXN];
int adj[MAXN][3];
int side[MAXN];
int nrep, rep[MAXN], wrep[MAXN];
int Alist[MAXN], nA;
int Rv[MAXG * 2][2], nR;
int Av[MAXG * 2][2], nAe;
int stamp[MAXN], gen = 1;
int dq[MAXN], dd[MAXN];
unsigned long long rs;

static unsigned long long rnd64(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static double rnd01(void) { return (rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static int has_edge(int a, int b) {
    for (int i = 0; i < 3; i++) if (adj[a][i] == b) return 1;
    return 0;
}

/* far from representatives: sum_r w_r * bad_r, far = total / 2 ; same side count = n/2 */
static long long cost(void) {
    long long total = 0;
    int half = n / 2;
    for (int r = 0; r < nrep; r++) {
        int s = rep[r];
        gen++;
        int head = 0, tail = 0;
        dq[tail++] = s; stamp[s] = gen; dd[s] = 0;
        int same = 1; /* s itself */
        while (head < tail) {
            int x = dq[head++];
            if (dd[x] >= 6) continue;
            for (int i = 0; i < 3; i++) {
                int y = adj[x][i];
                if (stamp[y] != gen) {
                    stamp[y] = gen; dd[y] = dd[x] + 1; dq[tail++] = y;
                    if (side[y] == side[s] && (dd[y] % 2 == 0)) same++;
                }
            }
        }
        long long bad = half - same;
        total += (long long)wrep[r] * bad;
    }
    return total / 2;
}

static int in_R(int a, int b) {
    for (int i = 0; i < nR; i++) if (Rv[i][0] == a && Rv[i][1] == b) return 1;
    return 0;
}


/* build the move; returns 1 if valid */
static int build_move(int x, int y, int z, int w) {
    nR = 0; nAe = 0;
    for (int g = 0; g < ng; g++) {
        int pairs[2][2] = { {G[g][x], G[g][y]}, {G[g][z], G[g][w]} };
        for (int p = 0; p < 2; p++) {
            int a = pairs[p][0], b = pairs[p][1];
            if (side[a] != 0) { int t = a; a = b; b = t; }
            int dup = 0;
            for (int i = 0; i < nR; i++) if (Rv[i][0] == a && Rv[i][1] == b) { dup = 1; break; }
            if (!dup) { Rv[nR][0] = a; Rv[nR][1] = b; nR++; }
        }
        int nw[2][2] = { {G[g][x], G[g][w]}, {G[g][z], G[g][y]} };
        for (int p = 0; p < 2; p++) {
            int a = nw[p][0], b = nw[p][1];
            if (side[a] != 0) { int t = a; a = b; b = t; }
            int dup = 0;
            for (int i = 0; i < nAe; i++) if (Av[i][0] == a && Av[i][1] == b) { dup = 1; break; }
            if (!dup) { Av[nAe][0] = a; Av[nAe][1] = b; nAe++; }
        }
    }
    /* validity: every new edge is either absent or being removed; degrees return to 3 */
    static int delta[MAXN];
    static int touched[MAXN * 2], nt;
    nt = 0;
    for (int i = 0; i < nR; i++) {
        int a = Rv[i][0], b = Rv[i][1];
        if (!has_edge(a, b)) return 0; /* removing a non-edge: inconsistent */
        if (delta[a] == 0) touched[nt++] = a;
        delta[a]--; 
        if (delta[b] == 0) touched[nt++] = b;
        delta[b]--;
    }
    int ok = 1;
    for (int i = 0; i < nAe && ok; i++) {
        int a = Av[i][0], b = Av[i][1];
        if (has_edge(a, b) && !in_R(a, b)) ok = 0;
        if (a == b) ok = 0;
        if (delta[a] == 0) touched[nt++] = a;
        delta[a]++;
        if (delta[b] == 0) touched[nt++] = b;
        delta[b]++;
    }
    for (int i = 0; i < nt && ok; i++) if (delta[touched[i]] != 0) ok = 0;
    for (int i = 0; i < nt; i++) delta[touched[i]] = 0;
    /* a G-image might create a double edge within A list: dedupe already done */
    return ok;
}

static int saved_n, saved_v[MAXN * 2];
static int saved_adj[MAXN * 2][3];

static void apply_move(void) {
    /* save touched vertices */
    int cnt = 0; static int mark[MAXN]; static int list[MAXN * 2]; int nl = 0;
    for (int i = 0; i < nR; i++) for (int p = 0; p < 2; p++) {
        int v = p ? Rv[i][1] : Rv[i][0];
        if (!mark[v]) { mark[v] = 1; list[nl++] = v; }
    }
    for (int i = 0; i < nAe; i++) for (int p = 0; p < 2; p++) {
        int v = p ? Av[i][1] : Av[i][0];
        if (!mark[v]) { mark[v] = 1; list[nl++] = v; }
    }
    for (int i = 0; i < nl; i++) { saved_v[cnt] = list[i]; memcpy(saved_adj[cnt], adj[list[i]], sizeof(adj[0])); cnt++; mark[list[i]] = 0; }
    saved_n = cnt;
    for (int i = 0; i < nR; i++) {
        int a = Rv[i][0], b = Rv[i][1];
        for (int j = 0; j < 3; j++) if (adj[a][j] == b) { adj[a][j] = -1; break; }
        for (int j = 0; j < 3; j++) if (adj[b][j] == a) { adj[b][j] = -1; break; }
    }
    for (int i = 0; i < nAe; i++) {
        int a = Av[i][0], b = Av[i][1];
        for (int j = 0; j < 3; j++) if (adj[a][j] == -1) { adj[a][j] = b; break; }
        for (int j = 0; j < 3; j++) if (adj[b][j] == -1) { adj[b][j] = a; break; }
    }
}

static void undo_move(void) {
    for (int i = 0; i < saved_n; i++) memcpy(adj[saved_v[i]], saved_adj[i], sizeof(adj[0]));
}

static void write_graph(const char *fn) {
    FILE *f = fopen(fn, "w");
    fprintf(f, "%d\n", n);
    for (int a = 0; a < n; a++) if (side[a] == 0)
        for (int j = 0; j < 3; j++) fprintf(f, "%d %d\n", a, adj[a][j]);
    fclose(f);
}

int main(int argc, char **argv) {
    if (argc < 9) { fprintf(stderr, "usage: symloc GROUP GRAPH ITERS T0 T1 SECONDS SEED OUTPREFIX\n"); return 1; }
    FILE *f = fopen(argv[1], "r");
    if (fscanf(f, "%d %d", &n, &ng) != 2) return 1;
    for (int g = 0; g < ng; g++) for (int v = 0; v < n; v++) if (fscanf(f, "%d", &G[g][v]) != 1) return 1;
    for (int v = 0; v < n; v++) if (fscanf(f, "%d", &side[v]) != 1) return 1;
    fclose(f);
    long long iters = atoll(argv[3]);
    double T0 = atof(argv[4]), T1 = atof(argv[5]);
    double secs = atof(argv[6]);
    rs = 88172645463325252ULL ^ (unsigned long long)atoll(argv[7]) * 2654435761ULL;
    for (int i = 0; i < 10; i++) rnd64();
    const char *outp = argv[8];
    f = fopen(argv[2], "r");
    int nn; if (fscanf(f, "%d", &nn) != 1 || nn != n) { fprintf(stderr, "graph n mismatch\n"); return 1; }
    for (int v = 0; v < n; v++) for (int j = 0; j < 3; j++) adj[v][j] = -1;
    int deg[MAXN] = {0};
    int a, b;
    while (fscanf(f, "%d %d", &a, &b) == 2) {
        adj[a][deg[a]++] = b; adj[b][deg[b]++] = a;
    }
    fclose(f);
    for (int v = 0; v < n; v++) if (deg[v] != 3) { fprintf(stderr, "degree %d at %d\n", deg[v], v); return 1; }
    /* orbit representatives of G on vertices */
    static int orb[MAXN]; for (int v = 0; v < n; v++) orb[v] = -1;
    nrep = 0;
    for (int v = 0; v < n; v++) if (orb[v] < 0) {
        int sz = 0;
        for (int g = 0; g < ng; g++) { int w = G[g][v]; if (orb[w] < 0) { orb[w] = nrep; sz++; } }
        rep[nrep] = v; wrep[nrep] = sz; nrep++;
    }
    nA = 0; for (int v = 0; v < n; v++) if (side[v] == 0) Alist[nA++] = v;
    long long cur = cost(), best = cur;
    fprintf(stderr, "group %d reps %d start far %lld\n", ng, nrep, cur);
    write_graph(outp);  /* placeholder best = start */
    char fn[512]; sprintf(fn, "%s_best.edges", outp);
    write_graph(fn);
    time_t t0 = time(NULL);
    /* tabu search over orbit moves: at each step sample S valid moves, take the best non-tabu one (aspiration if it
       beats the global best); removed edges become tabu for TT steps. */
    static int tabu_until[MAXN][MAXN];
    memset(tabu_until, 0, sizeof(tabu_until));
    int S = 40; int TT = 15;
    char *ce = getenv("SYMTABU_S"); if (ce) S = atoi(ce);
    ce = getenv("SYMTABU_TT"); if (ce) TT = atoi(ce);
    long long it = 0, valid = 0;
    for (it = 1; it <= iters; it++) {
        long long bc = -1; int bx = -1, by = -1, bz = -1, bw = -1;
        for (int s = 0; s < S; s++) {
            int x = Alist[rnd64() % nA];
            int y = adj[x][rnd64() % 3];
            int z = Alist[rnd64() % nA];
            int w = adj[z][rnd64() % 3];
            if (x == z || y == w) continue;
            if (!build_move(x, y, z, w)) continue;
            valid++;
            int tabu = 0;
            for (int i = 0; i < nAe; i++) if (tabu_until[Av[i][0]][Av[i][1]] > it) { tabu = 1; break; }
            apply_move();
            long long nc = cost();
            undo_move();
            if (tabu && !(nc < best)) continue;
            if (bc < 0 || nc < bc || (nc == bc && (rnd64() & 1))) { bc = nc; bx = x; by = y; bz = z; bw = w; }
        }
        if (bc < 0) continue;
        if (!build_move(bx, by, bz, bw)) continue;
        for (int i = 0; i < nR; i++) {
            tabu_until[Rv[i][0]][Rv[i][1]] = (int)it + TT + (int)(rnd64() % 5);
            tabu_until[Rv[i][1]][Rv[i][0]] = (int)it + TT + (int)(rnd64() % 5);
        }
        apply_move();
        cur = cost();
        if (cur < best) {
            best = cur;
            write_graph(fn);
            fprintf(stderr, "it %lld NEW BEST far %lld\n", it, best);
            if (best == 0) break;
        }
        if ((it & 0x3FF) == 0) {
            if (difftime(time(NULL), t0) > secs) break;
            fprintf(stderr, "it %lld cur %lld best %lld valid %lld\n", it, cur, best, valid);
        }
    }
    long long acc = valid, tried = it;
    fprintf(stderr, "done best %lld cur %lld tried %lld valid %lld acc %lld time %.0fs\n", best, cur, tried, valid, acc, difftime(time(NULL), t0));
    printf("%lld\n", best);
    return 0;
}
