/* haar_plain.c (card c8): tabu search over ALL 9-subsets S of G = C_m : C_k (not self-dual), for the general Haar graph
 * H(G,S): vertices (g,A) = g and (g,B) = n + g, (g,A) ~ (s g, B) for s in S.
 * G = <x,y | x^m = y^k = 1, y x y^-1 = x^r>, element (i,j) = x^i y^j has index i*k + j; (i,j)(a,b) = (i + r^j a, j + b).
 * k = 1 gives the cyclic group C_m.
 * Right translations g -> g h are automorphisms of H(G,S) (on each side), so diameter <= 5 iff the eccentricities of
 * (e,A) and (e,B) are both <= 5.  Energy E = #{v : d((e,A),v) > 5} + #{v : d((e,B),v) > 5} (0 = valid).
 * Tabu: each step NB random single replacements (one element of S by a new element), the best non-tabu one is taken
 * (aspiration if it beats the best energy seen), replaced elements are tabu for TEN steps, restart after STALL steps
 * without improvement of the run's best.  Solutions go to EDGES (first one only) in the apsp format.
 * usage: haar_plain m k r SECS SEED   (env NB=48 TEN=12 STALL=2000 EDGES=file)
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define KV 9
static int m, k, r, n;
static uint16_t *mul;      /* mul[a*n+b] */
static int *inv;
static int S[KV], invS[KV];
static int *dist_st, *stamp_arr, stampv = 0, *queue_arr;
static int NB = 48, TEN = 12, STALL = 2000;
static uint64_t rs = 88172645463325252ULL;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }

static int rpow(int e) { long long p = 1 % m; for (int t = 0; t < e; t++) p = p * r % m; return (int)p; }

static void build_group(void) {
    int *rp = malloc(sizeof(int) * (k + 1));
    for (int j = 0; j < k; j++) rp[j] = rpow(j);
    mul = malloc(sizeof(uint16_t) * (size_t)n * n);
    for (int a = 0; a < n; a++) {
        int i = a / k, j = a % k;
        for (int b = 0; b < n; b++) {
            int c = b / k, d = b % k;
            int ii = (i + (int)((long long)rp[j] * c % m)) % m;
            int jj = (j + d) % k;
            mul[(size_t)a * n + b] = (uint16_t)(ii * k + jj);
        }
    }
    inv = malloc(sizeof(int) * n);
    for (int a = 0; a < n; a++) for (int b = 0; b < n; b++) if (mul[(size_t)a * n + b] == 0) { inv[a] = b; break; }
    free(rp);
}

/* number of vertices at distance > 5 from source src (vertex index in 0..2n-1), BFS cut at depth 5 */
static int far_count(int src) {
    stampv++;
    int head = 0, tail = 0;
    stamp_arr[src] = stampv; dist_st[src] = 0; queue_arr[tail++] = src;
    while (head < tail) {
        int v = queue_arr[head++]; int d = dist_st[v];
        if (d >= 5) continue;
        if (v < n) {                       /* A-vertex g: neighbours (s g, B) */
            for (int t = 0; t < KV; t++) {
                int w = n + mul[(size_t)S[t] * n + v];
                if (stamp_arr[w] != stampv) { stamp_arr[w] = stampv; dist_st[w] = d + 1; queue_arr[tail++] = w; }
            }
        } else {                           /* B-vertex h: neighbours (s^-1 h, A) */
            int h = v - n;
            for (int t = 0; t < KV; t++) {
                int w = mul[(size_t)invS[t] * n + h];
                if (stamp_arr[w] != stampv) { stamp_arr[w] = stampv; dist_st[w] = d + 1; queue_arr[tail++] = w; }
            }
        }
    }
    return 2 * n - tail;
}

static int energy(void) {
    for (int t = 0; t < KV; t++) invS[t] = inv[S[t]];
    return far_count(0) + far_count(n);
}

static int in_set(int x) { for (int t = 0; t < KV; t++) if (S[t] == x) return 1; return 0; }
static void random_set(void) {
    for (int t = 0; t < KV; t++) { int x; do { x = (int)(rnd() % n); } while (in_set(x)); S[t] = x; }
}

int main(int argc, char **argv) {
    if (argc < 6) { fprintf(stderr, "usage: haar_plain m k r SECS SEED\n"); return 2; }
    m = atoi(argv[1]); k = atoi(argv[2]); r = ((atoi(argv[3]) % m) + m) % m;
    double secs = atof(argv[4]);
    rs ^= (uint64_t)atoll(argv[5]) * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 10; i++) rnd();
    if (getenv("NB")) NB = atoi(getenv("NB"));
    if (getenv("TEN")) TEN = atoi(getenv("TEN"));
    if (getenv("STALL")) STALL = atoi(getenv("STALL"));
    const char *edges_out = getenv("EDGES");
    n = m * k;
    if (n > 65535) { fprintf(stderr, "order too big for uint16\n"); return 2; }
    /* check r^k = 1 mod m */
    if (rpow(k) != 1 % m) { fprintf(stderr, "need r^k = 1 mod m\n"); return 2; }
    build_group();
    dist_st = malloc(sizeof(int) * 2 * n); stamp_arr = calloc(2 * n, sizeof(int)); queue_arr = malloc(sizeof(int) * 2 * n);
    if (getenv("SETIN")) {          /* check mode: energy of the 9 indices in SETIN (no search) */
        sscanf(getenv("SETIN"), "%d %d %d %d %d %d %d %d %d", &S[0], &S[1], &S[2], &S[3], &S[4], &S[5], &S[6], &S[7], &S[8]);
        printf("SETIN energy %d\n", energy());
        return 0;
    }
    long long *tabu_until = calloc(n, sizeof(long long));
    clock_t c0 = clock();
    int best = 1 << 30, sols = 0; long long step = 0, restarts = 0, evals = 0;
    random_set();
    int E = energy(); evals++;
    int runbest = E; long long last_imp = 0;
    int gbest_set[KV];
    while (1) {
        double el = (double)(clock() - c0) / CLOCKS_PER_SEC;
        if (el >= secs) break;
        step++;
        int bi = -1, bx = -1, be = 1 << 30, bold = -1;
        for (int t = 0; t < NB; t++) {
            int i = (int)(rnd() % KV); int x = (int)(rnd() % n);
            if (in_set(x)) continue;
            int old = S[i]; S[i] = x; int e2 = energy(); evals++; S[i] = old;
            if (tabu_until[x] > step && e2 >= best) continue;
            if (e2 < be || (e2 == be && (rnd() & 1))) { be = e2; bi = i; bx = x; bold = old; }
        }
        if (bi < 0) continue;
        tabu_until[bold] = step + TEN;
        S[bi] = bx; E = be;
        if (E < runbest) { runbest = E; last_imp = step; }
        if (E < best) { best = E; memcpy(gbest_set, S, sizeof S); }
        if (E == 0) {
            sols++;
            printf("SOL m %d k %d r %d n %d S", m, k, r, n);
            for (int t = 0; t < KV; t++) printf(" %d", S[t]);
            printf("\n"); fflush(stdout);
            if (edges_out && sols == 1) {
                FILE *o = fopen(edges_out, "w");
                fprintf(o, "%d\n", 2 * n);
                for (int g = 0; g < n; g++) for (int t = 0; t < KV; t++) fprintf(o, "%d %d\n", g, n + mul[(size_t)S[t] * n + g]);
                fclose(o);
            }
            random_set(); E = energy(); evals++; runbest = E; last_imp = step; restarts++;
            continue;
        }
        if (step - last_imp > STALL) { random_set(); E = energy(); evals++; runbest = E; last_imp = step; restarts++; }
    }
    printf("PLAIN m %d k %d r %d n %d N %d best %d sols %d steps %lld evals %lld restarts %lld secs %.1f\n",
           m, k, r, n, 2 * n, best, sols, step, evals, restarts, (double)(clock() - c0) / CLOCKS_PER_SEC);
    printf("BESTSET");
    for (int t = 0; t < KV; t++) printf(" %d", gbest_set[t]);
    printf("\n");
    return 0;
}
