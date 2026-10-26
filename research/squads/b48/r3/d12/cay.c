/* Bipartite Cayley graph search, D=9, degree 4.
   usage: cay TABLE.bin PHI.bin MODE SECONDS SEED [D]
   TABLE.bin: int32 N, then N*N uint16 (row g: g*h), identity 0 (groups.py format).
   PHI.bin: N bytes, homomorphism G -> Z_2 (generators must lie in phi=1).
   MODE: ex1  exhaustive over {a,a^-1,b,b^-1} (non-involutions, both in phi=1), SECONDS = time cap
         sa2  annealing over {a,a^-1,b,c}, b,c involutions in phi=1
         sa3  annealing over four involutions in phi=1
         sa1  annealing over {a,a^-1,b,b^-1}
   Cost = number of group elements not reached from e within D steps (= vertices of the Cayley graph at distance > D from e).
   Prints BEST cost and S (element indices), and writes best S to stdout line "S a b c d". */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <stdint.h>
#include <math.h>

static int N, D = 9;
static uint16_t *TR;   /* TR[s*N + x] = x*s */
static uint16_t *TT;   /* T[x*N+s] */
static uint8_t *phi;
static int *inv_, *stamp_, *queue_;
static int curstamp = 0;

static unsigned long long rng_state;
static inline unsigned long long rnd(void) {
    rng_state ^= rng_state << 13; rng_state ^= rng_state >> 7; rng_state ^= rng_state << 17; return rng_state;
}
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }

/* number of reached elements within D steps from 0 using generator list gens[0..d-1] */
static int reach(const int *gens, int d) {
    curstamp++;
    int head = 0, tail = 0, cnt = 1;
    queue_[tail++] = 0; stamp_[0] = curstamp;
    for (int lev = 0; lev < D; lev++) {
        int end = tail;
        if (head == end) break;
        for (; head < end; head++) {
            int x = queue_[head];
            for (int i = 0; i < d; i++) {
                int y = TR[(size_t)gens[i] * N + x];
                if (stamp_[y] != curstamp) { stamp_[y] = curstamp; queue_[tail++] = y; }
            }
        }
    }
    cnt = tail;
    return cnt;
}

static int *cls_reps; static int ncls;     /* non-involution class reps in phi=1 */
static int *invol; static int ninv;       /* involutions in phi=1 */

static void print_S(FILE *f, const int *g, int d, int cost) {
    fprintf(f, "cost %d S", cost);
    for (int i = 0; i < d; i++) fprintf(f, " %d", g[i]);
    fprintf(f, "\n");
}

int main(int argc, char **argv) {
    if (argc < 6) { fprintf(stderr, "usage: cay TABLE PHI MODE SECONDS SEED [D]\n"); return 1; }
    FILE *f = fopen(argv[1], "rb"); if (!f) { perror("table"); return 1; }
    int32_t n32; if (fread(&n32, 4, 1, f) != 1) return 1; N = n32;
    uint16_t *T = malloc((size_t)N * N * 2);
    if (fread(T, 2, (size_t)N * N, f) != (size_t)N * N) { fprintf(stderr, "short table\n"); return 1; }
    fclose(f);
    phi = malloc(N); f = fopen(argv[2], "rb"); if (!f || fread(phi, 1, N, f) != (size_t)N) { fprintf(stderr, "phi\n"); return 1; } fclose(f);
    const char *mode = argv[3];
    double secs = atof(argv[4]);
    rng_state = 88172645463325252ULL ^ (unsigned long long)atoll(argv[5]) * 2654435761ULL;
    if (argc > 6) D = atoi(argv[6]);
    /* transpose: TR[s*N + x] = T[x*N + s] = x*s */
    TR = malloc((size_t)N * N * 2);
    for (int x = 0; x < N; x++) for (int s = 0; s < N; s++) TR[(size_t)s * N + x] = T[(size_t)x * N + s];
    inv_ = malloc(sizeof(int) * N); for (int g = 0; g < N; g++) for (int h = 0; h < N; h++) if (T[(size_t)g * N + h] == 0) { inv_[g] = h; break; }
    /* sanity: phi homomorphism */
    for (int x = 0; x < N; x += 1) for (int y = 0; y < N; y += 7) if (phi[T[(size_t)x * N + y]] != (phi[x] ^ phi[y])) { fprintf(stderr, "phi not a homomorphism\n"); return 2; }
    stamp_ = calloc(N, sizeof(int)); queue_ = malloc(sizeof(int) * N);
    cls_reps = malloc(sizeof(int) * N); invol = malloc(sizeof(int) * N); ncls = 0; ninv = 0;
    for (int g = 1; g < N; g++) {
        if (phi[g] != 1) continue;
        if (inv_[g] == g) invol[ninv++] = g;
        else if (g < inv_[g]) cls_reps[ncls++] = g;
    }
    fprintf(stderr, "N=%d classes(non-invol, phi=1)=%d involutions(phi=1)=%d\n", N, ncls, ninv);
    double t0 = now();
    int gens[4];
    int bestcost = 1 << 30; int best[4] = {0};
    long long evals = 0;

    if (strcmp(mode, "ex1") == 0) {
        for (int i = 0; i < ncls && now() - t0 < secs; i++) {
            int a = cls_reps[i];
            gens[0] = a; gens[1] = inv_[a];
            for (int j = i + 1; j < ncls; j++) {
                int b = cls_reps[j];
                gens[2] = b; gens[3] = inv_[b];
                int r = reach(gens, 4); evals++;
                int cost = N - r;
                if (cost < bestcost) { bestcost = cost; best[0]=a; best[1]=b; print_S(stderr, best, 2, cost); }
                if (cost == 0) { printf("VALID "); print_S(stdout, (int[]){a, inv_[a], b, inv_[b]}, 4, 0); }
            }
        }
        if (bestcost == 0) {}
        printf("EXHAUSTIVE_DONE evals=%lld completed=%d best=%d\n", evals, (now()-t0) < secs, bestcost);
        printf("BEST cost %d S a=%d b=%d\n", bestcost, best[0], best[1]);
    } else {
        /* annealing */
        int type = (mode[2] == '2') ? 2 : (mode[2] == '3') ? 3 : 1;
        int ncur = 0;
        int cur[4];
        /* state: for type 1: cur[0]=a, cur[1]=b (classes); type 2: a, b, c (b,c involutions); type 3: four involutions */
        int nslot = (type == 1) ? 2 : (type == 2) ? 3 : 4;
        #define GENS_FROM(st, out) do { if (type == 1) { out[0]=(st)[0]; out[1]=inv_[(st)[0]]; out[2]=(st)[1]; out[3]=inv_[(st)[1]]; } \
            else if (type == 2) { out[0]=(st)[0]; out[1]=inv_[(st)[0]]; out[2]=(st)[1]; out[3]=(st)[2]; } \
            else { out[0]=(st)[0]; out[1]=(st)[1]; out[2]=(st)[2]; out[3]=(st)[3]; } } while (0)
        #define RANDOM_SLOT(i) ( (type == 1 || (type == 2 && (i) == 0)) ? cls_reps[rnd() % ncls] : invol[rnd() % ninv] )
        int sb[4], g4[4];
        double T0 = 3.0, T1 = 0.05;
        int restarts = 0;
        int state[4]; int curc;
        while (now() - t0 < secs) {
            for (int i = 0; i < nslot; i++) state[i] = RANDOM_SLOT(i);
            /* check distinct */
            int ok = 1;
            for (int i = 0; i < nslot; i++) for (int j = 0; j < i; j++) if (state[i] == state[j]) ok = 0;
            if (!ok) continue;
            GENS_FROM(state, g4); curc = N - reach(g4, 4); evals++;
            double tstart = now(); double dur = 5.0; /* cooling cycle length */
            long long it = 0;
            while (now() - t0 < secs) {
                double frac = (now() - tstart) / dur; if (frac >= 1.0) break;
                double temp = T0 * pow(T1 / T0, frac);
                int i = rnd() % nslot;
                int old = state[i];
                state[i] = RANDOM_SLOT(i);
                int dup = 0;
                for (int j = 0; j < nslot; j++) if (j != i && state[j] == state[i]) dup = 1;
                if (dup) { state[i] = old; continue; }
                GENS_FROM(state, g4);
                int c = N - reach(g4, 4); evals++; it++;
                int dc = c - curc;
                if (dc <= 0 || (double)(rnd() % 1000000) / 1e6 < exp(-dc / temp)) {
                    curc = c;
                    if (c < bestcost) { bestcost = c; memcpy(sb, state, sizeof(state)); print_S(stderr, g4, 4, c); }
                    if (c == 0) break;
                } else state[i] = old;
                if (bestcost == 0) break;
            }
            restarts++;
            if (bestcost == 0) break;
        }
        GENS_FROM(sb, g4);
        printf("BEST cost %d S", bestcost); for (int i = 0; i < 4; i++) printf(" %d", g4[i]); printf("\n");
        printf("EVALS %lld RESTARTS %d\n", evals, restarts);
    }
    return 0;
}
