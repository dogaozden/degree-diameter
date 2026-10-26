/* d11: route-chart lift over F2^4 with 9 letters on a Haar controller H(G,S), G = Z_p x| Z_r (metacyclic).
   Vertices of controller: A-side (0,g), B-side (1,g); (0,g) ~ (1,s g) for s in S (|S| = 9).
   Chart: letter k has A_k in GL(4,2) (columns) and b_k != 0 in F2^4.
   Lift edge: (0,g,x) ~ (1, s_k g, A_k x + lam b_k), lam in {0,1}: 18-regular bipartite on 2*m*16 vertices.
   Cost = number of controller vertices g (same-side targets from identity) with no NONSINGULAR nonbacktracking
   4-walk ending at g (nonsingular = controllability vectors c1..c4 span F2^4, so the walk reaches the whole fibre).
   Usage: lift9 p r seed iters T0 T1 outfile */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <stdint.h>
#define K 9
static int P, R, M;
static int tpow[4096];
static unsigned short *MUL;
static int *INV;
static unsigned long long rs;
static inline unsigned long long rnd(void){ rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline int rndi(int n){ return (int)(rnd() % (unsigned long long)n); }
static inline double rndu(void){ return (rnd() >> 11) * (1.0 / 9007199254740992.0); }
typedef struct { unsigned char A[4], Ai[4], b, bB; } Letter;
static Letter L[K];
static int S[K];
static int endp[K][K][K][K];

static int mul(int g, int h){ int a1 = g / R, b1 = g % R, a2 = h / R, b2 = h % R;
    int a = (a1 + (long)tpow[b1] * a2) % P; int b = (b1 + b2) % R; return a * R + b; }
static int apply(const unsigned char *c, int v){ int r = 0; for (int i = 0; i < 4; i++) if (v >> i & 1) r ^= c[i]; return r; }
static int invertible_and_inverse(const unsigned char *A, unsigned char *Ai){
    int inv[16]; int seen[16] = {0};
    for (int v = 0; v < 16; v++){ int o = apply(A, v); if (seen[o]) return 0; seen[o] = 1; inv[o] = v; }
    for (int i = 0; i < 4; i++) Ai[i] = (unsigned char)inv[1 << i];
    return 1;
}
static void rand_letter(Letter *l){
    for (;;){ unsigned char A[4]; for (int i = 0; i < 4; i++) A[i] = rndi(16);
        unsigned char Ai[4]; if (invertible_and_inverse(A, Ai)){ memcpy(l->A, A, 4); memcpy(l->Ai, Ai, 4); break; } }
    do { l->b = rndi(16); } while (l->b == 0);
    l->bB = apply(l->Ai, l->b);
}
static int rank4(int *v){ int basis[4] = {0,0,0,0}, r = 0;
    for (int j = 0; j < 4; j++){ int x = v[j]; for (int bit = 3; bit >= 0; bit--){ if (!(x >> bit & 1)) continue;
            if (!basis[bit]){ basis[bit] = x; r++; break; } x ^= basis[bit]; } }
    return r; }
static void rebuild_endp(void){
    int inv[K]; for (int k = 0; k < K; k++) inv[k] = INV[S[k]];
    for (int k1 = 0; k1 < K; k1++) for (int k2 = 0; k2 < K; k2++) for (int k3 = 0; k3 < K; k3++) for (int k4 = 0; k4 < K; k4++){
        if (k1 == k2 || k2 == k3 || k3 == k4) continue;
        endp[k1][k2][k3][k4] = mul(inv[k4], mul(S[k3], mul(inv[k2], S[k1])));
    }
}
static int nonsing(int k1, int k2, int k3, int k4){
    int v[4];
    v[3] = L[k4].bB;
    v[2] = apply(L[k4].Ai, L[k3].b);
    v[1] = apply(L[k4].Ai, apply(L[k3].A, L[k2].bB));
    v[0] = apply(L[k4].Ai, apply(L[k3].A, apply(L[k2].Ai, L[k1].b)));
    return rank4(v) == 4;
}
static int *covered;

static uint16_t *covm; /* covm[g*16+x0] = union of reached fibre points */
static int cost_of(int *nsing_count){
    memset(covm, 0, (size_t)M * 16 * sizeof(uint16_t)); int ns = 0;
    for (int k1 = 0; k1 < K; k1++) for (int k2 = 0; k2 < K; k2++) for (int k3 = 0; k3 < K; k3++) for (int k4 = 0; k4 < K; k4++){
        if (k1 == k2 || k2 == k3 || k3 == k4) continue;
        int v[4];
        v[3] = L[k4].bB;
        v[2] = apply(L[k4].Ai, L[k3].b);
        v[1] = apply(L[k4].Ai, apply(L[k3].A, L[k2].bB));
        v[0] = apply(L[k4].Ai, apply(L[k3].A, apply(L[k2].Ai, L[k1].b)));
        if (rank4(v) == 4) ns++;
        int span[16];
        for (int lam = 0; lam < 16; lam++){ int s = 0; for (int j = 0; j < 4; j++) if (lam >> j & 1) s ^= v[j]; span[lam] = s; }
        int g = endp[k1][k2][k3][k4];
        for (int x0 = 0; x0 < 16; x0++){
            int y = apply(L[k4].Ai, apply(L[k3].A, apply(L[k2].Ai, apply(L[k1].A, x0))));
            uint16_t mk = 0; for (int lam = 0; lam < 16; lam++) mk |= (uint16_t)(1u << (y ^ span[lam]));
            covm[g * 16 + x0] |= mk;
        }
    }
    int c = 0;
    for (int i = 0; i < M * 16; i++) c += 16 - __builtin_popcount(covm[i]);
    if (nsing_count) *nsing_count = ns;
    return c;
}
static int find_t(void){
    for (int x = 2; x < P; x++){ long y = 1; int ok = 1; int ord = 0;
        /* order of x mod P must be R */
        long z = 1; for (int e = 1; e <= R; e++){ z = z * x % P; if (z == 1){ ord = e; break; } }
        if (ord == R){ long t = 1; for (int b = 0; b < R; b++){ tpow[b] = (int)t; t = t * x % P; } return 1; }
        (void)y; (void)ok;
    }
    return 0;
}
int main(int argc, char **argv){
    if (argc < 8){ fprintf(stderr, "usage: lift9 p r seed iters T0 T1 outfile\n"); return 1; }
    P = atoi(argv[1]); R = atoi(argv[2]); rs = strtoull(argv[3], 0, 10) * 2654435761ULL + 88172645463325252ULL;
    long iters = atol(argv[4]); double T0 = atof(argv[5]), T1 = atof(argv[6]); const char *out = argv[7];
    M = P * R;
    if (!find_t()){ fprintf(stderr, "no element of order %d mod %d\n", R, P); return 1; }
    MUL = malloc((size_t)M * M * sizeof(unsigned short)); INV = malloc(M * sizeof(int)); covered = malloc(M * sizeof(int)); covm = malloc((size_t)M * 16 * sizeof(uint16_t));
    for (int g = 0; g < M; g++) for (int h = 0; h < M; h++) MUL[(size_t)g * M + h] = (unsigned short)mul(g, h);
    for (int g = 0; g < M; g++){ for (int h = 0; h < M; h++) if (MUL[(size_t)g * M + h] == 0){ INV[g] = h; break; } }
    /* init */
    for (int k = 0; k < K; k++){ int ok; do { S[k] = rndi(M); ok = 1; for (int j = 0; j < k; j++) if (S[j] == S[k]) ok = 0; } while (!ok); rand_letter(&L[k]); }
    rebuild_endp();
    int ns; int cur = cost_of(&ns); int best = cur; int bestS[K]; Letter bestL[K]; memcpy(bestS, S, sizeof S); memcpy(bestL, L, sizeof L);
    fprintf(stderr, "m=%d init cost %d nonsing %d\n", M, cur, ns);
    for (long it = 0; it < iters && best > 0; it++){
        double T = T0 * pow(T1 / T0, (double)it / iters);
        int kind = rndi(3);
        int k = rndi(K);
        int oldS = S[k]; Letter oldL = L[k];
        if (kind == 0){ int g; int ok; do { g = rndi(M); ok = 1; for (int j = 0; j < K; j++) if (S[j] == g) ok = 0; } while (!ok); S[k] = g; rebuild_endp(); }
        else if (kind == 1) rand_letter(&L[k]);
        else { /* small change: flip one bit of b or one column of A */
            Letter l = L[k]; if (rndi(2)){ int bit = rndi(4); l.b ^= 1 << bit; if (!l.b) l.b = 1; l.bB = apply(l.Ai, l.b); }
            else { unsigned char A[4]; memcpy(A, l.A, 4); A[rndi(4)] = rndi(16); unsigned char Ai[4];
                if (!invertible_and_inverse(A, Ai)) continue; memcpy(l.A, A, 4); memcpy(l.Ai, Ai, 4); l.bB = apply(l.Ai, l.b); }
            L[k] = l;
        }
        int nc = cost_of(&ns);
        int d = nc - cur;
        if (d <= 0 || rndu() < exp(-d / T)){ cur = nc;
            if (cur < best){ best = cur; memcpy(bestS, S, sizeof S); memcpy(bestL, L, sizeof L); fprintf(stderr, "it %ld best %d nonsing %d T %.3f\n", it, best, ns, T); }
        } else { if (kind == 0){ S[k] = oldS; rebuild_endp(); } else L[k] = oldL; }
    }
    memcpy(S, bestS, sizeof S); memcpy(L, bestL, sizeof L); rebuild_endp();
    int nsf; int fc = cost_of(&nsf);
    printf("p %d r %d m %d cost %d nonsing_words %d\n", P, R, M, fc, nsf);
    FILE *f = fopen(out, "w");
    fprintf(f, "%d %d %d\n", P, R, M);
    for (int k = 0; k < K; k++){ fprintf(f, "%d", S[k]); fprintf(f, " %d %d %d %d %d\n", L[k].A[0], L[k].A[1], L[k].A[2], L[k].A[3], L[k].b); }
    fclose(f);
    return 0;
}
