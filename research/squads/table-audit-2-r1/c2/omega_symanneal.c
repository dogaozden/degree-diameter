/* omega_symanneal.c (table-audit): search for a labelling of Omega H(q) (omega_model.h) with diameter <= D among
   labellings with two symmetries:
   - Z_5: the 5 copies of a block carry the same labelling (then copy 5B+i -> 5B+i+1, hub (t,k) -> (t,k+1) is an
     automorphism);
   - G = <g>, g an automorphism of H(q) acting semiregularly (orbits of size m) on points and on lines (hex_aut.py):
     rows = base points, and P_B(g t) = g P_B(t), L_B(g t) = g L_B(t), so g acting on every copy and on the rows is
     an automorphism.
   Parameters per block B and orbit s (rep p_s; row t = g^j p_s):  P_B(t) = g^(j + eP) p_(piP(s)),
   L_B(t) = g^(j + eL) l_(piL(s)).  Block 0 has P = identity.  Under both symmetries every vertex is equivalent to
   a hub (p_s,0) or (p_s,0bar), or a point p_s / line l_s of copy 5B, so BFS from those 2r(alpha+1) vertices decides
   the diameter exactly (the final graph is re-checked independently anyway).
   Cost = number of (source, vertex) pairs at distance > D.  Moves: change one exponent, swap two orbits.
   Env ZMODE=2: Z_5 acts with a row twist psi (G-equivariant, psi^5 = 1, orbits of psi on G-orbits are 5-cycles):
   copy 5B+i marks rows by P_B(psi^i(t)), so the 5 copies of a block differ; rotation (copy +1, hub (t,k)->(psi t,k+1))
   is an automorphism and the sources are the same 2r(alpha+1) as for the plain Z_5.  HUBONLY=1: score from hub sources
   only (a final check over all sources is printed).
   Env NOZ5=1: drop the Z_5 symmetry (all 5*alpha copies get their own marking; sources 10r(alpha+1)).
   usage: omega_symanneal HEX AUT TYPES INNER D SECONDS SEED OUTPREFIX [T0]
   AUT: hex_aut.py output (first line used); "none" = trivial group (m = 1, plain Z_5-symmetric search).
   Writes OUTPREFIX.lab (full labelling, omega_model.h format) whenever the best cost improves. */
#include "omega_model.h"
#include <math.h>
#include <time.h>

static uint64_t rs = 0x9E3779B97F4A7C15ULL;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int n, m, r, A, K, Z5 = 1, *psinv; /* psinv[i*n + t] = psi^-i (t) */
static int *orbP, *orbL, *sP, *jP;   /* orbP[s*m+j] = g^j p_s; sP[x], jP[x]: orbit and exponent of point x */
static int *piP, *eP, *piL, *eL;      /* [B*r + s] */
static Omega o;
static void fill(void) {
    for (int B = 0; B < K; B++) for (int t = 0; t < n; t++) {
        int s = sP[t], j = jP[t];
        int pp = orbP[piP[B * r + s] * m + (j + eP[B * r + s]) % m];
        int ll = orbL[piL[B * r + s] * m + (j + eL[B * r + s]) % m];
        if (Z5 == 1) for (int i = 0; i < 5; i++) { o.P[(long)(5 * B + i) * n + t] = pp; o.L[(long)(5 * B + i) * n + t] = ll; }
        else if (Z5 == 0) { o.P[(long)B * n + t] = pp; o.L[(long)B * n + t] = ll; }
        else for (int i = 0; i < 5; i++) { int u = psinv[i * n + t]; o.P[(long)(5 * B + i) * n + u] = pp; o.L[(long)(5 * B + i) * n + u] = ll; }
    }
}
/* c2 (steepest descent with tabu): helpers */
static long *g_src; static int g_ns, g_D; static long g_evals;
static long evalc(void) { fill(); om_build(&o); g_evals++; return om_far(&o, g_src, g_ns, g_D, NULL, NULL, NULL); }
/* snapshot (put=1: save piP,eP,piL,eL into d) / restore (put=0) */
static void snap(int *d, int put) {
    int N = K * r; int *arr[4] = {piP, eP, piL, eL};
    for (int a = 0; a < 4; a++) for (int i = 0; i < N; i++) { if (put) d[a * N + i] = arr[a][i]; else arr[a][i] = d[a * N + i]; }
}
/* random kick move: exponent change or pi swap on a random (B,w) (block 0 P excluded) */
static void rand_move(void) {
    int B, w, s1, s2;
    do { B = rnd() % K; w = rnd() % 2; } while (B == 0 && w == 0);
    int *pi = w ? piL : piP, *e = w ? eL : eP;
    s1 = rnd() % r;
    if ((rnd() & 1) || r == 1) e[B * r + s1] = rnd() % m;
    else { do { s2 = rnd() % r; } while (s2 == s1); int tt = pi[B * r + s1]; pi[B * r + s1] = pi[B * r + s2]; pi[B * r + s2] = tt; }
}

int main(int argc, char **argv) {
    if (argc < 9) { fprintf(stderr, "usage: omega_symanneal HEX AUT TYPES INNER D SECONDS SEED OUTPREFIX [T0]\n"); return 2; }
    if (om_load_hex(&o, argv[1])) return 2;
    om_alloc(&o, argv[3], argv[4]); n = o.n; A = o.A;
    int D = atoi(argv[5]); double secs = atof(argv[6]); rs ^= (uint64_t)atol(argv[7]) * 0x2545F4914F6CDD1DULL;
    for (int i = 0; i < 10; i++) rnd();
    const char *pre = argv[8]; double T0 = argc > 9 ? atof(argv[9]) : 2.0;
    int *g = malloc(sizeof(int) * 2 * n);
    if (!strcmp(argv[2], "none")) for (int i = 0; i < 2 * n; i++) g[i] = i;
    else { FILE *f = fopen(argv[2], "r"); for (int i = 0; i < 2 * n; i++) if (fscanf(f, "%d", &g[i]) != 1) return 2; fclose(f); }
    /* orbits */
    m = 1; { int x = g[0]; while (x != 0) { x = g[x]; m++; } }
    r = n / m; orbP = malloc(sizeof(int) * n); orbL = malloc(sizeof(int) * n); sP = malloc(sizeof(int) * n); jP = malloc(sizeof(int) * n);
    int *sL = malloc(sizeof(int) * n), *jL = malloc(sizeof(int) * n);
    for (int w = 0; w < 2; w++) {
        int *orb = w ? orbL : orbP, *so = w ? sL : sP, *jo = w ? jL : jP, ns = 0;
        for (int x = 0; x < n; x++) so[x] = -1;
        for (int x = 0; x < n; x++) if (so[x] < 0) {
            int y = x, j = 0;
            do { if (j >= m) { fprintf(stderr, "not semiregular\n"); return 2; } so[y] = ns; jo[y] = j; orb[ns * m + j] = y; j++; y = g[w * n + y] - w * n; } while (y != x);
            if (j != m) { fprintf(stderr, "not semiregular (orbit %d)\n", j); return 2; }
            ns++;
        }
        if (ns != r) { fprintf(stderr, "orbit count\n"); return 2; }
    }
    if (getenv("NOZ5")) Z5 = 0;
    if (getenv("ZMODE")) Z5 = atoi(getenv("ZMODE"));
    if (Z5 == 2) {   /* psi(g^j p_s) = g^(j + f(s)) p_tau(s), tau = 5-cycles on orbits (fixed orbits left fixed), cycle sums of f = 0 mod m */
        int *tau = malloc(sizeof(int) * r), *f = malloc(sizeof(int) * r), *ord = malloc(sizeof(int) * r);
        for (int s = 0; s < r; s++) { ord[s] = s; tau[s] = s; f[s] = 0; }
        for (int s = r - 1; s > 0; s--) { int u = rnd() % (s + 1); int tt = ord[s]; ord[s] = ord[u]; ord[u] = tt; }
        for (int b = 0; b + 5 <= r; b += 5) { int sum = 0;
            for (int i = 0; i < 5; i++) { tau[ord[b + i]] = ord[b + (i + 1) % 5]; if (i < 4) { f[ord[b + i]] = rnd() % m; sum += f[ord[b + i]]; } }
            f[ord[b + 4]] = ((-sum) % m + m) % m; }
        int *psi = malloc(sizeof(int) * n); psinv = malloc(sizeof(int) * 5 * n);
        for (int t = 0; t < n; t++) psi[t] = orbP[tau[sP[t]] * m + (jP[t] + f[sP[t]]) % m];
        for (int t = 0; t < n; t++) psinv[t] = t;
        for (int i = 1; i < 5; i++) for (int t = 0; t < n; t++) psinv[i * n + psi[t]] = psinv[(i - 1) * n + t];
        for (int t = 0; t < n; t++) { int u = t; for (int i = 0; i < 5; i++) u = psi[u]; if (u != t) { fprintf(stderr, "psi^5 != 1\n"); return 2; } }
    }
    K = Z5 ? A : 5 * A; int hubonly = getenv("HUBONLY") != NULL;
    fprintf(stderr, "n=%d m=%d r=%d alpha=%d markings=%d\n", n, m, r, A, K);
    piP = malloc(sizeof(int) * K * r); eP = malloc(sizeof(int) * K * r); piL = malloc(sizeof(int) * K * r); eL = malloc(sizeof(int) * K * r);
    for (int B = 0; B < K; B++) {
        for (int s = 0; s < r; s++) { piP[B * r + s] = s; piL[B * r + s] = s; eP[B * r + s] = 0; eL[B * r + s] = 0; }
        if (B > 0) for (int s = r - 1; s > 0; s--) { int u = rnd() % (s + 1); int tt = piP[B * r + s]; piP[B * r + s] = piP[B * r + u]; piP[B * r + u] = tt; }
        for (int s = r - 1; s > 0; s--) { int u = rnd() % (s + 1); int tt = piL[B * r + s]; piL[B * r + s] = piL[B * r + u]; piL[B * r + u] = tt; }
        for (int s = 0; s < r; s++) { if (B > 0) eP[B * r + s] = rnd() % m; eL[B * r + s] = rnd() % m; }
    }
    long ns = 0, *src = malloc(sizeof(long) * (10 * r * (A + 1)));
    for (int s = 0; s < r; s++) { int p = orbP[s * m]; for (int k = 0; k < (Z5 ? 1 : 5); k++) { src[ns++] = om_hub(&o, p, 0, k); src[ns++] = om_hub(&o, p, 1, k); } }
    long nhub = ns;
    for (int c = 0; c < 5 * A; c += Z5 ? 5 : 1) for (int s = 0; s < r; s++) { src[ns++] = (long)c * 2 * n + orbP[s * m]; src[ns++] = (long)c * 2 * n + n + orbL[s * m]; }
    long nall = ns; if (hubonly) ns = nhub;
    fill(); om_build(&o);
    long cur = om_far(&o, src, (int)ns, D, NULL, NULL, NULL), best = cur;
    fprintf(stderr, "start cost %ld (sources %ld)\n", cur, ns);
    char path[512]; snprintf(path, sizeof path, "%s.lab", pre);
    time_t t0 = time(NULL);
    /* Steepest descent with tabu over exponents.  Step = pick (B,w,s) not in the last TABU_LEN picks (block 0 P excluded),
       evaluate ALL m exponents of that orbit slot, set the best (ties random).  Every 10th step: 10 random pi swaps of
       block B, class w, keep the best.  Moves are never worse; after PATIENCE steps without a strict decrease, KICK_MOVES
       random moves are applied unconditionally. */
    const int TABU_LEN = 20, PATIENCE = 30, KICK_MOVES = 3;
    int tabu[20]; for (int i = 0; i < TABU_LEN; i++) tabu[i] = -1; int tpos = 0;
    long step = 0, kicks = 0, noimp = 0;
    int *snapb = malloc(sizeof(int) * 4 * K * r); snap(snapb, 1);
    g_src = src; g_ns = (int)ns; g_D = D;
    while (best > 0 && difftime(time(NULL), t0) < secs) {
        step++;
        int B, w, s, idx, bad;
        do {
            do { B = rnd() % K; w = rnd() % 2; } while (B == 0 && w == 0);
            s = rnd() % r; idx = (B * 2 + w) * r + s; bad = 0;
            for (int i = 0; i < TABU_LEN; i++) if (tabu[i] == idx) bad = 1;
        } while (bad);
        int *pi = w ? piL : piP, *e = w ? eL : eP;
        long before = cur, bc = -1; int chosen = e[B * r + s], ties = 0;
        for (int v = 0; v < m; v++) {
            e[B * r + s] = v;
            long c = evalc();
            if (bc < 0 || c < bc) { bc = c; chosen = v; ties = 1; }
            else if (c == bc && rnd() % (++ties) == 0) chosen = v;
        }
        e[B * r + s] = chosen; cur = bc;   /* bc <= before, since the current value is among the m values */
        tabu[tpos] = idx; tpos = (tpos + 1) % TABU_LEN;
        if (cur < before) noimp = 0; else noimp++;
        if (step % 10 == 0) {   /* 10 random pi swaps of block B, class w; keep the best if not worse */
            long sc = -1; int sa = -1, sb = -1, sties = 0;
            for (int k = 0; k < 10; k++) {
                int a = rnd() % r, b2; do { b2 = rnd() % r; } while (b2 == a);
                int va = pi[B * r + a], vb = pi[B * r + b2];
                pi[B * r + a] = vb; pi[B * r + b2] = va;
                long c = evalc();
                pi[B * r + a] = va; pi[B * r + b2] = vb;
                if (sc < 0 || c < sc) { sc = c; sa = a; sb = b2; sties = 1; }
                else if (c == sc && rnd() % (++sties) == 0) { sa = a; sb = b2; }
            }
            if (sc <= cur) {
                int tt = pi[B * r + sa]; pi[B * r + sa] = pi[B * r + sb]; pi[B * r + sb] = tt;
                if (sc < cur) noimp = 0;
                cur = sc;
            }
        }
        if (cur < best) {
            best = cur; fill(); om_write_lab(&o, path); snap(snapb, 1);
            fprintf(stderr, "step %ld t %.0f evals %ld cost %ld\n", step, difftime(time(NULL), t0), g_evals, best);
        }
        if (noimp >= PATIENCE) {   /* kick: 3 random moves, accepted regardless of cost */
            kicks++;
            for (int k = 0; k < KICK_MOVES; k++) rand_move();
            cur = evalc(); noimp = 0;
            fprintf(stderr, "step %ld t %.0f kick %ld cur %ld best %ld\n", step, difftime(time(NULL), t0), kicks, cur, best);
        }
        if (step % 10 == 0) fprintf(stderr, "status step %ld t %.0f cur %ld best %ld evals %ld kicks %ld\n",
                                    step, difftime(time(NULL), t0), cur, best, g_evals, kicks);
    }
    /* restore the best labelling for the final all-source check */
    snap(snapb, 0); fill(); om_build(&o); long fin = om_far(&o, src, (int)nall, D, NULL, NULL, NULL);
    printf("final check over all %ld orbit representatives: far pairs %ld\n", nall, fin);
    printf("RESULT types=%s inner=%s m=%d D=%d best=%ld steps=%ld evals=%ld kicks=%ld lab=%s\n", o.types, o.inner, m, D, best, step, g_evals, kicks, path);
    return 0;
}
