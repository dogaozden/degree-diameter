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
/* ---- c6: greedy construction (env GREEDY=1) ---- */
static int PCAND = 8, ECAND = 8, DG, gns; static long *gsrc; static time_t tstart;
/* wall-clock guard: the greedy pass must end within gbud seconds (env GBUDGET, default 420); when the measured
   cost per evaluation says it would not, the candidate counts are cut for the remaining orbits */
static double evsec = 0, gbud = 420, gstart; static long evn = 0, steps_left; static int pc_last = -1, ec_last = -1;
static double nowsec(void) { struct timespec ts; clock_gettime(CLOCK_MONOTONIC, &ts); return ts.tv_sec + 1e-9 * ts.tv_nsec; }
static long evalc(void) {
    double t = nowsec(); fill(); om_build(&o); long c = om_far(&o, gsrc, gns, DG, NULL, NULL, NULL);
    evsec += nowsec() - t; evn++; return c;
}
/* give orbit s target t; the orbit s2 that held t receives the old target of s, so pi stays a permutation */
static void set_target(int *pi, int *inv, int s, int t) {
    int s2 = inv[t], old = pi[s];
    pi[s] = t; pi[s2] = old; inv[t] = s; inv[old] = s2;
}
/* block B, w = 0 (P) or 1 (L): orbits in random order; target pi(s) tried among up to PCAND still-unused targets,
   then e(s) among ECAND random exponents; each choice by full cost (the annealer's cost).  Returns cost after the block. */
static long greedy_block(int B, int w) {
    int *pi = (w ? piL : piP) + (long)B * r, *e = (w ? eL : eP) + (long)B * r;
    int *inv = malloc(sizeof(int) * r), *pool = malloc(sizeof(int) * r), *tmp = malloc(sizeof(int) * r), *ord = malloc(sizeof(int) * r);
    for (int s = 0; s < r; s++) { inv[pi[s]] = s; pool[s] = s; ord[s] = s; }
    for (int i = r - 1; i > 0; i--) { int u = rnd() % (i + 1); int x = ord[i]; ord[i] = ord[u]; ord[u] = x; }
    int np = r; long cost = 0;
    for (int q = 0; q < r; q++) {
        int s = ord[q];
        /* candidate counts for this orbit: PCAND / ECAND unless the time guard says fewer */
        double per = evn ? evsec / evn : 0.1, left = gbud - (nowsec() - gstart);
        int tot = (int)(left / (steps_left * per)), pc = PCAND, ec = ECAND;
        if (tot < PCAND + ECAND) { pc = tot - 1 < 1 ? 1 : (tot + 1) / 2; if (pc > PCAND) pc = PCAND; ec = tot - pc; if (ec < 0) ec = 0; if (ec > ECAND) ec = ECAND; }
        if (pc != pc_last || ec != ec_last) { fprintf(stderr, "greedy counts: PCAND %d ECAND %d (projected evals/step %d, %.3f s/eval)\n", pc, ec, tot, per); pc_last = pc; ec_last = ec; }
        steps_left--;
        int nc = np < pc ? np : pc;
        memcpy(tmp, pool, sizeof(int) * np);
        for (int i = 0; i < nc; i++) { int u = i + rnd() % (np - i); int x = tmp[i]; tmp[i] = tmp[u]; tmp[u] = x; }
        long bc = -1; int bt = -1;
        for (int i = 0; i < nc; i++) {
            int t = tmp[i], old = pi[s];
            set_target(pi, inv, s, t); long c = evalc(); set_target(pi, inv, s, old);
            if (bc < 0 || c < bc) { bc = c; bt = t; }
        }
        set_target(pi, inv, s, bt);
        for (int i = 0; i < np; i++) if (pool[i] == bt) { pool[i] = pool[--np]; break; }
        int bex = e[s]; long be = -1;
        if (ec == 0) { be = evalc(); }
        for (int i = 0; i < ec; i++) {
            int x = rnd() % m, old = e[s];
            e[s] = x; long c = evalc(); e[s] = old;
            if (be < 0 || c < be) { be = c; bex = x; }
        }
        e[s] = bex; cost = be;
        if (q % 16 == 15 || q == r - 1) fprintf(stderr, "greedy B %d %s orbit %d/%d cost %ld t %.0f\n", B, w ? "L" : "P", q + 1, r, cost, difftime(time(NULL), tstart));
    }
    free(inv); free(pool); free(tmp); free(ord);
    return cost;
}
int main(int argc, char **argv) {
    tstart = time(NULL);
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
    int greedy = getenv("GREEDY") != NULL;   /* c6: start from identity (pi, e) everywhere and build blocks 1.. greedily */
    if (getenv("PCAND")) PCAND = atoi(getenv("PCAND"));
    if (getenv("ECAND")) ECAND = atoi(getenv("ECAND"));
    piP = malloc(sizeof(int) * K * r); eP = malloc(sizeof(int) * K * r); piL = malloc(sizeof(int) * K * r); eL = malloc(sizeof(int) * K * r);
    for (int B = 0; B < K; B++) {
        for (int s = 0; s < r; s++) { piP[B * r + s] = s; piL[B * r + s] = s; eP[B * r + s] = 0; eL[B * r + s] = 0; }
        if (B > 0 && !greedy) for (int s = r - 1; s > 0; s--) { int u = rnd() % (s + 1); int tt = piP[B * r + s]; piP[B * r + s] = piP[B * r + u]; piP[B * r + u] = tt; }
        if (!greedy) for (int s = r - 1; s > 0; s--) { int u = rnd() % (s + 1); int tt = piL[B * r + s]; piL[B * r + s] = piL[B * r + u]; piL[B * r + u] = tt; }
        if (!greedy) for (int s = 0; s < r; s++) { if (B > 0) eP[B * r + s] = rnd() % m; eL[B * r + s] = rnd() % m; }
    }
    long ns = 0, *src = malloc(sizeof(long) * (10 * r * (A + 1)));
    for (int s = 0; s < r; s++) { int p = orbP[s * m]; for (int k = 0; k < (Z5 ? 1 : 5); k++) { src[ns++] = om_hub(&o, p, 0, k); src[ns++] = om_hub(&o, p, 1, k); } }
    long nhub = ns;
    for (int c = 0; c < 5 * A; c += Z5 ? 5 : 1) for (int s = 0; s < r; s++) { src[ns++] = (long)c * 2 * n + orbP[s * m]; src[ns++] = (long)c * 2 * n + n + orbL[s * m]; }
    long nall = ns; if (hubonly) ns = nhub;
    gsrc = src; gns = (int)ns; DG = D;
    if (getenv("GBUDGET")) gbud = atof(getenv("GBUDGET"));
    if (greedy) {
        gstart = nowsec(); steps_left = (long)(K - 1) * 2 * r;
        for (int B = 1; B < K; B++) for (int w = 0; w < 2; w++) {
            long c = greedy_block(B, w);
            fprintf(stderr, "greedy block %d %s done: cost %ld t %.0f evals %ld (%.3f s/eval)\n", B, w ? "L" : "P", c, difftime(time(NULL), tstart), evn, evsec / (evn ? evn : 1));
        }
    }
    fill(); om_build(&o);
    long cur = om_far(&o, src, (int)ns, D, NULL, NULL, NULL), best = cur, start0 = cur;
    fprintf(stderr, "%s %ld (sources %ld) t %.0f\n", greedy ? "GREEDY pass cost" : "start cost", cur, ns, difftime(time(NULL), tstart));
    char path[512]; snprintf(path, sizeof path, "%s.lab", pre);
    if (greedy) om_write_lab(&o, path);
    /* annealing gets the time left of SECONDS (counted from program start, so greedy + annealing <= SECONDS) */
    time_t t0 = time(NULL); long it = 0, acc = 0; double T = T0;
    double asecs = secs - difftime(t0, tstart);
    while (best > 0 && difftime(time(NULL), t0) < asecs) {
        it++;
        int B = rnd() % K, w = rnd() % 2; if (B == 0 && w == 0) w = 1;
        int *pi = w ? piL : piP, *e = w ? eL : eP;
        int s1 = rnd() % r, s2 = rnd() % r, kind = rnd() % 2, sv1 = pi[B * r + s1], sv2 = pi[B * r + s2], ev1 = e[B * r + s1], ev2 = e[B * r + s2];
        if (kind == 0 || r == 1) { if (m == 1) continue; e[B * r + s1] = rnd() % m; }
        else { if (s1 == s2) continue; pi[B * r + s1] = sv2; pi[B * r + s2] = sv1; e[B * r + s1] = ev2; e[B * r + s2] = ev1; }
        fill(); om_build(&o);
        long c = om_far(&o, src, (int)ns, D, NULL, NULL, NULL);
        double frac = difftime(time(NULL), t0) / asecs; T = T0 * (1 - frac) + 1e-3;
        if (c <= cur || exp((cur - c) / T) * 4294967296.0 > (double)(rnd() & 0xffffffff)) {
            cur = c; acc++;
            if (c < best) {
                best = c; fprintf(stderr, "it %ld t %.0f cost %ld\n", it, difftime(time(NULL), t0), best);
                om_write_lab(&o, path);
            }
        } else { pi[B * r + s1] = sv1; pi[B * r + s2] = sv2; e[B * r + s1] = ev1; e[B * r + s2] = ev2; }
    }
    fill(); om_build(&o); long fin = om_far(&o, src, (int)nall, D, NULL, NULL, NULL);
    printf("final check over all %ld orbit representatives: far pairs %ld\n", nall, fin);
    printf("RESULT types=%s inner=%s m=%d D=%d greedy=%d start=%ld best=%ld iters=%ld accepted=%ld lab=%s\n", o.types, o.inner, m, D, greedy, start0, best, it, acc, path);
    return 0;
}
