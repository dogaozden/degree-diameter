// Sigma-invariant voltage annealer. Lift automorphism Phi(u,g)=(sigma u, phi g) requires v(sigma d)=phi(v(d)) on darts.
// Free variable per dart orbit of sigma; voltages on edges determined. Cost over root orbit representatives (weighted).
// usage: orb BASE GROUP SIGMA PHI|- SECONDS SEED OUTPREFIX T0 T1 [D]
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>
#include <math.h>
#define MAXB 256
#define MAXE 1024
static int N, mul[8][8], invv[8], phi[8], phipow[8][8];
static int nb, m, ea[MAXE], eb[MAXE], etree[MAXE], volt[MAXE];
static int sigv[MAXB], sdart[2 * MAXE];      // sdart[2e+(s<0)] = 2e'+(s'<0)
static int norb, orbstart[MAXE], orbnd[MAXE], orbM[MAXE], orbedge0[MAXE];
static int allowed[MAXE][8], nallowed[MAXE], cur_t[MAXE];
static int nroot, roots[MAXB], rootw[MAXB];
static uint8_t TT[8][256];
static int nin[MAXB], inw[MAXB][8], inx[MAXB][8];
static uint64_t rs = 88172645463325252ULL;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static double urand(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }
static int D = 10;
static int findedge(int a, int b) {
    for (int e = 0; e < m; e++) if ((ea[e] == a && eb[e] == b) || (ea[e] == b && eb[e] == a)) return e;
    return -1;
}
// walk the dart orbit of (e0,+1) with voltage t; fill edge voltages; return 1 if consistent
static int propagate(int e0, int t, int *vals, int *mark) {
    int e = e0, s = 1, v = t, steps = 0;
    do {
        int x = s > 0 ? v : invv[v];
        if (mark[e]) { if (vals[e] != x) return 0; }
        else { mark[e] = 1; vals[e] = x; }
        int code = sdart[2 * e + (s < 0)];
        e = code >> 1; s = (code & 1) ? -1 : 1;
        v = phi[v];
        steps++;
        if (steps > 100000) return 0;
    } while (!(e == e0 && s == 1));
    return v == t;
}
static void build_in(void) {
    for (int v = 0; v < nb; v++) nin[v] = 0;
    for (int e = 0; e < m; e++) {
        int a = ea[e], b = eb[e], x = volt[e];
        inw[b][nin[b]] = a; inx[b][nin[b]] = x; nin[b]++;
        inw[a][nin[a]] = b; inx[a][nin[a]] = invv[x]; nin[a]++;
    }
}
static int cost(int bound) {
    int total = 0;
    uint8_t cur[MAXB], nxt[MAXB];
    for (int r = 0; r < nroot; r++) {
        int u = roots[r];
        memset(cur, 0, nb);
        cur[u] = 1;
        for (int k = 1; k <= D; k++) {
            for (int v = 0; v < nb; v++) {
                uint8_t s = cur[v];
                for (int i = 0; i < nin[v]; i++) s |= TT[inx[v][i]][cur[inw[v][i]]];
                nxt[v] = s;
            }
            memcpy(cur, nxt, nb);
        }
        int c = 0;
        for (int v = 0; v < nb; v++) c += N - __builtin_popcount(cur[v]);
        total += c * rootw[r];
        if (total > bound) return total;
    }
    return total;
}
static void set_orbit(int o, int t) {
    cur_t[o] = t;
    int e = orbedge0[o];
    // recompute values along orbit
    static int vals[MAXE], mark[MAXE];
    memset(mark, 0, sizeof(int) * m);
    propagate(e, t, vals, mark);
    for (int i = 0; i < m; i++) if (mark[i] && orbstart[0] >= 0) { /* only edges of this orbit */ }
    for (int i = 0; i < m; i++) if (mark[i]) volt[i] = vals[i];
}
int main(int argc, char **argv) {
    if (argc < 9) { fprintf(stderr, "usage: orb BASE GROUP SIGMA PHI|- SECONDS SEED OUTPREFIX T0 T1 [D]\n"); return 1; }
    FILE *f = fopen(argv[1], "r");
    if (fscanf(f, "%d %d", &nb, &m) != 2) return 1;
    for (int e = 0; e < m; e++) {
        int a, b, t, s;
        if (fscanf(f, "%d %d %d %d", &a, &b, &t, &s) != 4) return 1;
        ea[e] = a; eb[e] = b; etree[e] = t; volt[e] = 0;
    }
    fclose(f);
    f = fopen(argv[2], "r");
    if (fscanf(f, "%d", &N) != 1) return 1;
    for (int i = 0; i < N; i++) for (int j = 0; j < N; j++) if (fscanf(f, "%d", &mul[i][j]) != 1) return 1;
    fclose(f);
    for (int x = 0; x < N; x++) for (int y = 0; y < N; y++) if (mul[x][y] == 0) invv[x] = y;
    for (int x = 0; x < N; x++) for (int mask = 0; mask < 256; mask++) {
        int r = 0;
        for (int h = 0; h < N; h++) if (mask >> h & 1) r |= 1 << mul[h][x];
        TT[x][mask] = (uint8_t)r;
    }
    f = fopen(argv[3], "r");
    for (int i = 0; i < nb; i++) if (fscanf(f, "%d", &sigv[i]) != 1) return 1;
    fclose(f);
    for (int x = 0; x < N; x++) phi[x] = x;
    if (strcmp(argv[4], "-") != 0) {
        f = fopen(argv[4], "r");
        for (int x = 0; x < N; x++) if (fscanf(f, "%d", &phi[x]) != 1) return 1;
        fclose(f);
    }
    for (int x = 0; x < N; x++) { phipow[0][x] = x; for (int j = 1; j < N; j++) phipow[j][x] = phi[phipow[j - 1][x]]; }
    double secs = atof(argv[5]);
    rs ^= (uint64_t)atoll(argv[6]) * 0x9E3779B97F4A7C15ULL; if (!rs) rs = 1;
    const char *outp = argv[7];
    double T0 = atof(argv[8]), T1 = atof(argv[9]);
    if (argc > 10) D = atoi(argv[10]);
    for (int i = 0; i < 10; i++) rnd();
    // sigma on darts
    for (int e = 0; e < m; e++) for (int s = 0; s < 2; s++) {
        int tail = s == 0 ? ea[e] : eb[e], head = s == 0 ? eb[e] : ea[e];
        int t2 = sigv[tail], h2 = sigv[head];
        int e2 = findedge(t2, h2);
        if (e2 < 0) { fprintf(stderr, "sigma not an automorphism\n"); return 1; }
        int s2 = (ea[e2] == t2) ? 0 : 1;
        sdart[2 * e + s] = 2 * e2 + s2;
    }
    // dart-orbit representatives per edge orbit
    int seen[MAXE]; memset(seen, 0, sizeof seen);
    norb = 0;
    for (int e = 0; e < m; e++) {
        if (seen[e]) continue;
        // edge orbit
        int ee = e, cnt = 0;
        do { seen[ee] = 1; cnt++; int c = sdart[2 * ee]; ee = c >> 1; } while (ee != e);
        orbedge0[norb] = e; orbnd[norb] = cnt;
        // allowed values
        int vals[MAXE], mark[MAXE];
        nallowed[norb] = 0;
        for (int t = 0; t < N; t++) {
            memset(mark, 0, sizeof(int) * m);
            if (propagate(e, t, vals, mark)) allowed[norb][nallowed[norb]++] = t;
        }
        if (nallowed[norb] == 0) { fprintf(stderr, "orbit %d has no consistent voltage\n", norb); return 1; }
        norb++;
    }
    // root orbits under sigma
    int vseen[MAXB]; memset(vseen, 0, sizeof vseen); nroot = 0;
    for (int u = 0; u < nb; u++) {
        if (vseen[u]) continue;
        int w = 0, x = u;
        do { vseen[x] = 1; w++; x = sigv[x]; } while (x != u);
        roots[nroot] = u; rootw[nroot] = w; nroot++;
    }
    fprintf(stderr, "edge orbits %d (allowed sizes:", norb);
    for (int o = 0; o < norb; o++) fprintf(stderr, " %d", nallowed[o]);
    fprintf(stderr, ") root reps %d\n", nroot);
    // random initial assignment
    for (int o = 0; o < norb; o++) set_orbit(o, allowed[o][rnd() % nallowed[o]]);
    build_in();
    int cur = cost(1 << 30), best = cur;
    int bestvolt[MAXE];
    memcpy(bestvolt, volt, sizeof(int) * m);
    clock_t t0 = clock();
    long iters = 0, acc = 0;
    double el = 0, lastp = 0;
    while (1) {
        if ((iters & 63) == 0) {
            el = (double)(clock() - t0) / CLOCKS_PER_SEC;
            if (el >= secs) break;
            if (el - lastp >= 10) { lastp = el; fprintf(stderr, "t=%.0f it=%ld cur=%d best=%d\n", el, iters, cur, best); }
        }
        iters++;
        double Tm = T0 * pow(T1 / T0, el / secs);
        int o = rnd() % norb;
        if (nallowed[o] < 2) continue;
        int oldt = cur_t[o];
        int nt = allowed[o][rnd() % nallowed[o]];
        if (nt == oldt) continue;
        int savev[MAXE]; memcpy(savev, volt, sizeof(int) * m);
        set_orbit(o, nt); build_in();
        double thr = cur - Tm * log(urand() + 1e-300);
        int nc = cost((int)floor(thr));
        if (nc <= thr) {
            cur = nc; acc++;
            if (cur < best) { best = cur; memcpy(bestvolt, volt, sizeof(int) * m); }
            if (cur == 0) break;
        } else { memcpy(volt, savev, sizeof(int) * m); cur_t[o] = oldt; build_in(); }
    }
    fprintf(stderr, "done iters=%ld acc=%ld best=%d\n", iters, acc, best);
    memcpy(volt, bestvolt, sizeof(int) * m);
    char fn[512];
    sprintf(fn, "%s.volt", outp);
    f = fopen(fn, "w");
    fprintf(f, "%d %d %d\n", N, nb, best);
    for (int e = 0; e < m; e++) fprintf(f, "%d %d %d %d\n", ea[e], eb[e], volt[e], etree[e]);
    fclose(f);
    sprintf(fn, "%s.edges", outp);
    f = fopen(fn, "w");
    fprintf(f, "%d\n", nb * N);
    for (int e = 0; e < m; e++)
        for (int g = 0; g < N; g++) fprintf(f, "%d %d\n", ea[e] * N + g, eb[e] * N + mul[g][volt[e]]);
    fclose(f);
    printf("BEST %d\n", best);
    return 0;
}
