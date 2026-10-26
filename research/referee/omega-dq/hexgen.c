/* hexgen.c (referee omega-dq): the split Cayley hexagon H(q), q prime, from scratch, in the split-octonion model.
   Split octonions as Zorn vector matrices x = [[a, u], [v, b]] (a, b in F_q, u, v in F_q^3), product
     [[a,u],[v,b]] [[a',u'],[v',b']] = [[aa' + u.v', a u' + b' u + v x v'], [a' v + b v' - u x u', bb' + v.u']].
   Points: 1-spaces <x> of pure octonions (b = -a) with x^2 = 0, i.e. a^2 + u.v = 0 (the quadric Q(6,q)).
   Lines:  2-spaces <x, y> with xy = 0 (Tits; Springer-Veldkamp). The program does not trust this: it checks that every
           point is on q+1 lines, and bitapsp then checks diameter 6 and girth 12 of the incidence graph.
   Writes the incidence graph: first line "N" (= 2n), then one edge "u v" per incidence (points 0..n-1, lines n..2n-1).
   usage: hexgen q out.txt */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int q;
static int md(long a) { a %= q; return (int)(a < 0 ? a + q : a); }

/* x = (a, u0, u1, u2, v0, v1, v2), b = -a; returns 1 if xy = 0 */
static int prod_zero(const int *x, const int *y) {
    long a = x[0], b = -x[0], a2 = y[0], b2 = -y[0];
    const int *u = x + 1, *v = x + 4, *u2 = y + 1, *v2 = y + 4;
    if (md(a * a2 + (long)u[0]*v2[0] + (long)u[1]*v2[1] + (long)u[2]*v2[2])) return 0;
    if (md(b * b2 + (long)v[0]*u2[0] + (long)v[1]*u2[1] + (long)v[2]*u2[2])) return 0;
    for (int i = 0; i < 3; i++) {
        int j = (i + 1) % 3, k = (i + 2) % 3;
        long vx = (long)v[j]*v2[k] - (long)v[k]*v2[j], ux = (long)u[j]*u2[k] - (long)u[k]*u2[j];
        if (md(a * u2[i] + b2 * u[i] + vx)) return 0;
        if (md(a2 * v[i] + b * v2[i] - ux)) return 0;
    }
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 3) { fprintf(stderr, "usage: hexgen q out\n"); return 1; }
    q = atoi(argv[1]);
    long qq7 = 1; for (int i = 0; i < 7; i++) qq7 *= q;
    int cap = 1 << 20, n = 0;
    int (*P)[7] = malloc(sizeof(int[7]) * cap);
    int *idx = malloc(sizeof(int) * qq7);              /* base-q code of a normalised vector -> point index */
    for (long c = 0; c < qq7; c++) idx[c] = -1;
    for (long c = 1; c < qq7; c++) {
        int x[7]; long r = c;
        for (int i = 6; i >= 0; i--) { x[i] = r % q; r /= q; }
        int f = 0; while (x[f] == 0) f++;
        if (x[f] != 1) continue;                        /* first nonzero coordinate 1 */
        long Q = (long)x[0]*x[0] + (long)x[1]*x[4] + (long)x[2]*x[5] + (long)x[3]*x[6];
        if (md(Q) != 0) continue;
        memcpy(P[n], x, sizeof x); idx[c] = n; n++;
    }
    long want = (qq7 / q - 1) / (q - 1);               /* (q^6-1)/(q-1) */
    fprintf(stderr, "q=%d points %d (expected %ld)\n", q, n, want);
    if (n != want) return 2;
    int inv[256]; for (int a = 1; a < q; a++) for (int b = 1; b < q; b++) if (a * b % q == 1) inv[a] = b;
    int *lines = malloc(sizeof(int) * (q + 1) * (long)n * 2); long nl = 0;
    int *deg = calloc(n, sizeof(int)); long npairs = 0;
    for (int a = 0; a < n; a++) {
        for (int b = a + 1; b < n; b++) {
            if (!prod_zero(P[a], P[b])) continue;
            npairs++;
            int pts[256], np = 0;
            pts[np++] = b;
            for (int l = 0; l < q; l++) {                /* the points x + l*y */
                int z[7]; for (int i = 0; i < 7; i++) z[i] = md(P[a][i] + (long)l * P[b][i]);
                int f = 0; while (f < 7 && z[f] == 0) f++;
                if (f == 7) return 4;
                int s = inv[z[f]]; long c = 0;
                for (int i = 0; i < 7; i++) c = c * q + md((long)z[i] * s);
                if (idx[c] < 0) { fprintf(stderr, "line point off the quadric\n"); return 3; }
                pts[np++] = idx[c];
            }
            int m1 = n, m2 = n;                          /* record the line once: when (a, b) are its two smallest points */
            for (int i = 0; i < np; i++) { int v = pts[i]; if (v < m1) { m2 = m1; m1 = v; } else if (v < m2) m2 = v; }
            if (m1 != a || m2 != b) continue;
            for (int i = 0; i < np; i++) { lines[nl * (q + 1) + i] = pts[i]; deg[pts[i]]++; }
            nl++;
        }
    }
    fprintf(stderr, "collinear pairs %ld (expected %ld), lines %ld (expected %d)\n",
            npairs, (long)n * q * (q + 1) / 2, nl, n);
    int bad = 0; for (int a = 0; a < n; a++) if (deg[a] != q + 1) bad++;
    fprintf(stderr, "points not on exactly q+1 lines: %d\n", bad);
    if (nl != n || bad || npairs != (long)n * q * (q + 1) / 2) return 5;
    FILE *fo = fopen(argv[2], "w");
    fprintf(fo, "%d\n", 2 * n);
    for (long l = 0; l < nl; l++) for (int i = 0; i <= q; i++) fprintf(fo, "%d %ld\n", lines[l * (q + 1) + i], n + l);
    fclose(fo);
    return 0;
}
