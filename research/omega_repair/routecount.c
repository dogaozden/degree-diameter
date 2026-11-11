/* routecount.c: for every block pattern of length A, the route numbers of twist.c's formula:
   m4(X,c') = number of distinct non-identity radius-4 centres (w_a w_b^-1, a != b), m2 = non-identity radius-2
   centres, for every hub class X and copy c' it misses.  Prints, per pattern, the pair minimising
   q^5 - m4 q^4 - m2 q^2 (the counting bound of Theorem 3.2) and that bound.  usage: routecount q A  */
#define TWIST_NO_MAIN
#include "twist.c"
int main(int argc, char **argv) {
    int qq = atoi(argv[1]); A = atoi(argv[2]); C = 5 * A; n = 1;
    double q5 = pow(qq, 5), q4 = pow(qq, 4), q2 = (double)qq * qq;
    for (int mask = 0; mask < (1 << A); mask++) {
        /* canonical up to swapping types (a<->b changes the graph) and block order (does not): count a's */
        int na = __builtin_popcount(mask); if (mask != (1 << na) - 1) continue;      /* types = a^na b^(A-na) */
        for (int B = 0; B < A; B++) types[B] = B < na ? 'a' : 'b'; types[A] = 0;
        wiring(); routes();
        double worst = 1e30; int wX = -1, wc = -1, w4 = 0, w2 = 0, has_id = 0, min4 = 99, max4 = 0;
        for (int X = 0; X < 10; X++) for (int cp = 0; cp < C; cp++) if (!att[cp][X]) {
            int m4 = 0, m2 = 0, id = 0;
            for (int i = 0; i < ncen[X][cp]; i++) { Cen e = cen[X][cp][i]; if (e.a < 0) { if (e.R >= 4) id = 1; continue; }
                if (e.R >= 4) m4++; else if (e.R >= 2) m2++; }
            double s = q5 - m4 * q4 - m2 * q2;           /* points of opp(t) certainly uncovered */
            if (m4 < min4) min4 = m4; if (m4 > max4) max4 = m4;
            if (-s < worst) { worst = -s; wX = X; wc = cp; w4 = m4; w2 = m2; has_id = id; }
        }
        printf("q=%d types=%s: m4 range %d..%d; best pair X=%d c'=%d m4=%d m2=%d id4=%d: uncovered >= q^5 - m4 q^4 - m2 q^2 = %.0f per t\n",
               qq, types, min4, max4, wX, wc, w4, w2, has_id, -worst);
    }
    return 0;
}
