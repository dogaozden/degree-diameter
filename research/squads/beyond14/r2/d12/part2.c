static int distinct(int i) { for (int t = 0; t < d; t++) if (t != i && S[t].a == S[i].a && S[t].j == S[i].j) return 0; return 1; }
/* ---- order-2 orbit form: S = {e, x1, b(x1), x2, b(x2)}, b(a,j) = (-a, j) (an involutive automorphism, a != 0 so that
 * b(x) != x). Slots: 0 = e; pair q occupies slots 1+2q (x) and 2+2q (b(x)). Move: replace one pair. ---- */
static inline el bof(el x) { el y = { (M - x.a) % M, x.j }; return y; }
static int pairok(int i) {   /* slot i (x, with a != 0) and slot i+1 (= b(x)) distinct from all other slots */
    if (S[i].a == 0) return 0;
    if (!distinct(i) || !distinct(i + 1)) return 0;
    return 1;
}
/* targeted candidate for pair slot i (partner i+1): a word of length D-1 from e on `side` ending at hole u, with x at a
 * random position and the other letters random from S \ {x, b(x)}; returns the x that makes the word end at u */
static el target2(int i, int side, el u) {
    int L = D - 1, p = 1 + rnd() % L; el x = {0, 0}, z = {0, 0};
    for (int q = 1; q <= L; q++) {
        if (q == p) continue;
        int g; do g = rnd() % d; while (g == i || g == i + 1);
        int useinv = (side == 0) ? (q & 1) : !(q & 1);
        el t = useinv ? SI[g] : S[g];
        if (q < p) x = emul(x, t); else z = emul(z, t);
    }
    el tp = emul(emul(inv(x), u), inv(z));
    int useinv = (side == 0) ? (p & 1) : !(p & 1);
    return useinv ? inv(tp) : tp;
}
