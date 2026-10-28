# Lemma 7.13 of joint.tex from Definition 7.1: for every block pattern, the stated copy c' is missed by X and
# exactly one copy of C(X) per block shares a class of the other bar with c' (so r4 = alpha).
import itertools
def C(cls, typ):  # cls = (k, barred)
    k, bar = cls; out = set()
    for B, t in enumerate(typ):
        offs = ({'a': (-1, 1), 'b': (3, 4)} if not bar else {'a': (2, 3), 'b': (-1, 1)})[t]
        for o in offs: out.add((B, (k + o) % 5))
    return out
def classes_meeting(copy, typ, bar):
    return {k for k in range(5) if copy in C((k, bar), typ)}
for alpha in range(1, 9):
    for typ in itertools.product('ab', repeat=alpha):
        for k in range(5):
            for bar in (False, True):
                X = (k, bar); CX = C(X, typ)
                if not bar:
                    Bp = next((B for B, t in enumerate(typ) if t == 'a'), None)
                    cp = (Bp, (k + 3) % 5) if Bp is not None else (0, k % 5)
                else:
                    Bp = next((B for B, t in enumerate(typ) if t == 'b'), None)
                    cp = (Bp, (k + 3) % 5) if Bp is not None else (0, (k + 1) % 5)
                assert cp not in CX
                other = classes_meeting(cp, typ, not bar)
                N = [c1 for c1 in CX if classes_meeting(c1, typ, not bar) & other]
                assert len(N) == alpha and len({B for B, _ in N}) == alpha, (typ, X, cp, N)
print("Lemma 7.13 holds for every pattern with alpha <= 8")
