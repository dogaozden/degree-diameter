# Follow-up checks (convention A): (1) strictness: random elements of G should be covered on the odd side;
# (2) even side (words of length 10) for the 15 alpha-fixed elements and for 20 printed holes.
import random
src = open('fixcheck.py').read().split('t0 = time.time()')[0]
exec(src)
mult, L5, T4 = gmulA, build_L5(gmulA), build_T4(gmulA)
random.seed(7)
rnd_unc = 0
for _ in range(150):
    # random PSL element: random SL(2,31) matrix, normalised
    while True:
        a, b, c, d = (random.randrange(P) for _ in range(4))
        if (a*d - b*c) % P == 1: break
    h = normM((a, b, c, d)) + (random.randrange(N),)
    if not cov_odd(h, mult, L5, T4): rnd_unc += 1
print("random elements uncovered on odd side: %d/150" % rnd_unc)
T = set()
for a in range(P):
    for b in range(P):
        for c in range(P):
            for d in range(P):
                if (a*d - b*c) % P == 1:
                    X = (a, b, c, d)
                    if mulM(GM, X) == mulM(X, GM): T.add(normM(X))
fixed = [normM(x) + (0,) for x in sorted(T)]
ev = [cov_even(f, mult, L5) for f in fixed]
print("even side, alpha-fixed (x,0): covered %d, uncovered %d" % (sum(ev), len(ev) - sum(ev)))
ph = holes[:20]
ev_h = [cov_even(h, mult, L5) for h in ph]
print("even side, first 20 printed holes: covered %d, uncovered %d" % (sum(ev_h), len(ev_h) - sum(ev_h)))
