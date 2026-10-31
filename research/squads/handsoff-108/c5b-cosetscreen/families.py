# Enumerate (q, G, h, H-type) with N = |G|/h in the window, for prime q, G = PSL or PGL, cyclic or dihedral H.
import sys
LO, HI = 588241, 610000
def isprime(n):
    if n < 2: return False
    i = 2
    while i * i <= n:
        if n % i == 0: return False
        i += 1
    return True
rows = []
for q in range(5, 420):
    if not isprime(q): continue
    for G, order in (("PSL", (q**3 - q) // 2), ("PGL", q**3 - q)):
        if order % 2: continue
        for h in range(2, 200):
            if order % h: continue
            N = order // h
            if not (LO <= N <= HI): continue
            # cyclic C_h: element orders in G
            if G == "PSL":
                tors = [x for x in ((q - 1) // 2, (q + 1) // 2) if x % 1 == 0]
                cyc_ok = any(t % h == 0 for t in tors) or h == q
            else:
                cyc_ok = (q - 1) % h == 0 or (q + 1) % h == 0 or h == q
            # dihedral D_m, m = h/2 (order h)
            dih_ok = False
            if h % 2 == 0 and h // 2 >= 3:
                m = h // 2
                if G == "PSL":
                    dih_ok = any(t % m == 0 for t in ((q - 1) // 2, (q + 1) // 2))
                else:
                    dih_ok = (q - 1) % m == 0 or (q + 1) % m == 0
            if cyc_ok or dih_ok:
                rows.append((q, G, h, N, "C%d" % h if cyc_ok else "", "D%d" % (h // 2) if dih_ok else ""))
print("q G h N cyclic dihedral")
for r in rows:
    print(*r)
