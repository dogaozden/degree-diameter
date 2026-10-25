"""Write metacyclic Cayley tables Z_M x|_t Z_N (N in NLO..NHI) of order in [LO, HI] into OUT (ctrl_search format).
usage: python3 mkmeta.py LO HI NLO NHI OUT   (prints 'name file' lines)"""
import sys, os, math
sys.path.insert(0, '/home/user/degree-diameter/research/theorems/chartlift')
import groups
lo, hi, nlo, nhi, out = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), sys.argv[5]
os.makedirs(out, exist_ok=True)
for n in range(lo, hi + 1):
    for k in range(nlo, nhi + 1):
        if n % k: continue
        m = n // k
        if m < 3: continue
        seen = set()
        for t in range(2, m):
            if math.gcd(t, m) != 1 or pow(t, k, m) != 1: continue
            sub = frozenset(pow(t, e, m) for e in range(k))
            if sub in seen: continue
            seen.add(sub)
            name = 'meta:%d:%d:%d' % (m, k, t)
            fn = os.path.join(out, name.replace(':', '_') + '.txt')
            if not os.path.exists(fn):
                T = groups.make(name)
                with open(fn, 'w') as f:
                    f.write('%d\n' % len(T)); f.write(' '.join(str(x) for row in T for x in row) + '\n')
            print(name, fn, n)
