"""Write Cayley tables (ctrl_search format) for every group groups.py can build with order in [lo, hi]:
cyclic, Z_a x Z_b, dihedral, dicyclic, and metacyclic Z_m x|_t Z_n (t^n = 1 mod m, t != 1, one t per subgroup <t>).
usage: python3 r3/mkgroups.py lo hi outdir   (prints one name per line)"""
import sys, os, math
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import groups
lo, hi, out = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
os.makedirs(out, exist_ok=True)
names = []
for n in range(lo, hi + 1):
    names.append('cyc:%d' % n)
    for a in range(2, n):
        if n % a == 0 and a <= n // a and math.gcd(a, n // a) > 1 and (n // a) % a == 0: names.append('prod:%d:%d' % (a, n // a))
    if n % 2 == 0 and n // 2 >= 3: names.append('dih:%d' % (n // 2))
    if n % 4 == 0 and n // 4 >= 2: names.append('dic:%d' % (n // 4))
    for m in range(3, n):
        if n % m: continue
        k = n // m
        if k < 2: continue
        seen = set()
        for t in range(2, m):
            if math.gcd(t, m) != 1 or pow(t, k, m) != 1: continue
            sub = frozenset(pow(t, e, m) for e in range(k))
            if sub in seen: continue
            seen.add(sub)
            if k == 2 and t == m - 1: continue          # dihedral, already listed
            names.append('meta:%d:%d:%d' % (m, k, t))
for nm in names:
    fn = os.path.join(out, nm.replace(':', '_') + '.txt')
    if not os.path.exists(fn):
        T = groups.make(nm)
        with open(fn, 'w') as f:
            f.write('%d\n' % len(T)); f.write(' '.join(str(x) for row in T for x in row) + '\n')
    print(nm, fn)
