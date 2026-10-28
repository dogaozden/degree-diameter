# Audit item (6): Corollary 3.4 inequality, and its chain, against every line of scan/lps_p*.txt (own arithmetic).
import re, glob, math
import qlib as L
def first_kv(line):
    kv = {}
    for k, v in re.findall(r'(\w+)=([^\s()]+)', line):
        kv.setdefault(k, v)
    return kv
disc = []; n_lines = 0; fails = []
for f in sorted(glob.glob('/home/user/degree-diameter/research/theorems/haar_families/scan/lps_p*.txt')):
    for line in open(f):
        if not line.startswith('p='): continue
        kv = first_kv(line)
        p = int(kv['p']); q = int(kv['q']); m = int(kv['m']); Dl = int(kv['Delta']); n = int(kv['vertices']); D = int(kv['diameter'])
        n_lines += 1
        # sanity: Delta = p+1, vertices = q(q^2-1) for m=1
        bad = []
        if Dl != p + 1: bad.append('Delta')
        if n != q*(q*q-1)*m: bad.append('vertices!=q(q^2-1)m')
        Mb = 2 * sum(p**j for j in range(D))          # M^b(p+1, D) = 2 sum_{j<D} (Delta-1)^j
        lhs = n
        rhs = math.sqrt(2) * p**(1 - D/4) * Mb
        if not (lhs < rhs): bad.append('Cor3.4 n<sqrt2 p^(1-D/4) Mb')
        if not (q*q < 2 * p**(D//2)): bad.append('q^2<2p^floor(D/2)')
        if not (n < 2**1.5 * p**(1.5*(D//2))): bad.append('n<2^1.5 p^(3/2 floor(D/2))')
        if not (n < 2**1.5 * p**(3*D/4)): bad.append('n<2^1.5 p^(3D/4)')
        if m != 1 and True: pass
        if bad:
            fails.append((f.split('/')[-1], line.strip()[:110], bad))
        # ratio report
        if bad == []:
            pass
print("lines checked:", n_lines)
print("failing lines:", len(fails))
for x in fails[:20]: print(x)
# the strongest margin: max of n / (sqrt2 p^(1-D/4) Mb)
best = None
for f in sorted(glob.glob('/home/user/degree-diameter/research/theorems/haar_families/scan/lps_p*.txt')):
    for line in open(f):
        if not line.startswith('p='): continue
        kv = first_kv(line)
        p=int(kv['p']); q=int(kv['q']); n=int(kv['vertices']); D=int(kv['diameter'])
        Mb = 2*sum(p**j for j in range(D))
        r = n/(math.sqrt(2)*p**(1-D/4)*Mb)
        if best is None or r > best[0]: best = (r, p, q, D, n)
print("max ratio n/bound = %.4f at p=%d q=%d D=%d n=%d" % (best[0], best[1], best[2], best[3], best[4]))
print("DISCREPANCIES (d):", len(fails))
