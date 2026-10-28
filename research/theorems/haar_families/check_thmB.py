# Theorem B check: d((e,A),(psi(i),A)) versus L0 = least even L with 2 p^(L/2) > q^2, for every prime q > p.
import subprocess, re, sys
def isprime(n): return n > 1 and all(n % d for d in range(2, int(n**.5)+1))
P = [int(x) for x in sys.argv[1].split(",")]; QMAX = int(sys.argv[2]); QMIN = int(sys.argv[3]) if len(sys.argv) > 3 else 0
for p in P:
    for q in range(max(p+1, QMIN), QMAX+1):
        if not isprime(q): continue
        out = subprocess.run(['./lps_haar', str(p), str(q)], capture_output=True, text=True).stdout
        m = re.search(r'd\(e,psi\(i\)\)=(-?\d+) d\(e,psi\(j\)\)=(-?\d+) d\(e,psi\(k\)\)=(-?\d+).*thmB_bound=\S+\s+ecc=(\d+)', out)
        di, dj, dk, ecc = map(int, m.groups())
        L0 = 0
        while not (2 * p**(L0//2) > q*q): L0 += 2
        tag = 'EQUAL' if di == L0 else ('ABOVE' if di > L0 else 'BELOW!!')
        print(f"p={p} q={q} d(psi i,j,k)={di},{dj},{dk} L0={L0} {tag} ecc={ecc} ecc-L0={ecc-L0}")
