import sys
def isp(x):
    if x < 2: return False
    i = 2
    while i * i <= x:
        if x % i == 0: return False
        i += 1
    return True
def order(r, m):
    x, o = r % m, 1
    while x != 1 % m: x = x * r % m; o += 1
    return o
# keep pairs where each factor has m prime, k prime, ord(r) = k
for line in open(sys.argv[1]):
    N, a, b = line.split('|')
    fa = list(map(int, a.split())); fb = list(map(int, b.split()))
    ok = all(isp(m) and isp(k) and order(r, m) == k for m, k, r in (fa, fb))
    if ok: print(line.strip())
