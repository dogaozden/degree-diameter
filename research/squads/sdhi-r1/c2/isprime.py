import sys
def isprime(n):
    if n < 2: return False
    i = 2
    while i * i <= n:
        if n % i == 0: return False
        i += 1
    return True
rows = []
for line in open(sys.argv[1]):
    p = line.split()
    if len(p) < 6: continue
    N, m, k, r, d, inv = map(int, p[:6])
    if isprime(m): continue
    if inv > 1: continue
    if d < 4: continue
    rows.append((N, m, k, r, d, inv))
for row in rows:
    print(*row)
print("count", len(rows), file=sys.stderr)
