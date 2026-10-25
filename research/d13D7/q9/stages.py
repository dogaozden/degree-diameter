# stage counts of tovoid9's DFS, in Python (independent re-implementation)
F = [(a, b) for b in range(3) for a in range(3)]  # index a+3b
def add(x, y): return ((x % 3 + y % 3) % 3) + 3 * ((x // 3 + y // 3) % 3)
def mul(x, y):
    a, b, c, d = x % 3, x // 3, y % 3, y // 3
    return (a * c + 2 * b * d) % 3 + 3 * ((a * d + b * c) % 3)
SQ = [mul(t, t) for t in range(9)]
cube = [mul(t, mul(t, t)) for t in range(9)]
LIN = [[add(mul(g % 9, t), mul(g // 9, cube[t])) for t in range(9)] for g in range(81)]
s1 = [g for g in range(81) if all(mul(a, LIN[g][a]) != 0 for a in range(1, 9))]
print('stage1 (Ea or Fb bijective-type):', len(s1))
pairs = [(Ea, Ec) for Ea in s1 for Ec in range(81) if all(SQ[c] != mul(a, add(LIN[Ea][a], LIN[Ec][c])) for a in range(1, 9) for c in range(9))]
print('stage3 (Ea,Ec) pairs:', len(pairs))
# sanity: Ea(a) = nu*a with nu a non-square, Ec = 0 must pass (Q(4,9) elliptic ovoid)
nonsq = [t for t in range(1, 9) if t not in SQ]
print('non-squares of F_9:', nonsq, ' squares:', sorted(set(SQ) - {0}))
print('sanity (nu a, 0) in pairs:', all(((nu, 0) in pairs) for nu in nonsq))
