# Test of the s.2.4 universal group U = (Z[x]/(x^o-1))^d  x|  Z^d for G = Z_m x|_r Z_k, d = Delta-1.
import random
m, r, k = 7, 2, 6            # G = Z_7 x|_2 Z_6, o = ord_7(2) = 3 divides k
o = 3
def gmul(g, h):              # G product (a,j)(b,l) = (a + r^j b, j + l)
    return ((g[0] + pow(r, g[1], m) * h[0]) % m, (g[1] + h[1]) % k)
def shift(vec, t):           # x^t . vec in Z[C_o]
    t %= o
    return [vec[(c - t) % o] for c in range(o)]
def umul(U, V, jpart, mode):  # (P,n)(Q,n') = (P + x^{theta(n)} Q, n + n')
    P, n = U; Q, nn = V
    th = theta(n, jpart, mode)
    newP = [[P[i][c] + shift(Q[i], th)[c] for c in range(o)] for i in range(len(P))]
    return (newP, tuple(a + b for a, b in zip(n, nn)))
def theta(n, jpart, mode):
    if mode == 'correct':    # e_i acts by x^{j_i}
        return sum(a * b for a, b in zip(n, jpart))
    return sum(n)            # naive: every generator acts by x
def phi(U, avec):            # phi(P,n) = (sum_i a_i P_i(r), theta(n) mod k)
    P, n = U
    a = sum(avec[i] * sum(P[i][c] * pow(r, c, m) for c in range(o)) for i in range(len(P))) % m
    return (a, None if n is None else None)
def phi_full(U, avec, jpart, mode):
    P, n = U
    a = sum(avec[i] * sum(P[i][c] * pow(r, c, m) for c in range(o)) for i in range(len(P))) % m
    return (a, theta(n, jpart, mode) % k)
def ident(d):
    return ([[0] * o for _ in range(d)], tuple([0] * d))
def gen(i, d):              # u_i = (eps_i, e_i)
    P = [[0] * o for _ in range(d)]; P[i][0] = 1
    n = [0] * d; n[i] = 1
    return (P, tuple(n))
def uinv(U, jpart, mode):   # inverse (P,n)^{-1} = (-x^{-theta(n)} P, -n)
    P, n = U; th = theta(n, jpart, mode)
    return ([[-v for v in shift(P[i], -th)] for i in range(len(P))], tuple(-a for a in n))
random.seed(1)
trials = 2000; bad = {'correct': 0, 'naive': 0}; maxabs = 0; maxl1 = 0; ok_bounds = True
D = 7
for trial in range(trials):
    d = 2
    jpart = [random.randrange(k) for _ in range(d)]
    avec = [random.randrange(m) for _ in range(d)]
    S = [(avec[i], jpart[i]) for i in range(d)]           # s_i = (a_i, j_i); identity is s_0
    for mode in ('correct', 'naive'):
        U = ident(d); g = (0, 0)
        word = []
        for step in range(D):
            i = random.randrange(d); sgn = random.choice([1, -1])
            word.append((i, sgn))
            ui = gen(i, d)
            if sgn < 0:
                ui = uinv(ui, jpart, mode)
            # G element of the same letter
            sg = S[i] if sgn > 0 else None
            if sgn < 0:
                # inverse of s_i in G
                a, j = S[i]
                inv = ((-pow(r, (-j) % k, m) * a) % m, (-j) % k)
                sg = inv
            U = umul(U, ui, jpart, mode)
            g = gmul(g, sg)
        if phi_full(U, avec, jpart, mode) != g:
            bad[mode] += 1
        if mode == 'correct':
            P, n = U
            maxl1 = max(maxl1, sum(abs(a) for a in n))
            maxabs = max(maxabs, max(abs(v) for Pi in P for v in Pi))
            ok_bounds = ok_bounds and sum(abs(v) for Pi in P for v in Pi) <= D and sum(abs(a) for a in n) <= D
print('mismatches of phi(word) vs G-product over', trials, 'random words of length', D, ':', bad)
print('correct action: max |n|_1 =', maxl1, ' max |coeff| =', maxabs, ' all bounds (sum|P| <= D, |n|_1 <= D):', ok_bounds)
