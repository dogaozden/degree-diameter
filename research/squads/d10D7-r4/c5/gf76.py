# GF(7^6) via log/exp tables; elements are base-7 codes of coefficient vectors (poly basis 1,x,..,x^5).
import numpy as np, random, sys
p, n = 7, 6
Q6 = p**n            # 117649
M = Q6 - 1           # 117648
def build(f):        # f = [f0..f5], x^6 = -(f0 + f1 x + ... + f5 x^5)
    pw = np.array([p**i for i in range(n)], dtype=np.int64)
    exp = np.zeros(M, dtype=np.int64)
    v = [1, 0, 0, 0, 0, 0]
    seen = set()
    for k in range(M):
        code = sum(v[i] * p**i for i in range(n))
        if code in seen:
            return None
        seen.add(code)
        exp[k] = code
        top = v[5]
        v = [0] + v[:5]
        v = [(v[i] - top * f[i]) % p for i in range(n)]
    return exp
def find_primitive(seed=1):
    rng = random.Random(seed)
    while True:
        f = [rng.randrange(p) for _ in range(n)]
        if f[0] == 0:
            continue
        exp = build(f)
        if exp is not None:
            return f, exp
if __name__ == '__main__':
    f, exp = find_primitive(int(sys.argv[1]) if len(sys.argv) > 1 else 1)
    print('f', f)
    np.save('/home/user/degree-diameter/research/squads/d10D7-r4/c5/gf76_exp.npy', exp)
    np.save('/home/user/degree-diameter/research/squads/d10D7-r4/c5/gf76_f.npy', np.array(f))
    print('ok', exp[:8], exp[M-1])
