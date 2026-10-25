"""Convert between fibre-model states (lines 'F s b c f' and 'P x1 x2 x3 x6 level') and H(11) point indices.
usage: fibconv.py model2idx MODEL_FILE OUT_IDX      |  fibconv.py idx2model IDX_FILE OUT_MODEL"""
import sys, numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/d13D7/tools')
import hexlib
q, lines, coord = hexlib.load('/home/user/degree-diameter/research/d13D7/hex/hex_q11.bin')
code = coord @ (q ** np.arange(7))
def idx_of(x):
    x = np.array(x) % q
    nz = np.nonzero(x)[0][0]
    x = (x * pow(int(x[nz]), q - 2, q)) % q
    k = int(x @ (q ** np.arange(7)))
    j = int(np.searchsorted(code, k))
    assert code[j] == k, ('not a point', x)
    return j
def model2idx(path):
    fib, inf = [], []
    for line in open(path):
        t = line.split()
        if not t or t[0] == '#': continue
        if t[0] == 'F': fib.append(tuple(int(z) for z in t[1:5]))
        if t[0] == 'P': inf.append(tuple(int(z) for z in t[1:6]))
    out = set()
    for (s, b, c, f) in fib:
        for lam in range(q):
            a = lam; e = (s + 9 * lam) % q
            out.add(idx_of([1, a, b, c, (c * c - a * e - b * f) % q, e, f]))
    for (x1, x2, x3, x6, level) in inf:
        out.add(idx_of([0, x1, x2, x3, level, (2 * x1) % q, x6]))
    return sorted(out), len(fib), len(inf)
def idx2model(path):
    idx = [int(l) for l in open(path) if l.strip() and not l.startswith('#')]
    fib = {}; inf = []
    for j in idx:
        x = coord[j].tolist()
        if x[0] == 1:
            a, b, c, e, f = x[1], x[2], x[3], x[5], x[6]
            lam = (-a) % q
            s = (e + 9 * lam) % q          # fibre representative with a = 0: e = s
            fib.setdefault((s, b, c, f), set()).add(a)
        else:
            inf.append((x[1], x[2], x[3], x[6], x[4]))
    return fib, inf
if __name__ == '__main__':
    if sys.argv[1] == 'model2idx':
        idx, nf, ni = model2idx(sys.argv[2])
        with open(sys.argv[3], 'w') as f:
            f.write(f'# {len(idx)} points: {nf} fibres x 11 + {ni} infinity points (fibre model)\n' + '\n'.join(map(str, idx)) + '\n')
        print(len(idx), 'points written')
    else:
        fib, inf = idx2model(sys.argv[2])
        with open(sys.argv[3], 'w') as f:
            for (s, b, c, ff) in sorted(fib):
                f.write(f'F {s} {b} {c} {ff}\n')
            for (x1, x2, x3, x6, lev) in inf:
                f.write(f'P {x1} {x2} {x3} {x6} {lev}\n')
        print('fibres', len(fib), 'infinity', len(inf), 'partial fibres', sum(1 for v in fib.values() if len(v) != 11))
