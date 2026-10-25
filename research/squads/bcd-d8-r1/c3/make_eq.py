# make an init .sol with equal jump voltages on sigma_1 and sigma_2 (orbit-wise), optionally equal shifts t too
import sys
src, dst, mode = sys.argv[1], sys.argv[2], sys.argv[3]   # mode: va (equal voltages) | vat (equal voltages and shifts)
lines = open(src).read().split('\n')
out = []
sig = []
for ln in lines:
    if ln.startswith('sigma '):
        sig.append(ln)
    out.append(ln)
def parse(ln):
    w = ln.split()
    return w[:2], [int(x) for x in w[2:]]
h0, a0 = parse(sig[0]); h1, a1 = parse(sig[1])
NO = len(a0) // 3
new1 = []
for o in range(NO):
    pi, t, va = a0[3*o:3*o+3]
    pi1, t1, va1 = a1[3*o:3*o+3]
    if mode == 'vat':
        t1 = t
    va1 = va
    new1 += [pi1, t1, va1]
out = [l if not l.startswith('sigma 1') else 'sigma 1 ' + ' '.join(map(str, new1)) for l in out]
open(dst, 'w').write('\n'.join(out))
