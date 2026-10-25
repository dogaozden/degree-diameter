# badsrc.py BASE D OUT: list the base-vertex sources with uncovered pairs (bisection over SRCFILE chunks, exact).
import subprocess, sys, os
BIN = '/home/user/degree-diameter/research/d16D8/baselift'
base, D, out = sys.argv[1], sys.argv[2], sys.argv[3]
V = int(open(base).readline().split()[0])
tmp = out + '.src'
def uncov(srcs):
    with open(tmp, 'w') as f:
        f.write('\n'.join(map(str, srcs)) + '\n')
    r = subprocess.run([BIN, 'eval', base, D], env=dict(os.environ, SRCFILE=tmp, THREADS='1'),
                       capture_output=True, text=True)
    return int(r.stdout.split('uncovered=')[1].split()[0])
def bad(srcs):
    if not srcs or uncov(srcs) == 0:
        return []
    if len(srcs) == 1:
        return srcs
    h = len(srcs) // 2
    return bad(srcs[:h]) + bad(srcs[h:])
b = bad(list(range(V)))
open(out, 'w').write('\n'.join(map(str, b)) + '\n')
print('bad sources:', len(b), b[:20])
