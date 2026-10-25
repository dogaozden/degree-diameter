"""write_partial.py FLAGLS_OUT OUT.sol: flagls2 output (FLAGS k p:l ..., DEF d, SIGMA ... completed to a bijection) ->
lift2/dmfast sol (sigma twice, mv0 = 1, mv1 = 4, nu copied from the 4,800 graph) plus OUT.sol.free. Deficiency is
not required to be 0: coverage is then repaired by dmhub COVIT and the relaxed-coverage sigma swaps."""
import sys
src, out = sys.argv[1], sys.argv[2]
SOL0 = '../../../../d10D7/graphs/d10D5_n4800_gqdm_q7.sol'
flags = None; sig = None; de = None
for line in open(src):
    if line.startswith('FLAGS'): flags = line.split()[2:]
    if line.startswith('SIGMA'): sig = list(map(int, line.split()[1:]))
    if line.startswith('DEF'): de = int(line.split()[1])
assert flags and sig and len(sig) == 400 and sorted(sig) == list(range(400)), 'bad sigma (not a bijection)'
fl = [tuple(map(int, t.split(':'))) for t in flags]
for p, l in fl: assert sig[p] == l, ('freed point not on its line', p, l)
tok = open(SOL0).read().split(); q = 7; N = 400
nu = tok[7 + 4 * N:7 + 4 * N + N * (q + 1)]
assert len(nu) == N * (q + 1), len(nu)
with open(out, 'w') as f:
    f.write(f'{q} 2 6 7 0\ncyc 6\n'); s = ' '.join(map(str, sig)); f.write(s + '\n' + s + '\n')
    f.write(' '.join(['1'] * N) + '\n' + ' '.join(['4'] * N) + '\n' + ' '.join(nu) + '\n')
with open(out + '.free', 'w') as f:
    f.write(' '.join(str(p) for p, l in fl) + '\n')
print('wrote', out, 'deficiency', de, 'free', ' '.join(str(p) for p, l in fl))
