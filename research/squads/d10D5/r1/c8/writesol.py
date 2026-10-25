"""writesol.py LOG OUT.sol: take FLAGS and SIGMA lines of an lsearch.py log and write the lift2/dmfast sol
(sigma twice, mv0 all 1, mv1 all 4, nu copied from SOL0) plus OUT.sol.free, as flaggreedy.py does."""
import sys
log, out = sys.argv[1], sys.argv[2]
SOL0 = '../../../../d10D7/graphs/d10D5_n4800_gqdm_q7.sol'
flags = None; sig = None
for line in open(log):
    if line.startswith('FOUND'):
        flags = line.split('FLAGS', 1)[1].split()
    if line.startswith('SIGMA'):
        sig = list(map(int, line.split()[1:]))
assert flags and sig
tok = open(SOL0).read().split(); q = 7; N = 400
nu = tok[7 + 4 * N:7 + 4 * N + N * (q + 1)]
assert len(nu) == N * (q + 1), len(nu)
with open(out, 'w') as f:
    f.write(f'{q} 2 6 7 0\ncyc 6\n'); s = ' '.join(map(str, sig)); f.write(s + '\n' + s + '\n')
    f.write(' '.join(['1'] * N) + '\n' + ' '.join(['4'] * N) + '\n' + ' '.join(nu) + '\n')
with open(out + '.free', 'w') as f:
    f.write(' '.join(fl.split(':')[0] for fl in flags) + '\n')
print('wrote', out, 'free', ' '.join(fl.split(':')[0] for fl in flags))
