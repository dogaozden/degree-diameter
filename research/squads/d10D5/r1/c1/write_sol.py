"""write_sol.py SOL0 FOUND OUTSOL: FOUND is flagls output (FLAGS k p:l ... / SIGMA ...). Verifies the perfect matching with
flaggreedy's matching() (sigma must be an allowed perfect matching), then writes OUTSOL (lift2 DM format, sigma twice,
mv0 = 1s, mv1 = 4s, nu copied from SOL0) and OUTSOL.free, exactly as flaggreedy.py does at its end."""
import sys
SOL0, FOUND, OUTSOL = sys.argv[1:4]
sys.argv = ['flaggreedy.py', 'gq/gq_q7.bin', '1', '0']
src = open('flaggreedy.py').read().split('flags = []')[0]
exec(compile(src, 'flaggreedy_head', 'exec'))
lines_txt = open(FOUND).read().split('\n')
fl_tok = [t for t in lines_txt[0].split()][2:]
flags = [tuple(map(int, t.split(':'))) for t in fl_tok]
sigma = list(map(int, lines_txt[1].split()[1:]))
sz, mL = matching(flags)
print('k', len(flags), 'python matching', sz, 'of', N)
assert sz == N and sorted(sigma) == list(range(N))
assert all(sigma[p] == l for p, l in flags)
# check the sigma respects every allowed pair
for x in range(N):
    if x in dict(flags): continue
    M = sigma[x]
    for p, l in flags:
        if x in set(perp(lines, lof, p)) - set(lines[l]): assert M in set(lperp(lines, lof, l)) - {l}, ('A', x, M)
        if M in set(lperp(lines, lof, l)) - set(lof[p]): assert x in set(perp(lines, lof, p)) - {p}, ('G', x, M)
print('sigma verified against the exact-coverage conditions')
tok = open(SOL0).read().split(); nu = tok[7 + 4 * N:7 + 4 * N + N * (q + 1)]
assert len(nu) == N * (q + 1)
with open(OUTSOL, 'w') as f:
    f.write(f'{q} 2 6 7 0\ncyc 6\n'); s = ' '.join(map(str, sigma)); f.write(s + '\n' + s + '\n')
    f.write(' '.join(['1'] * N) + '\n' + ' '.join(['4'] * N) + '\n' + ' '.join(nu) + '\n')
with open(OUTSOL + '.free', 'w') as f: f.write(' '.join(str(p) for p, l in flags) + '\n')
print('wrote', OUTSOL, 'and', OUTSOL + '.free', '; free points:', open(OUTSOL + '.free').read().strip())
