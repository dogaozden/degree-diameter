"""sol2lift2.py IN OUT: dmhub solution -> lift2/dmfast DM solution (sigma twice, mv0 = 1, mv1 = 4, flag voltages),
so dmhub (which reads the lift2 format) and dmfast_hub can continue from it; prints the freed points."""
import sys
rows = {}
for ln in open(sys.argv[1]):
    t = ln.split()
    if t: rows[t[0]] = t[1:]
sig, nu = rows['sigma'], rows['nu']; N = len(sig); q = int(rows['dmhub'][1])
with open(sys.argv[2], 'w') as f:
    f.write(f'{q} 2 6 7 0\ncyc 6\n' + ' '.join(sig) + '\n' + ' '.join(sig) + '\n' + ' '.join(rows['mv0']) + '\n'
            + ' '.join(rows['mv1']) + '\n' + ' '.join(nu) + '\n')
print(' '.join(rows.get('free', [])))
