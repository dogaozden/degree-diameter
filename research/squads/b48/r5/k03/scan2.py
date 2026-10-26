# second parity pass: groups Z_m x|_r Z_k with m even, r odd; homs chi = a mod 2 (H1) or (a + j) mod 2 (H2)
import subprocess, sys, os
T = '/home/user/degree-diameter/research/squads/b48/tools'
base = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'base_loops.txt')
env = dict(os.environ, THREADS='1', NOTREE='1', LIMIT='30', QUIET='1')
out = open(sys.argv[1], 'w')
rows = [tuple(map(int, l.split())) for l in open(sys.argv[2])]
for N, m, k, r in rows:
    for hname in ('H1', 'H2'):
        odd = []
        for j in range(k):
            for a in range(m):
                chi = (a if hname == 'H1' else a + j) % 2
                if chi == 1: odd.append(a + m * j)
        lines = [f"0 {g0} {g1}\n" for g0 in odd for g1 in odd]
        p = subprocess.run(['timeout', '120', 'nice', '-n', '10', f'{T}/lift', base, f'meta:{m}:{k}:{r}', '3', '10', 'eval'],
                           input=''.join(lines), capture_output=True, text=True, env=env)
        vals = [v for v in p.stdout.split('\n') if v and v != 'invalid']
        best = min((int(v) for v in vals), default=None)
        out.write(f"{2*N} {N} {m} {k} {r} hom={hname} best={best} npairs={len(lines)} rc={p.returncode} err={p.stderr.strip()[:80]}\n")
        out.flush()
