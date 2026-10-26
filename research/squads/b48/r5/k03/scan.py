# exhaustive scan of loop-voltage pairs (g0, g1), both odd (chi = j mod 2), edge voltage e (WLOG by switching at side 1)
import subprocess, sys, os
T = '/home/user/degree-diameter/research/squads/b48/tools'
LIFT = f'{T}/lift'
base = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'base_loops.txt')
env = dict(os.environ, THREADS='1', NOTREE='1', LIMIT=sys.argv[3] if len(sys.argv) > 3 else '30', QUIET='1')
groups_file = sys.argv[1]
out = open(sys.argv[2], 'w')
rows = [tuple(map(int, l.split())) for l in open(groups_file)]
if len(sys.argv) > 4:
    a, b = map(int, sys.argv[4].split(':'))
    rows = rows[a:b]
for N, m, k, r in rows:
    odd = [a + m * j for j in range(1, k, 2) for a in range(m)]
    lines = []
    for g0 in odd:
        for g1 in odd:
            lines.append(f"0 {g0} {g1}\n")
    inp = ''.join(lines)
    gs = f'meta:{m}:{k}:{r}'
    p = subprocess.run(['timeout', '120', 'nice', '-n', '10', LIFT, base, gs, '3', '10', 'eval'],
                       input=inp, capture_output=True, text=True, env=env)
    vals = [l for l in p.stdout.split('\n') if l]
    best = None; bi = None; cnt = {}
    for idx, v in enumerate(vals):
        if v == 'invalid': continue
        c = int(v)
        if best is None or c < best:
            best = c; bi = idx
    if bi is not None:
        g0, g1 = odd[bi // len(odd)], odd[bi % len(odd)]
    else:
        g0 = g1 = -1
    out.write(f"{2*N} {N} {m} {k} {r} best={best} g0={g0} g1={g1} npairs={len(lines)} rc={p.returncode} err={p.stderr.strip()[:80]}\n")
    out.flush()
