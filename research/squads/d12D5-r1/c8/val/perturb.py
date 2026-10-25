import subprocess, sys
G = '/home/user/degree-diameter/research/d12D5/graphs/'
CTRL = G + 'd12D5_n10692_k33m_z22e_controller.txt'
rows = [list(map(int, l.split())) for l in open(G + 'd12D5_n10692_k33m_z22e_echart.txt') if l.strip()]
res = []
for e in range(12):
    for t in range(20):
        r = [list(x) for x in rows]
        r[e][t] = (r[e][t] + 1) % 3
        fn = f'/home/user/degree-diameter/research/squads/d12D5-r1/c8/val/p_{e}_{t}.echart'
        with open(fn, 'w') as f:
            f.write('\n'.join(' '.join(map(str, x)) for x in r) + '\n')
        p = subprocess.run(['/home/user/degree-diameter/research/squads/d12D5-r1/c8/exact_cover', CTRL, fn, '22'],
                             capture_output=True, text=True, timeout=60)
        out = p.stdout
        if 'uncovered' not in out:
            print(e, t, 'ERROR', p.returncode, p.stderr.strip(), flush=True); continue
        unc = int([l for l in out.splitlines() if l.startswith('uncovered')][0].split('=')[1].split()[0])
        pc = int([l for l in out.splitlines() if l.startswith('pair_cost')][0].split('=')[1].split()[0])
        res.append((e, t, unc, pc))
        print(e, t, 'uncovered', unc, 'pair_cost', pc, flush=True)
