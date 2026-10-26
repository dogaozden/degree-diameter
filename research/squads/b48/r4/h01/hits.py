import sys
sys.path.insert(0, '/home/user/degree-diameter/research/squads/b48/r4/h01')
import scan, subprocess, os
T_ = '/home/user/degree-diameter/research/squads/b48/tools'
for nm in sys.argv[2:]:
    binp = f'/home/user/degree-diameter/research/squads/b48/r4/h01/groups/{nm}.bin'
    T = scan.load_bin(binp); N = len(T)
    reps = scan.class_reps(T)
    import numpy as np
    arr = np.vstack([np.column_stack([np.zeros(N, int), np.full(N, a), np.zeros(N, int), np.zeros(N, int), np.full(N, b), np.arange(N)]) for a in reps for b in range(N)])
    data = '\n'.join(' '.join(map(str, r)) for r in arr.tolist()) + '\n'
    env = {'LIMIT': sys.argv[1], 'ONLYLOW': '1', 'PATH': '/usr/bin:/bin'}
    p = subprocess.run([f'{T_}/flift', f'{T_}/bases/cubic/b22_cubic.txt', binp, '3', '10', 'eval'], input=data.encode(), capture_output=True, env=env, timeout=120)
    hits = [l for l in p.stdout.decode().splitlines() if l.strip()]
    print(nm, p.stderr.decode().strip(), len(hits), hits[:4], flush=True)
