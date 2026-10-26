import sys, subprocess, numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/squads/b48/r4/h01')
import scan
T_ = '/home/user/degree-diameter/research/squads/b48/tools'
nm = sys.argv[1]
binp = f'/home/user/degree-diameter/research/squads/b48/r4/h01/groups/{nm}.bin'
T = scan.load_bin(binp); N = len(T)
reps = scan.class_reps(T)
volt = np.array([(0, a, 0, 0, b, c) for a in reps for b in range(N) for c in range(N)])
data = '\n'.join(' '.join(map(str, r)) for r in volt.tolist()) + '\n'
env = {'PATH': '/usr/bin:/bin'}
p = subprocess.run([f'{T_}/flift', f'{T_}/bases/cubic/b22_cubic.txt', binp, '3', '10', 'eval'], input=data.encode(), capture_output=True, env=env, timeout=200)
costs = np.array([int(x) if x.isdigit() else 10**9 for x in p.stdout.decode().split()])
mn = costs.min(); idx = np.where(costs == mn)[0]
print(nm, 'exact min', mn, 'count at min', len(idx), 'example volt', volt[idx[0]].tolist(), 'N', N, flush=True)
np.save(f'/home/user/degree-diameter/research/squads/b48/r4/h01/{nm}_argmin.npy', volt[idx[:20]])
