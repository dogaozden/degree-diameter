# Exhaustive 2+2 scan of one group G (order N) over base b22_cubic: voltages (0,a,0,0,b,c), a restricted to
# conjugacy-class representatives (complete: simultaneous conjugation is a relabelling of the lift).
import sys, subprocess, time, numpy as np
T_ = '/home/user/degree-diameter/research/squads/b48/tools'
sys.path.insert(0, T_)
import groups as G

def load_bin(path):
    with open(path, 'rb') as f:
        N = int(np.fromfile(f, dtype=np.int32, count=1)[0])
        return np.fromfile(f, dtype=np.uint16, count=N * N).reshape(N, N)

def class_reps(T):
    N = len(T)
    invs = np.array([int(np.where(T[g] == 0)[0][0]) for g in range(N)])
    seen = np.zeros(N, bool); reps = []
    for a in range(N):
        if seen[a]: continue
        reps.append(a)
        c = T[T[:, a], invs]  # g a g^-1 : T[T[g,a], inv(g)]
        seen[c] = True
    return reps

def run(binpath, limit=2):
    T = load_bin(binpath); N = len(T)
    reps = class_reps(T)
    t0 = time.time()
    lines = []
    for a in reps:
        for b in range(N):
            lines.append(np.column_stack([np.zeros(N, int), np.full(N, a), np.zeros(N, int), np.zeros(N, int), np.full(N, b), np.arange(N)]))
    arr = np.vstack(lines)
    data = '\n'.join(' '.join(map(str, r)) for r in arr.tolist()) + '\n'
    env = {'LIMIT': str(limit), 'ONLYLOW': '1', 'PATH': '/usr/bin:/bin'}
    p = subprocess.run([f'{T_}/flift', f'{T_}/bases/cubic/b22_cubic.txt', binpath, '3', '10', 'eval'],
                       input=data.encode(), capture_output=True, env=env, timeout=280)
    res = p.stdout.decode()
    err = p.stderr.decode().strip()
    best = [l for l in res.splitlines() if l.strip()]
    return dict(N=N, reps=len(reps), lines=len(arr), err=err, secs=round(time.time() - t0, 1), hits=best[:20])

if __name__ == '__main__':
    print(run(sys.argv[1]))
