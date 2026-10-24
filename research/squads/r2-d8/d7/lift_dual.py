"""Duality-hop lifts of H(q) at q=3: hops from dualities (or random non-incident bijections), Z_M voltages.

Usage: python3 -I lift_dual.py model q M seed [duals...]
  model rr  : two random non-incident bijections points->lines (baseline)
  model dr  : hop 1 = duality dual_q3_s<a>.npy, hop 2 = random non-incident bijection avoiding hop 1
  model dd  : hop 1 and hop 2 both dualities (given as file names); needs non-colliding dualities
Flags get uniform random Z_M voltages; hop voltages uniform random in Z_M.
Prints: model q M seed unreached max_ecc base_path
"""
import os, sys, subprocess
import numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/theorems/d8')
import gh

HERE = os.path.dirname(os.path.abspath(__file__))
LIFTDIAM = '/home/user/degree-diameter/research/theorems/d8/liftdiam'


def nonincident_bijection(N, H_nb, rng, avoid=None):
    """random bijection points->lines with p not incident to sigma(p) and sigma(p) != avoid[p]; rejection + repair"""
    for _ in range(100000):
        perm = rng.permutation(N)  # perm[p] = line index
        ok = True
        for p in range(N):
            L = perm[p]
            if L in H_nb[p] or (avoid is not None and avoid[p] == L):
                ok = False
                break
        if ok:
            return perm
    raise RuntimeError('no bijection')


def main():
    model = sys.argv[1]; q = int(sys.argv[2]); M = int(sys.argv[3]); seed = int(sys.argv[4])
    duals = sys.argv[5:]
    H = gh.load(q)
    N = H.N
    rng = np.random.default_rng(seed)
    H_nb = [set() for _ in range(N)]
    for k in range(N):
        for p in H.lines[k]:
            H_nb[int(p)].add(k)  # line indices (0..N-1) incident to point p
    if model == 'rr':
        s1 = nonincident_bijection(N, H_nb, rng)
        s2 = nonincident_bijection(N, H_nb, rng, avoid=s1)
    elif model == 'dr':
        d1 = np.load(os.path.join(HERE, duals[0]))
        s1 = np.array([int(d1[p]) - N for p in range(N)])
        s2 = nonincident_bijection(N, H_nb, rng, avoid=s1)
    elif model == 'dd':
        d1 = np.load(os.path.join(HERE, duals[0])); d2 = np.load(os.path.join(HERE, duals[1]))
        s1 = np.array([int(d1[p]) - N for p in range(N)])
        s2 = np.array([int(d2[p]) - N for p in range(N)])
    else:
        raise SystemExit('bad model')
    # count hop edges that duplicate an H-flag or each other
    dup = sum(1 for p in range(N) if s1[p] in H_nb[p]) + sum(1 for p in range(N) if s2[p] in H_nb[p])
    coll = sum(1 for p in range(N) if s1[p] == s2[p])
    edges = []
    for p in range(N):
        for L in H.lines[0:0]:
            pass
    for p, lv in gh.flags(H):
        a = int(rng.integers(M))
        edges.append((p, lv, a, 0))
    t1 = rng.integers(M, size=N); t2 = rng.integers(M, size=N)
    for p in range(N):
        edges.append((p, N + int(s1[p]), int(t1[p]), 0))
        edges.append((p, N + int(s2[p]), int(t2[p]), 0))
    name = f'bases/{model}_q{q}_M{M}_s{seed}.txt'
    os.makedirs(os.path.join(HERE, 'bases'), exist_ok=True)
    path = os.path.join(HERE, name)
    gh.write_base(path, 2 * N, M, 1, edges)
    out = subprocess.run([LIFTDIAM, path, '8', '1'], capture_output=True, text=True, timeout=800).stdout
    print(out.strip().replace('\n', ' | '), f'dup={dup} coll={coll}', sep=' || ')


if __name__ == '__main__':
    main()
