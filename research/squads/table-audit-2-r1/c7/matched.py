#!/usr/bin/env python3
"""c7: labellings where every row's point and line are INCIDENT (distance 1) in every copy.
M = a g-equivariant perfect matching of the incidence graph of H(5) (orbit-level matching, see build_M).
Copy c: P_c[t] = point given by a closed-form map of the row t (sweep.py-style), L_c[t] = M(P_c[t])."""
import sys, os, subprocess
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import sweep as S
N, C, M_, R = S.N, S.C, S.M, S.R
sP, jP, MP, sL, jL, ML = S.sP, S.jP, S.MP, S.sL, S.jL, S.ML

inc = [[] for _ in range(N)]
lines = open(S.HEX).read().split('\n')
for ln in lines[1:]:
    if not ln.strip(): continue
    u, v = map(int, ln.split())
    if u < N <= v: inc[u].append(v - N)
    elif v < N <= u: inc[v].append(u - N)
# orbit-level bipartite graph: point orbit s -> (line orbit sigma, exponent e) through rep MP[s][0]
adj = [[] for _ in range(R)]
for s in range(R):
    x = MP[s][0]
    for y in inc[x]:
        adj[s].append((sL[y], jL[y]))
matchR = [None] * R; chosen = [None] * R
def aug(s, seen):
    for (sig, e) in adj[s]:
        if sig in seen: continue
        seen.add(sig)
        if matchR[sig] is None or aug(matchR[sig], seen):
            matchR[sig] = s; chosen[s] = (sig, e); return True
    return False
for s in range(R):
    assert aug(s, set()), 'no perfect orbit matching'
sig_of = [chosen[s][0] for s in range(R)]; e_of = [chosen[s][1] for s in range(R)]
Mi = [0] * N   # Mi[point] = matched line index
for s in range(R):
    for j in range(M_):
        Mi[MP[s][j]] = ML[sig_of[s]][(j + e_of[s]) % M_]
assert len(set(Mi)) == N
for x in range(N): assert Mi[x] in inc[x], 'not incident'
print('matching ok: every point incident to its matched line', file=sys.stderr)

def write(path, Pfun):
    """Pfun(c, t) -> point index for copy c, row t.  L_c[t] = Mi[P_c[t]]."""
    P = [0] * (C * N); L = [0] * (C * N)
    for c in range(C):
        for t in range(N):
            p = Pfun(c, t); P[c * N + t] = p; L[c * N + t] = Mi[p]
    with open(path, 'w') as f:
        for i in range(0, C * N, N): f.write(' '.join(map(str, P[i:i + N])) + '\n')
        for i in range(0, C * N, N): f.write(' '.join(map(str, L[i:i + N])) + '\n')

def run(name, Pfun, types='abab', inner='LLLL'):
    lab = os.path.join(S.HERE, 'lab', f'{name}.lab'); write(lab, Pfun)
    out = subprocess.run(['timeout', '900', 'nice', '-n', '10', S.EVAL, S.HEX, types, inner, lab, '8', 'hubs0'],
                         capture_output=True, text=True).stdout.strip()
    far = int(out.split('far(>8)=')[1].split()[0]); ecc = out.split('maxecc=')[1].split()[0]
    print(f'{name:28s} {types} {inner} far={far} maxecc={ecc}', flush=True)
    return far, lab

if __name__ == '__main__':
    mode = sys.argv[1]
    res = []
    if mode == 'id':        # same point and matched line in every copy (thesis-like, distance-1 pairs)
        res.append(run('mat_id', lambda c, t: t))
    elif mode == 'shift':   # point orbit shift per copy, row stays in its orbit position
        for d in map(int, sys.argv[2].split(',')):
            res.append(run(f'mat_shift_d{d}', lambda c, t, d=d: MP[(sP[t] + c * d) % R][jP[t]]))
    elif mode == 'exp':     # g-exponent linear in c*s
        for a in map(int, sys.argv[2].split(',')):
            res.append(run(f'mat_exp_a{a}', lambda c, t, a=a: MP[sP[t]][(jP[t] + a * c * sP[t]) % M_]))
    elif mode == 'mult':    # orbit multiplier per copy
        U = S.UNITS
        for k in map(int, sys.argv[2].split(',')):
            res.append(run(f'mat_mult_k{k}', lambda c, t, k=k: MP[(U[(c * k) % len(U)] * sP[t]) % R][jP[t]]))
    if res: print('BEST', min(res))
