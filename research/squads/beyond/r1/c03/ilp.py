"""Exact-ish max of |M| by HiGHS MIP. usage: python3 ilp.py INST SECONDS OUT  (OUT: k then line indices)"""
import sys
import numpy as np
HERE = sys.argv[0].rsplit('/', 1)[0] if '/' in sys.argv[0] else '.'
sys.path.insert(0, HERE + '/pylib')
import highspy  # noqa: E402

inst, secs, outf = sys.argv[1], float(sys.argv[2]), sys.argv[3]
with open(inst) as f:
    N, M, NO = map(int, f.readline().split())
    ov = set(map(int, f.readline().split()))
    lines = [list(map(int, f.readline().split())) for _ in range(M)]
cap = [2 if p in ov else 1 for p in range(N)]
h = highspy.Highs()
h.setOptionValue('output_flag', False)
h.setOptionValue('time_limit', secs)
h.setOptionValue('threads', 1)
inf = highspy.kHighsInf
h.addVars(M, np.zeros(M), np.ones(M))
h.changeColsCost(M, np.arange(M, dtype=np.int32), -np.ones(M))
h.changeColsIntegrality(M, np.arange(M, dtype=np.int32), np.array([highspy.HighsVarType.kInteger] * M))
# rows: one per point, sum over lines through point <= cap
on = [[] for _ in range(N)]
for j, L in enumerate(lines):
    for p in L:
        on[p].append(j)
starts, idx, vals = [], [], []
for p in range(N):
    starts.append(len(idx))
    idx.extend(on[p]); vals.extend([1.0] * len(on[p]))
h.addRows(N, np.full(N, -inf), np.array(cap, dtype=float), len(idx), np.array(starts, dtype=np.int32),
          np.array(idx, dtype=np.int32), np.array(vals))
h.run()
sol = h.getSolution().col_value
x = [j for j in range(M) if sol[j] > 0.5]
info = h.getInfo()
print(f'|M|={len(x)} status={h.modelStatusToString(h.getModelStatus())} bound={info.mip_dual_bound:.2f}', flush=True)
with open(outf, 'w') as g:
    g.write(f'{len(x)}\n' + ''.join(f'{j}\n' for j in x))
