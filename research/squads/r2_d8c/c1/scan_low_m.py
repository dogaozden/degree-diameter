"""c1: find one random axis with 739 axis points (degenerate cone type, the rand0 class) and scan m = 14..21."""
import importlib.util, json, numpy as np
spec = importlib.util.spec_from_file_location('ax', '/home/user/degree-diameter/research/squads/r2_d8c/c1/axis_study.py')
ax = importlib.util.module_from_spec(spec); spec.loader.exec_module(ax)
rng = np.random.default_rng(777)
found = None
for t in range(300):
    a = rng.integers(0, 9, 7); a2 = rng.integers(0, 9, 7)
    F1 = ax.bvec(a, ax.C); F2 = ax.bvec(a2, ax.C)
    if int(((F1 == 0) & (F2 == 0)).sum()) == 739:
        found = (a, a2); break
print('found after', t + 1, 'tries', flush=True)
a, a2 = found
c, F1, F2 = ax.pencil_c(a, a2, np.random.default_rng(7))
print('stats', ax.stats(F1, F2), 'class', ax.class_of_pair(a, a2), flush=True)
out = {}
for m in range(14, 22):
    p = f'{ax.BASES}/scan_m{m}.txt'
    ax.write_base(c, m, p)
    out[m] = [ax.glift(p, s) for s in (1, 2, 3)]
    import os; os.remove(p)
    print(m, out[m], flush=True)
json.dump({'a': a.tolist(), 'a2': a2.tolist(), 'costs': out}, open('/home/user/degree-diameter/research/squads/r2_d8c/c1/scan_low_m.json', 'w'))
