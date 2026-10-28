"""Sanity check of the MIP formulation: R = all points (F empty) on small q, should match exact_mip.py optimum."""
import sys, time
sys.argv = ['lns.py', sys.argv[1], '/dev/null', '1', '1', '/tmp/x', sys.argv[2]]
import importlib.util
spec = importlib.util.spec_from_file_location('lns', '/home/user/degree-diameter/research/squads/d5relax-r1/c4/lns.py')
M = importlib.util.module_from_spec(spec); spec.loader.exec_module(M)
R = set(range(M.n)); t0 = time.time()
newT, st, dt, nrow = M.solve([], R, float(sys.argv[6]))
print('q', M.q, 'status', st, 'size', len(newT), 'relaxed', M.relaxed(newT), 'rows', nrow, '%.1f s' % dt)
