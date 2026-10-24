import sys, time
sys.path.insert(0, '/home/user/degree-diameter/research/theorems/d8')
import gh
t0 = time.time()
H = gh.load(5)
print('N', H.N, 'lines shape', H.lines.shape, 'P shape', H.P.shape, 'through', H.through.shape, 'time', round(time.time()-t0, 2))
print('P[0..2]', H.P[:3].tolist())
print('lines[0]', H.lines[0].tolist(), 'through[0]', H.through[0].tolist())
print('dtypes', H.lines.dtype, H.P.dtype)
