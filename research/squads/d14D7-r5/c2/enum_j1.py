import sys, time
sys.path.insert(0, '/home/user/degree-diameter/research/squads/d14D7-r5/c2')
import numpy as np, j1lib as J
t = time.time()
gens = J.load_gens()
print('isometries:', all(J.L.is_isometry(g.tolist(), J.L.std_gram(11), 11) for g in gens), flush=True)
ALL = J.enumerate_group(gens)
print('group size', len(ALL), 'time %.1f' % (time.time() - t), flush=True)
np.save('/home/user/degree-diameter/research/squads/d14D7-r5/c2/j1_all_u8.npy', ALL.astype(np.uint8))
print('saved', flush=True)
