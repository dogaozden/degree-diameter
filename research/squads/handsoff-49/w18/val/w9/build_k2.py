# build_k2.py (w18 audit copy): build only the S7 order-2 class K2 bin with w9's grp9.py functions (same class order)
import sys, time
sys.path.insert(0, '.')
import grp9
t0 = time.time()
G = grp9.Grp(grp9.group_gens('S7'))
classes = G.subgroup_classes(2, 3000)
print('classes', len(classes), flush=True)
H = classes[2]
print('H', G.describe(H), flush=True)
M, hh = G.build_bin(H, 'runs/S7_h2_K2.bin')
print('built M', M, 'time', round(time.time() - t0, 1), flush=True)
