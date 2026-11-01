# build_k.py GROUP H TRIALS K : build one coset table with w9's grp9 functions (same class order as grp9.py main)
import sys, time
sys.path.insert(0, '.')
import grp9
name, h, trials, K = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
G = grp9.Grp(grp9.group_gens(name))
classes = G.subgroup_classes(h, trials)
print('classes', len(classes), flush=True)
H = classes[K]
tag = f"{name}_h{h}_K{K}"
M, hh = G.build_bin(H, f"runs/{tag}.bin")
print('built', tag, 'M', M, 'describe', G.describe(H), flush=True)
