import sys, random, numpy as np, subprocess
sys.path.insert(0,'/home/user/degree-diameter/research/squads/hexfam_r1/c8')
sys.path.insert(0,'/home/user/degree-diameter/research/projects/hexagon-family/tools')
from chart import Chart
from q6lib import Geo
q = 11
ch = Chart(q); iso = ch.iso_vectors()
A = list(np.load(sys.argv[1]).tolist())   # chart indices (encode order)
P = ch.P
def vec(idx): return P[idx]
def mark(bad, z):
    Y = (P[z][None, :] + iso) % q
    bad[ch.encode(Y)] = True
inA = np.zeros(ch.N5, dtype=bool)
bad = np.zeros(ch.N5, dtype=bool)
for a in A: inA[a] = True; mark(bad, a)
print('start size', len(A), 'bad-free candidates', int((~bad & ~inA).sum()))
rng = random.Random(int(sys.argv[2]) if len(sys.argv) > 2 else 0)
cand = np.nonzero(~bad & ~inA)[0].tolist()
rng.shuffle(cand)
for z in cand:
    if bad[z] or inA[z]: continue
    A.append(z); inA[z] = True; mark(bad, z)
print('extended size', len(A))
# to point ids: x = (1,a,b,c,c^2-ae-bf,e,f)
V = []
for z in A:
    a,b,c,e,f = P[z].tolist()
    V.append([1,a,b,c,(c*c-a*e-b*f)%q,e,f])
V.append([0,0,0,0,1,0,0])
G = Geo(q)
ids = G.ids_of(np.array(V))
print('ok,ext =', G.check_opp(ids))
out = sys.argv[3]
open(out,'w').write(' '.join(map(str, ids.tolist())) + '\n')
print(subprocess.run(['/home/user/degree-diameter/research/projects/hexagon-family/tools/povcheck','/home/user/degree-diameter/research/projects/hexagon-family/hex/hex_q11.bin', out], capture_output=True, text=True).stdout.strip().splitlines()[-1])
