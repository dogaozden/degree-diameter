"""Apply a random isometry of Q(6,q) (product of reflections, q odd prime) to a point set; write the image ids.
usage: python3 moveR.py q RFILE OUT seed [nrefl]"""
import sys, random, numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/projects/hexagon-family/tools'); from q6lib import Geo, A7
q = int(sys.argv[1]); G = Geo(q); R = np.array([int(x) for x in open(sys.argv[2]).read().split()])
rng = random.Random(int(sys.argv[4])); nr = int(sys.argv[5]) if len(sys.argv) > 5 else 9
X = G.C[R].copy() % q
for _ in range(nr):
    while True:
        v = np.array([rng.randrange(q) for _ in range(7)]); Qv = int(v @ A7 @ v) * pow(2, q - 2, q) % q
        if Qv: break
    B = (X @ A7 @ v) % q; c = (B * pow(Qv, q - 2, q)) % q          # x -> x - B(x,v)/Q(v) v  (B = 2*polar/2)
    X = (X - (c[:, None] * v[None, :]) % q) % q
ids = G.ids_of(X); assert len(set(ids.tolist())) == len(R)
open(sys.argv[3], 'w').write('\n'.join(map(str, ids.tolist())) + '\n')
