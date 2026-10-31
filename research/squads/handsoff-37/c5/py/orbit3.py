"""From the free conder quotient (AR=BR=28, E=84) to n=174 (AR=BR=29, E=87): delete three quotient edges i,j,k;
add a new A-orbit 28 joined to the three freed B-slots and a new B-orbit 28 joined to the three freed A-slots,
with random voltages. usage: orbit3.py STATE OUTDIR NSAMPLES SEED"""
import sys, os, random
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from surgery import load, save
FA, FB, Q, fa, fb = load(sys.argv[1])
assert FA == 0 and FB == 0
od = sys.argv[2]; os.makedirs(od, exist_ok=True)
N = int(sys.argv[3]); random.seed(int(sys.argv[4]))
cnt = 0; tries = 0
while cnt < N and tries < 100 * N:
    tries += 1
    idx = random.sample(range(len(Q)), 3)
    rest = [q for k, q in enumerate(Q) if k not in idx]
    Q2 = list(rest)
    for k in idx:
        Q2.append((28, Q[k][1], random.randrange(3)))     # new A-orbit to freed B-slot
    for k in idx:
        Q2.append((Q[k][0], 28, random.randrange(3)))     # new B-orbit to freed A-slot
    if len(set(Q2)) != len(Q2): continue
    save(os.path.join(od, "t%05d.state" % cnt), 0, 0, Q2, [], [])
    cnt += 1
print("wrote", cnt, "tries", tries)
