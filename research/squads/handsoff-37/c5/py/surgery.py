"""Surgery from an n = 2m state to n + 2 (FA+1, FB+1): delete one quotient edge (a, b, t), attach a new fixed
A-vertex to B-orbit b and a new fixed B-vertex to A-orbit a. usage: surgery.py STATE OUTDIR"""
import sys, os

def load(path):
    with open(path) as f:
        toks = f.read().split()
    FA, FB, E = int(toks[0]), int(toks[1]), int(toks[2])
    p = 3
    Q = []
    for e in range(E):
        Q.append((int(toks[p]), int(toks[p + 1]), int(toks[p + 2]))); p += 3
    fa = [int(x) for x in toks[p:p + FA]]; p += FA
    fb = [int(x) for x in toks[p:p + FB]]
    return FA, FB, Q, fa, fb

def save(path, FA, FB, Q, fa, fb):
    with open(path, "w") as f:
        f.write("%d %d\n%d\n" % (FA, FB, len(Q)))
        for a, b, t in Q: f.write("%d %d %d\n" % (a, b, t))
        for x in fa: f.write("%d\n" % x)
        for x in fb: f.write("%d\n" % x)

if __name__ == "__main__":
    FA, FB, Q, fa, fb = load(sys.argv[1])
    od = sys.argv[2]
    os.makedirs(od, exist_ok=True)
    for i, (a, b, t) in enumerate(Q):
        Q2 = Q[:i] + Q[i + 1:]
        save(os.path.join(od, "s%03d.state" % i), FA + 1, FB + 1, Q2, fa + [b], fb + [a])
    print("wrote", len(Q), "surgery states to", od)
