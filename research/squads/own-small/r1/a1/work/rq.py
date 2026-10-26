# requot a flift-convention G-lift (base edges + voltages) to an H-lift over subgroup H (|H| = h, index r).
# Output: base file (k' E') with edges, flift-convention voltages (inverse of right-convention), H table .bin.
import sys, os, pickle
sys.path.insert(0, "/home/user/degree-diameter/research/squads/own-small/r1/a1/work")
from common import *
N, M = load_group(); INV = inverses(N, M)
SUBS = pickle.load(open("/home/user/degree-diameter/research/squads/own-small/r1/a1/work/subs.pkl", "rb"))

def H_table(Hset):
    H = sorted(Hset, key=lambda x: (x != 0, x)); pos = {x: j for j, x in enumerate(H)}
    MH = np.array([[pos[int(M[x, y])] for y in H] for x in H], dtype=np.int64)
    invH = [int(np.where(MH[j] == 0)[0][0]) for j in range(len(H))]
    return H, pos, MH, invH

def requot(k, edges, volts_left, Hset):
    H, pos, MH, invH = H_table(Hset)
    coset_of = {}; reps = []
    for g in range(N):
        if g in coset_of: continue
        j = len(reps); reps.append(g)
        for x in H: coset_of[int(M[x, g])] = (j, x)
    r = len(reps); p = k // 2
    E, V = [], []
    for (u, v), g in zip(edges, volts_left):
        a = INV[g]
        for j, t in enumerate(reps):
            kk, bb = coset_of[int(M[t, a])]
            E.append((u * r + j, v * r + kk)); V.append(invH[pos[bb]])   # flift convention voltage = inverse
    return dict(k=k * r, h=len(H), r=r, MH=MH, E=E, V=V)

def write_base(path, kk, E):
    with open(path, "w") as f:
        f.write(f"{kk} {len(E)}\n" + "".join(f"{a} {b}\n" for a, b in E))

def write_bin(path, MH):
    h = MH.shape[0]
    with open(path, "wb") as f:
        np.array([h], dtype=np.int32).tofile(f); MH.astype(np.uint16).tofile(f)

def lift_edges(kk, h, MH, E, V):
    """flift convention: (u,x)~(v,g x); vertex u*h+x; returns n and edge list."""
    out = []
    for (u, v), g in zip(E, V):
        for x in range(h):
            out.append((u * h + x, v * h + int(MH[g, x])))
    return kk * h, out

def write_edges(path, n, out):
    with open(path, "w") as f:
        f.write(f"{n}\n" + "".join(f"{a} {b}\n" for a, b in out))

if __name__ == "__main__":
    # usage: rq.py VOLTS_FILE LINE_INDEX h_order which OUTDIR
    vf, li, hord, which, od = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), sys.argv[5]
    os.makedirs(od, exist_ok=True)
    k, E0 = base_edges("/home/user/degree-diameter/research/squads/own-small/tools/bases/cubic/b22_cubic.txt")
    lines = [l for l in open(vf) if ":" in l]
    volts = list(map(int, lines[li].split(":")[1].split()))
    keys = sorted([kk for kk in SUBS if len(kk) == hord], key=lambda x: x)
    Hset = keys[which]
    R = requot(k, E0, volts, Hset)
    tag = f"h{hord}_w{which}_l{li}"
    write_base(f"{od}/{tag}.base", R["k"], R["E"])
    write_bin(f"{od}/H{hord}_{which}.bin", R["MH"])
    with open(f"{od}/{tag}.volts", "w") as f: f.write(" ".join(map(str, R["V"])) + "\n")
    n, out = lift_edges(R["k"], R["h"], R["MH"], R["E"], R["V"])
    write_edges(f"{od}/{tag}.edges", n, out)
    print(tag, "base", R["k"], "edges", len(R["E"]), "h", R["h"], "r", R["r"], "n", n)
