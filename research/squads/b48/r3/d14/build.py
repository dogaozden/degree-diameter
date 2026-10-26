# d14: build group tables for the groups of orders 2486..2495 that are not covered by cyclic/metacyclic
# sweeps (Z_p x| H with H of small order, direct products, Q8 and Z_4xZ_2 twisted actions).
import sys, itertools
import numpy as np
sys.path.insert(0, "/home/user/degree-diameter/research/squads/b48/tools")
import groups

OUT = "/home/user/degree-diameter/research/squads/b48/r3/d14/tabs/"

def semi_char(p, TH, M):
    """Z_p x|_M H: (a,h)(b,g) = (a + M[h] b, hg); index a*NH + h; identity index 0."""
    NH = len(TH)
    M = np.array(M, dtype=np.int64) % p
    N = p * NH
    g = np.arange(N)
    a, h = g // NH, g % NH
    A = (a[:, None] + (M[h][:, None] * a[None, :]) % p) % p
    H = TH[h[:, None], h[None, :]].astype(np.int64)
    return (A * NH + H).astype(np.uint16)

def q8_table():
    # elements (sign, unit) unit: 0=1,1=i,2=j,3=k
    base = {(0, 0): (1, 0), (0, 1): (1, 1), (0, 2): (1, 2), (0, 3): (1, 3),
            (1, 1): (-1, 0), (2, 2): (-1, 0), (3, 3): (-1, 0),
            (1, 2): (1, 3), (2, 1): (-1, 3), (2, 3): (1, 1), (3, 2): (-1, 1),
            (3, 1): (1, 2), (1, 3): (-1, 2)}
    def unit_mul(u, v):
        if u == 0: return (1, v)
        if v == 0: return (1, u)
        return base[(u, v)]
    els = [(1, 0), (-1, 0), (1, 1), (-1, 1), (1, 2), (-1, 2), (1, 3), (-1, 3)]
    idx = {e: i for i, e in enumerate(els)}
    T = np.zeros((8, 8), dtype=np.uint16)
    for i, (s, u) in enumerate(els):
        for j, (t, v) in enumerate(els):
            s2, w = unit_mul(u, v)
            T[i, j] = idx[(s * t * s2, w)]
    assert (T[0] == np.arange(8)).all()
    M = [1 if u in (0, 1) else -1 for (s, u) in els]   # kernel <i>
    return T, M

def write(name, T):
    groups.write_bin(T, OUT + name + ".bin")
    print(name, len(T), flush=True)

def prim_root_order(p, d):
    for x in range(2, p):
        w = pow(x, (p - 1) // d, p)
        if all(pow(w, d // q, p) != 1 for q in range(2, d + 1) if d % q == 0 and all(q % s for s in range(2, q))):
            return w
    raise ValueError

if __name__ == "__main__":
    which = sys.argv[1:] or ["all"]
    r3_829 = prim_root_order(829, 3)
    r3_277 = prim_root_order(277, 3)
    r4_89 = next(x for x in range(2, 89) if pow(x, 4, 89) == 1 and pow(x, 2, 89) != 1)
    specs = {
        # order 2486 = 2 * 11 * 113
        "o2486_D1243": "dih 1243",
        "o2486_Z11xD113": "cyc 11 x dih 113",
        # 2487 = 3 * 829: Frobenius Z_829 x| Z_3
        "o2487_F829_3": f"meta 829 3 {r3_829}",
        # 2488 = 8 * 311
        "o2488_Z311xD4": "dih 4 x cyc 311",
        "o2488_Z311x|Z8": "meta 311 8 310",
        # 2490 = 2*3*5*83
        "o2490_Z83x|Z30": "meta 83 30 82",
        "o2490_Z83xD15": "dih 15 x cyc 83",
        # 2492 = 4 * 7 * 89
        "o2492_Z89x|Z28_r4": f"meta 89 28 {r4_89}",
        "o2492_Dic7xZ89": "meta 7 4 6 x cyc 89",
        "o2492_D14xZ89": "dih 14 x cyc 89",
        # 2493 = 9 * 277 = 3^2 * 277
        "o2493_Z277x|Z9": f"meta 277 9 {r3_277}",
        "o2493_Z3xF831": f"cyc 3 x meta 277 3 {r3_277}",
        # 2494 = 2 * 29 * 43
        "o2494_D1247": "dih 1247",
        "o2494_D43xZ29": "dih 43 x cyc 29",
        "o2494_D29xZ43": "dih 29 x cyc 43",
    }
    for name, spec in specs.items():
        if which != ["all"] and name not in which:
            continue
        T = groups.table(spec)
        write(name, T)
    # twisted semidirect products (not expressible with the spec grammar)
    if which == ["all"] or "o2488_Z311x|Q8" in which:
        Q, M = q8_table()
        write("o2488_Z311x|Q8", semi_char(311, Q, [(310 if m < 0 else 1) for m in M]))
    if which == ["all"] or "o2488_Z311x|Z4xZ2" in which:
        H = groups.table("cyc 4 x cyc 2")
        M = [(310 if (h % 2) == 1 else 1) for h in range(8)]  # index a*2+b, chi = (-1)^b
        write("o2488_Z311x|Z4xZ2", semi_char(311, H, M))
    if which == ["all"] or "o2490_Z83x|D15" in which:
        H = groups.table("dih 15")
        M = [(82 if h >= 15 else 1) for h in range(30)]  # reflections (index >= 15) invert
        write("o2490_Z83x|D15", semi_char(83, H, M))
    if which == ["all"] or "o2493_Z277x|Z3^2" in which:
        H = groups.table("cyc 3 x cyc 3")
        M = [pow(r3_277, h // 3, 277) for h in range(9)]  # chi = w^a, a = first coordinate
        write("o2493_Z277x|Z3^2", semi_char(277, H, M))
