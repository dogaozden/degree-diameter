#!/usr/bin/env python3
"""w17: subgroup catalogue and config writer for mix.c.

Usage:
  python3 mkcfg.py TABLE.bin list [ORDERS]          print subgroups of order 2 and 4 (or the orders given, e.g. 2,4)
                                                     with ids, order, conjugacy class and class size
  python3 mkcfg.py TABLE.bin cfg OUT.cfg ID [ID...] write a mix.c config; each ID is a subgroup id from `list`,
                                                     or the token 'triv' for the trivial subgroup
  python3 mkcfg.py TABLE.bin types                   enumerate admissible orbit types with class representatives

Subgroups of order 2 and 4 (cyclic or Klein): ids are stable for a given table.
"""
import sys
import numpy as np


def load(path):
    with open(path, "rb") as f:
        n = int(np.fromfile(f, dtype=np.int32, count=1)[0])
        T = np.fromfile(f, dtype=np.uint16, count=n * n).reshape(n, n)
    return T


def inverses(T):
    N = len(T)
    inv = np.empty(N, dtype=np.int64)
    for g in range(N):
        inv[g] = int(np.nonzero(T[g] == 0)[0][0])
    return inv


def subgroups(T, orders):
    N = len(T)
    inv = inverses(T)
    sq = T[np.arange(N), np.arange(N)]
    invol = [g for g in range(1, N) if sq[g] == 0]
    found = {}
    def add(elems):
        key = tuple(sorted(int(x) for x in elems))
        if len(key) in orders and key not in found:
            found[key] = True
    if 2 in orders:
        for t in invol:
            add([0, t])
    if 4 in orders:
        for x in range(1, N):
            if T[T[x, x], T[x, x]] == 0 and sq[x] != 0:  # order 4
                x2 = T[x, x]
                add([0, x, x2, T[x2, x]])
        invset = set(invol)
        for a in invol:
            for b in invol:
                if b <= a:
                    continue
                if T[a, b] == T[b, a] and T[a, b] != 0 and int(T[a, b]) in invset:
                    ab = int(T[a, b])
                    add([0, a, b, ab])
    subs = [list(k) for k in found]
    return subs, inv


def conj_classes(T, inv, subs):
    """Return class id per subgroup and class sizes (conjugation by all of G)."""
    N = len(T)
    index = {tuple(sorted(s)): i for i, s in enumerate(subs)}
    cls = [-1] * len(subs)
    classes = []
    for i, s in enumerate(subs):
        if cls[i] != -1:
            continue
        arr = np.array(s)
        members = set()
        for g in range(N):
            # g s g^-1
            img = T[T[g, arr], inv[g]]
            key = tuple(sorted(int(x) for x in img))
            members.add(key)
        cid = len(classes)
        ids = []
        for key in members:
            j = index[key]
            cls[j] = cid
            ids.append(j)
        classes.append(len(members))
    return cls, classes


def main():
    if len(sys.argv) < 3:
        print(__doc__)
        return
    T = load(sys.argv[1])
    N = len(T)
    cmd = sys.argv[2]
    if cmd == "list":
        orders = {2, 4}
        if len(sys.argv) > 3:
            orders = {int(x) for x in sys.argv[3].split(",")}
        subs, inv = subgroups(T, orders)
        cls, sizes = conj_classes(T, inv, subs)
        print(f"# N={N} subgroups={len(subs)} classes={len(sizes)}")
        for i, s in enumerate(subs):
            print(f"{i}\torder={len(s)}\tclass={cls[i]}\tclsize={sizes[cls[i]]}\telems={' '.join(map(str, s))}")
        return
    if cmd == "cfg":
        out = sys.argv[3]
        ids = sys.argv[4:]
        subs, inv = subgroups(T, {2, 4})
        blocks = []
        for tok in ids:
            if tok == "triv":
                blocks.append([0])
            else:
                blocks.append(subs[int(tok)])
        with open(out, "w") as f:
            f.write(f"{len(blocks)}\n")
            for b in blocks:
                b = sorted(b)
                # identity first
                b = [0] + [x for x in b if x != 0]
                f.write(f"{len(b)} " + " ".join(map(str, b)) + "\n")
        print("wrote", out, "orders", [len(b) for b in blocks])
        return
    if cmd == "pairs22":
        # orbit representatives of pairs (H0, H1) of order-2 subgroups under simultaneous conjugation;
        # H0 runs over conjugacy-class representatives, H1 over Stab(H0)-orbits.
        subs, inv = subgroups(T, {2})
        cls, sizes = conj_classes(T, inv, subs)
        index = {tuple(sorted(s_)): i for i, s_ in enumerate(subs)}
        reps0 = {}
        for i in range(len(subs)):
            reps0.setdefault(cls[i], i)
        out = []
        for c0, i0 in sorted(reps0.items()):
            H0 = np.array(subs[i0])
            stab = []
            for g in range(N):
                img = tuple(sorted(int(x) for x in T[T[g, H0], inv[g]]))
                if img == tuple(sorted(subs[i0])):
                    stab.append(g)
            seen = set()
            for i1 in range(len(subs)):
                if i1 in seen:
                    continue
                orb = set()
                H1 = np.array(subs[i1])
                for g in stab:
                    img = tuple(sorted(int(x) for x in T[T[g, H1], inv[g]]))
                    orb.add(index[img])
                seen |= orb
                out.append((i0, i1, len(orb), len(stab)))
        print("# H0 H1 orbit_size |Stab(H0)|  (ids of 'list 2')")
        for row in out:
            print("%d %d %d %d" % row)
        return
    if cmd == "rand":
        # rand TABLE rand TYPE SEED OUT : random subgroup choice for a type (22, 244, 4444, 1)
        import random
        typ, seed, out = sys.argv[3], int(sys.argv[4]), sys.argv[5]
        rng = random.Random(seed)
        subs, inv = subgroups(T, {2, 4})
        ids2 = [i for i, s_ in enumerate(subs) if len(s_) == 2]
        ids4 = [i for i, s_ in enumerate(subs) if len(s_) == 4]
        import os
        if os.environ.get("CLS") is not None:
            inv_ = inverses(T)
            cl_, _ = conj_classes(T, inv_, subs)
            want_cls = int(os.environ["CLS"])
            ids4 = [i for i in ids4 if cl_[i] == want_cls]
        want = {"1": [], "22": [2, 2], "244": [2, 4, 4], "4444": [4, 4, 4, 4]}[typ]
        pick = []
        for h in want:
            pool = ids2 if h == 2 else ids4
            pick.append(rng.choice(pool))
        blocks = [subs[i] for i in pick]
        with open(out, "w") as f:
            f.write(f"{len(blocks) if blocks else 1}\n")
            if not blocks:
                f.write("1 0\n")
            for b in blocks:
                b = [0] + [x for x in sorted(b) if x != 0]
                f.write(f"{len(b)} " + " ".join(map(str, b)) + "\n")
        print("picked", pick)
        return
    print("unknown command")


if __name__ == "__main__":
    main()
