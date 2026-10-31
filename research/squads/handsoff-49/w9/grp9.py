#!/usr/bin/env python3
"""w9: bi-coset graphs of permutation groups.  Usage:
   python3 grp9.py GROUP h [TRIALS] [MODE]     MODE = exh (default) | rnd:COUNT
Enumerates conjugacy classes of subgroups H of order h (random sampling of normalising chains), builds the
M x M coset table for each class (writes runs/GROUP_h_K.bin) and runs bi9 on it. Composition: see bi9.c."""
import sys, os, random, math, subprocess, time, json
import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, "/home/user/degree-diameter/research/squads/handsoff-49/w7")
import pgen  # w7's GF(p^k) tables and PSL/PGL generators (read only)

def cyc(d, *cycles):
    p = list(range(d))
    for c in cycles:
        for i in range(len(c)):
            p[c[i]] = c[(i + 1) % len(c)]
    return tuple(p)

def closure(gens):
    d = len(gens[0]); ident = tuple(range(d))
    els = [ident]; index = {ident: 0}; i = 0
    while i < len(els):
        g = els[i]; i += 1
        for s in gens:
            h = tuple(g[x] for x in s)
            if h not in index:
                index[h] = len(els); els.append(h)
    return els, index

def group_gens(name):
    if name == "M11":
        return [cyc(11, tuple(range(11))), cyc(11, (2, 6, 10, 7), (3, 9, 4, 5))]
    if name == "S7":
        return [cyc(7, (0, 1)), cyc(7, tuple(range(7)))]
    if name == "A7x2":
        return [cyc(9, (0, 1, 2)), cyc(9, tuple(range(7))), cyc(9, (7, 8))]
    if name == "A8":
        return [cyc(8, (0, 1, 2)), cyc(8, tuple(range(1, 8)))]
    if name.startswith("PSL2_") or name.startswith("PGL2_") or name.startswith("PSLs2_"):
        pgl = name.startswith("PGL2_")
        spec = name.split("_")[1]
        p, k = (int(x) for x in spec.split("^")) if "^" in spec else (int(spec), 1)
        polys = {(2, 5): [1, 0, 1, 0, 0], (2, 4): [1, 1, 0, 0], (3, 3): [1, 1, 0], (5, 2): [2, 0], (2, 3): [1, 1, 0],
                 (3, 2): [2, 0], (2, 2): [1, 1], (7, 2): [3, 0], (2, 6): [1, 1, 0, 0, 0, 0]}
        poly = polys.get((p, k), [0])
        gens = pgen.pl_gens(p, k, poly, pgl)
        if name.startswith("PSLs2_"):
            q, MUL, ADD, INV, NEG = pgen.gf_tables(p, k, poly)
            def powp(a, e):
                r = 1
                for _ in range(e):
                    r = MUL[r][a]
                return r
            frob = tuple([powp(a, p) for a in range(q)] + [q])
            gens = gens + [frob]
        return gens
    raise SystemExit("unknown group " + name)

class Grp:
    def __init__(self, gens):
        self.els, self.index = closure(gens)
        self.N = len(self.els); self.d = len(gens[0])
        self.P = np.array(self.els, dtype=np.int64)
        rs = np.random.default_rng(12345)
        self.w = rs.integers(1, 2 ** 62, size=self.d, dtype=np.uint64) | np.uint64(1)
        codes = self.code(self.P)
        assert len(np.unique(codes)) == self.N, "hash collision"
        self.order = np.argsort(codes); self.scodes = codes[self.order]
        self.Pinv = np.argsort(self.P, axis=1)
        self.inv = self.idx(self.Pinv)
        self.ords = None

    def code(self, Q):
        return (Q.astype(np.uint64) * self.w).sum(axis=-1, dtype=np.uint64)

    def idx(self, Q):
        c = self.code(Q)
        pos = np.minimum(np.searchsorted(self.scodes, c), self.N - 1)
        assert (self.scodes[pos] == c).all(), "element not in group"
        return self.order[pos]

    def orders(self):
        if self.ords is None:
            res = np.zeros(self.N, dtype=np.int64)
            for i, p in enumerate(self.els):
                seen = [False] * self.d; L = 1
                for s in range(self.d):
                    if not seen[s]:
                        c = 0; t = s
                        while not seen[t]:
                            seen[t] = True; t = p[t]; c += 1
                        L = L * c // math.gcd(L, c)
                res[i] = L
            self.ords = res
        return self.ords

    def conj_all(self, x):
        """index of g^-1 x g for every g"""
        Xg = self.P[x][self.P]
        return self.idx(np.take_along_axis(self.Pinv, Xg, axis=1))

    def gen_sub(self, gens, limit):
        S = {0}; lst = [0]; i = 0
        gt = [self.els[g] for g in gens]
        while i < len(lst):
            x = self.els[lst[i]]; i += 1
            for s in gt:
                y = self.index[tuple(x[t] for t in s)]
                if y not in S:
                    S.add(y); lst.append(y)
                    if len(S) > limit:
                        return None
        return sorted(S)

    def canon(self, H):
        A = np.stack([self.conj_all(hh) for hh in H], axis=1)
        A.sort(axis=1)
        o = np.lexsort(A.T[::-1])
        return tuple(A[o[0]].tolist())

    def subgroup_classes(self, h, trials, seed=1):
        rnd = random.Random(seed)
        ords = self.orders()
        X = [i for i in range(1, self.N) if h % ords[i] == 0]
        classes = {}
        for _ in range(trials):
            if not X:
                break
            H = self.gen_sub([rnd.choice(X)], h)
            if H is None:
                continue
            steps = 0
            while len(H) < h and steps < 80:
                steps += 1
                Hset = np.array(H)
                mask = np.ones(self.N, dtype=bool)
                for hh in H:
                    mask &= np.isin(self.conj_all(hh), Hset)
                cand = np.nonzero(mask)[0] if rnd.random() < 0.85 else np.arange(self.N)
                cand = cand[~np.isin(cand, Hset)]
                if len(cand) == 0:
                    break
                y = int(cand[rnd.randrange(len(cand))])
                nH = self.gen_sub(H + [y], h)
                if nH is not None and len(nH) > len(H):
                    H = nH
            if len(H) != h:
                continue
            key = self.canon(H)
            if key not in classes:
                classes[key] = H
        return list(classes.values())

    def describe(self, H):
        ords = self.orders()
        from collections import Counter
        return dict(Counter(int(ords[g]) for g in H))

    def build_bin(self, H, path):
        H = np.array(H, dtype=np.int64); h = len(H)
        Hp = self.P[H]
        Q = np.stack([Hp[k][self.P] for k in range(h)])     # h x N x d : h_k o x
        lab = self.idx(Q).min(axis=0)
        uniq = np.unique(lab); M = len(uniq)
        assert M * h == self.N, "coset count"
        cid = np.searchsorted(uniq, lab)
        Pc = self.P[uniq]
        T = np.empty((M, M), dtype=np.uint16)
        for c in range(M):
            T[c] = cid[self.idx(Pc[c][Pc])]
        Pinvc = self.Pinv[uniq]
        Ainv = np.empty((M, h), dtype=np.int32); rho = np.empty((M, h), dtype=np.int32)
        for t in range(h):
            Ainv[:, t] = cid[self.idx(Pinvc[:, Hp[t]])]
            rho[:, t] = cid[self.idx(Pc[:, Hp[t]])]
        with open(path, "wb") as f:
            f.write(np.array([M, h], dtype="<i4").tobytes())
            f.write(T.astype("<u2").tobytes())
            f.write(Ainv.astype("<i4").tobytes())
            f.write(rho.astype("<i4").tobytes())
        return M, h

def run_bi9(binpath, mode, outpath):
    cmd = ["nice", "-n", "10", os.path.join(HERE, "bi9"), binpath] + mode + [outpath]
    r = subprocess.run(cmd, capture_output=True, text=True, timeout=540)
    return r.stdout.strip(), r.stderr.strip()

def main():
    name = sys.argv[1]; h = int(sys.argv[2])
    trials = int(sys.argv[3]) if len(sys.argv) > 3 else 3000
    mode = sys.argv[4] if len(sys.argv) > 4 else "exh"
    t0 = time.time()
    G = Grp(group_gens(name))
    print(f"group {name}: order {G.N}, degree {G.d}  (sampling {time.time()-t0:.1f}s)", flush=True)
    classes = G.subgroup_classes(h, trials)
    print(f"subgroup classes of order {h}: {len(classes)}", flush=True)
    os.makedirs(os.path.join(HERE, "runs"), exist_ok=True)
    for K, H in enumerate(classes):
        tag = f"{name}_h{h}_K{K}"
        binp = os.path.join(HERE, "runs", tag + ".bin")
        M, hh = G.build_bin(H, binp)
        info = subprocess.run(["nice", "-n", "10", os.path.join(HERE, "bi9"), binp, "info"], capture_output=True, text=True).stdout.strip()
        print(f"[{tag}] H element orders {G.describe(H)}  {info}", flush=True)
        if mode == "exh":
            out, err = run_bi9(binp, ["exh", "0"], os.path.join(HERE, "runs", tag + ".edges"))
        else:
            cnt = mode.split(":")[1]
            out, err = run_bi9(binp, ["rnd", cnt, "7"], os.path.join(HERE, "runs", tag + ".edges"))
        print(out, flush=True)
        if err:
            print("\n".join(err.splitlines()[-6:]), flush=True)
        with open(os.path.join(HERE, "results.tsv"), "a") as f:
            f.write(f"{name}\th={h}\tK={K}\tn={2*M}\t{out}\t{json.dumps(G.describe(H))}\n")
    print("done", f"{time.time()-t0:.1f}s", flush=True)

if __name__ == "__main__":
    main()
