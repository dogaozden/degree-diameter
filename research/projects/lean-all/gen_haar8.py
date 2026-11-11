#!/usr/bin/env python3
"""Lean files for a Haar record of SL(2,8) x Z_n (research/frontier/sols format 'sl 8 poly x^3+x+1 n n'), checked by
LeanAll/HaarGF8Z.lean (cover8).

usage: gen_haar8.py SOLFILE OUTDIR MODULE THEOREM [--per K]

GF(8) = F2[x]/(x^3 + x + 1): bit i of the code is the coefficient of x^i. Batch i (i < 63 * 8) fixes the matrix with
SL(2,8) batch i / 8 and free entry i % 8 (as HaarGF8.bS8, jS8); slot j < n is the Z_n value j. Fields of 40 bits, 48
for words of 10 or 11 letters. Words of D - 1 letters:
D even: s0 * (s1^-1 s2) ...; D odd: left words (s0^-1 s1) (s2^-1 s3) ... and right words (s0 s1^-1) (s2 s3^-1) ...
The certificate words come from a BFS over the group, each re-evaluated before it is written.
"""
import argparse, os, re, sys

W = 40


def gmul(a, b):
    r = 0
    for i in range(3):
        if b >> i & 1:
            r ^= a << i
    for i in (4, 3):
        if r >> i & 1:
            r ^= 0b1011 << (i - 3)
    return r


def gadd(a, b):
    return a ^ b


def gneg(a):
    return a


def gsub(a, b):
    return a ^ b


GINV = {a: next(b for b in range(1, 8) if gmul(a, b) == 1) for a in range(1, 8)}


def chunked(v, bits=None, chunk=4096):
    if bits is None:
        bits = max(v.bit_length(), 1)
    if bits <= chunk:
        return hex(v)
    h = max(chunk, (bits // 2 // chunk) * chunk)
    return f'({chunked(v & ((1 << h) - 1), h, chunk)} + {chunked(v >> h, bits - h, chunk)} <<< {h})'


def jtree(kd, leaves):
    if len(leaves) == 1:
        return leaves[0][0]
    h = len(leaves) // 2
    return (f'(range_join (Q := Q{kd}) (lo := {leaves[0][1]}) (mid := {leaves[h][1]}) (hi := {leaves[-1][2]}) '
            f'{jtree(kd, leaves[:h])} {jtree(kd, leaves[h:])})')


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('sol')
    ap.add_argument('outdir')
    ap.add_argument('module')
    ap.add_argument('theorem')
    ap.add_argument('--per', type=int, default=100)
    ap.add_argument('--source', default='')
    args = ap.parse_args()
    lines = [l for l in open(args.sol).read().split('\n') if l.strip()]
    h = lines[0].split()
    assert h[2] == 'sl' and h[3] == '8' and h[4] == 'poly' and h[5] == 'x^3+x+1' and h[6] == 'n'
    deg, D, n = int(h[0]), int(h[1]), int(h[7])
    gens = []
    for l in lines[1:]:
        m = re.match(r'\s*\d+\s+mat\((\d+),(\d+),(\d+),(\d+)\)\s+z=(\d+)', l)
        if m:
            gens.append(tuple(int(x) for x in m.groups()))
    assert len(gens) == deg
    for a, b, c, d, z in gens:
        assert gsub(gmul(a, d), gmul(b, c)) == 1
    L = D - 1
    global W
    W = 40 if L <= 9 else 48
    NB = 63 * 8
    G = NB * n

    def mul(x, y):
        a, b, c, d, z = x
        e, f, g, hh, w = y
        return (gadd(gmul(a, e), gmul(b, g)), gadd(gmul(a, f), gmul(b, hh)), gadd(gmul(c, e), gmul(d, g)),
                gadd(gmul(c, f), gmul(d, hh)), (z + w) % n)

    def inv(x):
        a, b, c, d, z = x
        return (d, gneg(b), gneg(c), a, (-z) % n)

    def idx(x):
        a, b, c, d, z = x
        if c != 0:
            bs, js = a * 7 + (c - 1), d
        else:
            bs, js = 8 * 7 + (a - 1), b
        return (bs * 8 + js) * n + z

    def el(i):
        r, z = divmod(i, n)
        bs, js = divmod(r, 8)
        if bs < 8 * 7:
            a, c = divmod(bs, 7)
            c += 1
            d = js
            b = gmul(gsub(gmul(a, d), 1), GINV[c])
        else:
            a = bs - 8 * 7 + 1
            c, b = 0, js
            d = GINV[a]
        return (a, b, c, d, z)

    one = (1, 0, 0, 1, 0)
    kinds = ['E'] if D % 2 == 0 else ['L', 'R']
    invpat = {'E': lambda t: t % 2 == 1, 'L': lambda t: t % 2 == 0, 'R': lambda t: t % 2 == 1}
    invlean = {'E': 'decide (t % 2 = 1)', 'L': 'decide (t % 2 = 0)', 'R': 'decide (t % 2 = 1)'}
    codes = {}
    for kd in kinds:
        K = (D - 2) // 2 if kd == 'E' else L // 2
        if kd == 'R':
            pairs = [mul(gens[s], inv(gens[t])) for s in range(deg) for t in range(deg)]
        else:
            pairs = [mul(inv(gens[s]), gens[t]) for s in range(deg) for t in range(deg)]
        par = {idx(one): None}
        front = [one]
        for _ in range(K):
            nxt = []
            for x in front:
                ix = idx(x)
                for k, pr in enumerate(pairs):
                    y = mul(x, pr)
                    iy = idx(y)
                    if iy not in par:
                        par[iy] = (ix, k)
                        nxt.append(y)
            front = nxt
        cs = [0] * G
        for i in range(G):
            x = el(i)
            assert idx(x) == i
            if kd == 'E':
                found = None
                for s in range(deg):
                    y = mul(inv(gens[s]), x)
                    if idx(y) in par:
                        found = (s, idx(y))
                        break
                assert found, (kd, i)
                s0, iy = found
            else:
                iy = i
                assert iy in par, (kd, i)
            ps = []
            while par[iy] is not None:
                iy, k = par[iy]
                ps.append(k)
            ps.reverse()
            ps += [0] * (K - len(ps))
            dig = ([s0] if kd == 'E' else []) + [q for k in ps for q in divmod(k, deg)]
            assert len(dig) == L
            w = one
            for t in range(L):
                w = mul(w, inv(gens[dig[t]]) if invpat[kd](t) else gens[dig[t]])
            assert idx(w) == i, (kd, i)
            cs[i] = sum(dg << (4 * t) for t, dg in enumerate(dig))
        codes[kd] = cs
        print(f'{kd}: {G} words', file=sys.stderr)
    M = args.module
    os.makedirs(args.outdir, exist_ok=True)
    hdr = '/- Generated by research/projects/lean-all/gen_haar8.py. Do not edit by hand. -/\n'
    opens = ('open BipartiteDD.LeanAll BipartiteDD.LeanAll.GF8 BipartiteDD.LeanAll.HaarSwar BipartiteDD.LeanAll.Swar '
             'BipartiteDD.LeanAll.HaarSL BipartiteDD.LeanAll.HaarProd BipartiteDD.LeanAll.HaarGF8 '
             'BipartiteDD.LeanAll.HaarGF8Z Matrix')
    Kty = f'Multiplicative (ZMod {n}) × SpecialLinearGroup (Fin 2) GF8'
    rz = sum((j % n) << (W * j) for j in range(n))

    def stmt(kd, i):
        r, jj = f'({i} / 8)', f'({i} % 8)'
        return (f'∃ Dig, batchOK Pm ONES lt{kd} Dig true ONES 0 0 0 RZ = true ∧ batchOK8 Pm ONES lm{kd} Dig (kindB 8 {r}) '
                f'(sp (mk (aB 8 {r})) * ONES) (sp (mk {jj}) * ONES) (sp (mk (cB 8 {r})) * ONES) (sp (mk {jj}) * ONES) = true')

    with open(os.path.join(args.outdir, 'Defs.lean'), 'w') as f:
        f.write(hdr + 'import BipartiteDD.LeanAll.HaarGF8Z\n\n')
        src = f' ({args.source})' if args.source else ''
        f.write(f'/-! The Haar graph of `SL(2,8) × Z{n}`{src}: degree {deg}, diameter {D}, {2 * G} vertices. {NB} batches of '
                f'{n} slots per word kind. -/\n\n')
        f.write(f'namespace {M}\n\n{opens}\n\n')
        f.write('/-- The `Z_n` parts of the generators, as letters with identity matrices over `ZMod 2`. -/\ndef genZ : ℕ → Let\n')
        for u, g in enumerate(gens):
            f.write(f'  | {u} => ⟨1, 0, 0, 1, {g[4]}⟩\n')
        f.write('  | _ => ⟨1, 0, 0, 1, 0⟩\n\n')
        f.write(f'def sZ (u : ℕ) : G 2 {n} := gOf (genZ u)\n\n')
        f.write('/-- The matrices of the generators (codes over `GF8`). -/\ndef genM : ℕ → Q8\n')
        for u, g in enumerate(gens):
            f.write(f'  | {u} => (mk {g[0]}, mk {g[1]}, mk {g[2]}, mk {g[3]})\n')
        f.write('  | _ => (1, 0, 0, 1)\n\n')
        f.write('def s2 (u : ℕ) : SpecialLinearGroup (Fin 2) GF8 := mkSL8 (genM u)\n\n')
        f.write(f'/-- The generators. -/\ndef sK (u : ℕ) : {Kty} := ((sZ u).2, s2 u)\n\n')
        f.write(f'def Pm : Prm := ⟨{W}, {n}, 2, {n}, 30, {2 ** 29}, {deg}, {L}⟩\n\n')
        f.write('theorem Pm_valid : Pm.valid := by decide\n\n')
        f.write(f'def ONES : ℕ := (2 ^ ({W} * {n}) - 1) / (2 ^ {W} - 1)\n\n')
        f.write(f'theorem hO : ONES = pkF Pm.w (fun _ => 1) Pm.N := (pkF_one_eq {W} {n} (by norm_num)).symm\n\n')
        f.write(f'def RZ : ℕ := {hex(rz)}\n\n')
        f.write(f'theorem hRZ : RZ = pkF Pm.w (fun j => j % {n}) Pm.N := by decide +kernel\n\n')
        f.write(f'theorem detOK : ∀ u < {deg}, DetOK 2 (genZ u) := by decide\n\n')
        f.write(f'theorem genB : ∀ u < {deg}, (genZ u).f ≤ 2 ∧ (genZ u).g ≤ 2 ∧ (genZ u).zw ≤ {n} := by decide\n\n')
        f.write(f'theorem detOK2 : ∀ u < {deg}, (genM u).1 * (genM u).2.2.2 - (genM u).2.1 * (genM u).2.2.1 = 1 := by decide\n\n')
        for kd in kinds:
            f.write(f'def inv{kd} (t : ℕ) : Bool := {invlean[kd]}\n\n')
            f.write(f'def lt{kd} (t u : ℕ) : Let := cond (inv{kd} t) (invLet 2 {n} (genZ u)) (genZ u)\n\n')
            f.write(f'def lm{kd} (t u : ℕ) : Q8 := cond (inv{kd} t) (invQ (genM u)) (genM u)\n\n')
            f.write(f'theorem letOK{kd} : LetOK Pm lt{kd} := by unfold LetOK; decide\n\n')
            f.write(f'theorem letRep{kd} : LetRep sZ inv{kd} Pm.Δ Pm.L lt{kd} :=\n'
                    f'  letRep_of sZ inv{kd} {deg} {L} genZ (fun _ _ => rfl) detOK genB lt{kd} (fun _ _ => rfl)\n\n')
            f.write(f'theorem letRep2{kd} : LetRep8 s2 inv{kd} Pm.Δ Pm.L lm{kd} :=\n'
                    f'  letRep8_of s2 inv{kd} {deg} {L} genM (fun _ _ => rfl) detOK2 lm{kd} (fun _ _ => rfl)\n\n')
            f.write(f'/-- Batch `i` of kind {kd} passes. -/\ndef Q{kd} (i : ℕ) : Prop := {stmt(kd, "i")}\n\n')
        f.write(f'end {M}\n')
    mods = {kd: [] for kd in kinds}
    for kd in kinds:
        for mi, lo in enumerate(range(0, NB, args.per)):
            hi = min(NB, lo + args.per)
            mod = f'Bat{kd}{mi:03d}'
            mods[kd].append((mod, lo, hi))
            with open(os.path.join(args.outdir, mod + '.lean'), 'w') as f:
                f.write(hdr + f'import BipartiteDD.LeanAll.Range\nimport {M}.Defs\n\nnamespace {M}\n\n{opens}\n\n')
                f.write('set_option maxRecDepth 100000\n\n')
                for i in range(lo, hi):
                    dig = sum(codes[kd][i * n + j] << (W * j) for j in range(n))
                    f.write(f'theorem b{kd}{i} : {stmt(kd, i)} :=\n  ⟨{chunked(dig)}, by decide +kernel, by decide +kernel⟩\n\n')
                leaves = [(f'(range_one (Q := Q{kd}) (b := {i}) b{kd}{i})', i, i + 1) for i in range(lo, hi)]
                f.write(f'theorem range{kd}{mi:03d} : ∀ i, {lo} ≤ i → i < {hi} → Q{kd} i :=\n  {jtree(kd, leaves)}\n\nend {M}\n')
    for kd in kinds:
        with open(os.path.join(args.outdir, f'Cover{kd}.lean'), 'w') as f:
            f.write(hdr + 'import BipartiteDD.LeanAll.Range\n')
            for mod, _, _ in mods[kd]:
                f.write(f'import {M}.{mod}\n')
            f.write(f'\nnamespace {M}\n\n{opens}\n\n')
            f.write(f'theorem batches{kd} : ∀ i < (8 * 8 - 1) * 8, Q{kd} i := by\n  intro i hi\n  have hi\' : i < {NB} := hi\n')
            f.write(f'  exact {jtree(kd, [(f"range{kd}{mod[4:]}", lo, hi) for mod, lo, hi in mods[kd]])} i (Nat.zero_le i) hi\'\n\n')
            f.write(f'theorem words{kd} : ∀ x : {Kty}, ∃ dg : ℕ → ℕ, (∀ t < Pm.L, dg t < Pm.Δ) ∧ wordX sK inv{kd} dg Pm.L = x :=\n')
            f.write(f'  cover8 s2 inv{kd} sZ Pm Pm_valid (by decide) rfl rfl hO hRZ letOK{kd} letRep{kd} letRep2{kd} batches{kd}\n\n')
            f.write(f'end {M}\n')
    with open(os.path.join(args.outdir, 'Record.lean'), 'w') as f:
        f.write(hdr)
        for kd in kinds:
            f.write(f'import {M}.Cover{kd}\n')
        f.write(f'\nnamespace {M}\n\n{opens}\n\n')
        f.write(f'theorem record : ∃ H : SimpleGraph (Fin {2 * G}), BipartiteDD.IsBipartiteDegDiam H {deg} {D} := by\n')
        if D % 2 == 0:
            f.write(f'  have h := gen_record_even sK invE (fun _ => rfl) {deg} {(D - 2) // 2} (fun x => wordsE x)\n')
        else:
            f.write(f'  have h := gen_record_odd sK invL invR (fun _ => rfl) (fun _ => rfl) {deg} {L // 2} (by norm_num) '
                    f'(fun x => wordsL x) (fun x => wordsR x)\n')
        f.write('  rw [card_Z_SL8] at h\n  exact h\n\n')
        f.write(f'end {M}\n\nopen {M} in\n')
        f.write(f'/-- A bipartite graph on {2 * G} vertices with degree at most {deg} and diameter at most {D}: the Haar graph of '
                f'`SL(2,8) × Z{n}`. -/\n')
        f.write(f'theorem {args.theorem} : ∃ H : SimpleGraph (Fin {2 * G}), BipartiteDD.IsBipartiteDegDiam H {deg} {D} :=\n'
                f'  record\n')
    print(f'wrote {args.outdir}: {NB} batches per kind in {sum(len(v) for v in mods.values())} modules', file=sys.stderr)


if __name__ == '__main__':
    main()
