# B7: turn the alpha-orbit census (census.log) into per-variant predictions of the random-search budget.
# Model: an alpha-orbit of size L is uncovered with probability exp(-lam*L/k) (independent words, Poisson);
# P(sample solved) = (1 - p_deg) * exp(-f*E_gen - E_small), f = excess factor of generic clumps (1 = pure model).
import math, re, sys
path = sys.argv[1]
lam = None; rows = []; label = None; cur = {}
for line in open(path):
    line = line.rstrip("\n")
    if line.startswith("==="):
        label = line[4:].strip(); cur = {"label": label}; rows.append(cur)
    m = re.search(r"lambda=([0-9.]+)", line)
    if m: lam = float(m.group(1))
    m = re.search(r"CENSUS k=(\d+) AR=(\d+) AFROB=(\d+) AFROBD=(\d+).*\|Fix\|=(\d+):", line)
    if m:
        cur.update(k=int(m.group(1)), fix=int(m.group(5)))
        cur["orbits"] = {int(a): int(b) for a, b in re.findall(r"len (\d+): (\d+) orbits", line)}
    m = re.search(r"clumps_generic=([0-9.]+) small_misses=([0-9.]+) P_small=([0-9.]+) P0_model=([0-9.e+-]+)", line)
    if m:
        cur.update(Egen=float(m.group(1)), Esmall=float(m.group(2)), Psmall=float(m.group(3)), P0=float(m.group(4)))
    m = re.search(r"E\[uncovered elements\]=([0-9.]+)", line)
    if m: cur["Ecost"] = float(m.group(1))
P_DEG, T_EVAL = 0.2, 0.36          # measured on AFROBH k=10 (8 of 40 degenerate), seconds per evaluation
F_EXC = 1.6                         # measured generic clumps (AFROBH k=10, non-degenerate: 9.7) over the model value 6.06
print(f"lambda={lam:.4f}  eval={T_EVAL}s  p_degenerate={P_DEG}  excess f={F_EXC:.2f} (k=10 AFROBH; k=5 Frobenius f~1.05)")
print(f"{'variant':28s} {'|Fix|':>5s} {'orbits (len:count)':>26s} {'E_gen':>6s} {'E_small':>7s} {'P_small':>7s} "
      f"{'core-h f=1':>10s} {'core-h f=%.2f' % F_EXC:>12s}")
for r in rows:
    if "Egen" not in r: print(r["label"], "(no census)"); continue
    orb = " ".join(f"{L}:{n}" for L, n in sorted(r["orbits"].items()))
    p1 = (1 - P_DEG) * math.exp(-r["Egen"] - r["Esmall"])
    pf = (1 - P_DEG) * math.exp(-F_EXC * r["Egen"] - r["Esmall"])
    ch = lambda p: (T_EVAL / p) / 3600 if p > 0 else float("inf")
    print(f"{r['label']:28s} {r['fix']:5d} {orb:>26s} {r['Egen']:6.2f} {r['Esmall']:7.3f} {r['Psmall']:7.3f} "
          f"{ch(p1):10.2f} {ch(pf):12.2f}")
