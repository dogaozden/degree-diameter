import sys; sys.path.insert(0, '/home/user/degree-diameter/research/squads/raise11/r1/c13')
from model import pick, REC
out = []
for d in range(7, 15):
    rows = pick(d, 1.0, 1.03)
    for t in (1.0, 2.0):
        sel = [r for r in rows if t <= r[4] < t + 0.5][:5]
        out.append(f"Delta={d} target=+{t:.0f}% (window [{t},{t+0.5})%): top5 by K")
        for K, fam, p, n, gain, f in sel:
            out.append(f"  {fam} {p} {n}  gain={gain:.2f}%  N={f['N']}  mu={f['mu']:.2f}  lam={f['lam']:.2f}  "
                       f"I={f['I']} C={f['C']} F={f['F']} cenorb={f['cen_orb']}  Kclump={f['K_clump']:.2f}  Kpen={f['K_pen']:.2f}  K={K:.2f}  P0~{2.718281828**-K:.1e}")
        if not sel:
            out.append("  (no candidate in window)")
print("\n".join(out))
