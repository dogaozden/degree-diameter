# validate.py: compare exh member costs with c5b's cscreen lines (same H, same double-coset representatives)
import subprocess, sys, re
def vdec(k, q):
    if k < q**3: return [1, k//q**2, (k//q)%q, k%q]
    k -= q**3; return [0, 1, k//q, k%q]
fam = {
 'C': dict(q=181, psl=0, H=(42, 5930103), file='../c5b-cosetscreen/out/C_pgl181_D5_10_nsq.out'),
 'K': dict(q=229, psl=1, H=(52697, 6182), file='../c5b-cosetscreen/out/K_psl229_D5_10.out'),
}
name = sys.argv[1]; n = int(sys.argv[2]) if len(sys.argv) > 2 else 10
f = fam[name]; q = f['q']
r = vdec(f['H'][0], q); s = vdec(f['H'][1], q)
rows = []
for line in open(f['file']):
    if not line.startswith('cand'): continue
    t = line.split()
    rows.append((int(t[1]), int(t[3]), int(t[5]), int(t[7]), int(t[9]), int(t[11])))  # i, key, uBA, uAA, uBB, C
ok = 0
for (i, key, uBA, uAA, uBB, C) in rows[:n]:
    z = vdec(key, q)
    out = subprocess.run(['./exh', str(q), str(f['psl'])] + [str(v) for v in r] + [str(v) for v in s] + ['member'] + [str(v) for v in z],
                         capture_output=True, text=True).stdout.strip()
    m = re.search(r'regular (\d) dc (-?\d+) uBA (\d+) uAA (\d+) uBB (\d+) C (\d+)', out)
    reg, dc, mBA, mAA, mBB, mC = map(int, m.groups())
    good = (mBA, mAA, mBB) == (uBA, uAA, uBB)
    ok += good
    print(f"cand {i}: c5b uBA {uBA} uAA {uAA} uBB {uBB} C {C} | exh uBA {mBA} uAA {mAA} uBB {mBB} C {mC} regular {reg} {'OK' if good else 'MISMATCH'}")
print(name, "matching", ok, "of", n)
