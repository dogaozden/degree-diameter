# xval.py: cross-check exh12 cost of multi-double-coset members against c5b cscreen (J family: PGL(2,193), D6 nonsquare,
# spec 6,2,2). cscreen reps are its own keys; decode them to PGL matrices (same as cscreen's dec()) and map to exh12 DC ids.
import subprocess, re
q = 193; Q2 = q*q; Q3 = q*q*q
def dec(key):
    if key < Q3: return (1, key // Q2, (key // q) % q, key % q)
    k = key - Q3; return (0, 1, k // q, k % q)
out = open('/home/user/degree-diameter/research/squads/handsoff-108/c5b-cosetscreen/out/J_pgl193_D6_622_nsq.out').read().split('\n')
cands = []
for line in out:
    m = re.match(r'cand (\d+) reps (\d+) (\d+) (\d+) uncBA (\d+) uncAA (\d+) uncBB (\d+) C (\d+)', line)
    if m: cands.append([int(x) for x in m.groups()])
base = ['./exh12v', '193', '0', '85', '0', '0', '1', '0', '1', '5', '0', '10']
for c in cands[:4]:
    reps = c[1:4]
    ids = []
    for k in reps:
        z = dec(k)
        r = subprocess.run(base + ['dcof'] + [str(v) for v in z], capture_output=True, text=True).stdout.strip()
        ids.append(r.split()[6])
    r = subprocess.run(base + ['cost'] + ids, capture_output=True, text=True).stdout.strip()
    print("cscreen cand", c[0], "uncBA", c[4], "uncAA", c[5], "uncBB", c[6], "C", c[7], "| exh12 ids", ids, "->", r)
