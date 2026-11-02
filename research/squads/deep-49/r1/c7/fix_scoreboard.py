import glob, json, os, re
D = "/home/user/degree-diameter/research/squads/deep-49/r1/c7"
SB = "/home/user/degree-diameter/research/squads/deep-49/r1/scoreboard.jsonl"
TOOLS = "/home/user/degree-diameter/research/squads/deep-49/tools"
MOD = {2488: (311, 8), 2492: (89, 28), 2499: (17, 147), 2502: (139, 18), 2504: (313, 8),
       2508: (19, 132), 2511: (31, 81), 2512: (157, 16), 2516: (37, 68), 2528: (79, 32)}
def describe(name):
    m = re.match(r"o(\d+)_h(\d+)_(\d+)$", name)
    if m:
        N, h, k = int(m.group(1)), m.group(2), m.group(3)
        mm, hs = MOD[N]
        return N, ("non-metacyclic split C_%d : H, H = SmallGroups(%d) #%s, Aut(H)-class %s; "
                   "exact Haar search" % (mm, hs, h, k)), None
    m = re.match(r"f(\d+)p(\d+)_(\d+)$", name)
    if m:
        N = int(m.group(1))
        return N, ("semidirect C4 : P, P = SmallGroups(625) #%s, sampled order-4 action %s "
                   "(4 samples per P, partial)" % (m.group(2), m.group(3))), "partial"
    m = re.match(r"f(\d+)(F\d+|c4|a|d|e|g|[ac])_(\d+)$", name)
    if m:
        N = int(m.group(1)); fam = m.group(2); k = m.group(3)
        desc = {"F4": "(C13:C4) x SmallGroups(48)", "F6": "(C13:C6) x SmallGroups(32)",
                "F8": "(C13:C8) x SmallGroups(24)", "F12": "(C13:C12) x SmallGroups(16)",
                "c4": "C4 x SmallGroups(625)", "d": "SmallGroups(20) x SmallGroups(125)"}
        if N == 2500 and fam == "a":
            desc_s = "C2^2 x SmallGroups(625)"
        elif N == 2520 and fam == "a":
            desc_s = "SmallGroups(24) x SmallGroups(105)"
        elif N == 2520 and fam == "c":
            desc_s = "SmallGroups(12) x SmallGroups(210)"
        elif N == 2520 and fam == "e":
            desc_s = "SmallGroups(56) x SmallGroups(45)"
        elif N == 2520 and fam == "g":
            desc_s = "SmallGroups(40) x SmallGroups(63)"
        else:
            desc_s = desc[fam]
        return N, "direct product " + desc_s + ", pair index " + k, None
    raise SystemExit("unknown " + name)
keep = []
if os.path.exists(SB):
    for l in open(SB):
        l = l.rstrip("\n")
        if not l:
            continue
        if json.loads(l).get("card") == "c7":
            continue
        keep.append(l)
new = []
for f in sorted(glob.glob(D + "/res/*.out")):
    name = os.path.basename(f)[:-4]
    if not os.path.exists(D + "/exp/" + name + ".exp"):
        continue
    last = open(f).read().strip().splitlines()[-1]
    assert last.startswith("MIN >0"), (name, last)
    N, idea, note = describe(name)
    rec = {"card": "c7",
           "idea": idea + " (group order %d)" % N,
           "code": D + "/exp/" + name + ".exp",
           "command": "%s/hx %s/w/%s.tab %s/w/%s.aut 0 9" % (TOOLS, D, name, D, name),
           "n": 2 * N,
           "score": None,
           "exact": True,
           "valid": False,
           "next": ("no cost-0 Haar set (LIMIT 0, exhaustive); score is '>0', exact minimum not computed"
                    + ("; sampled family, not exhaustive over actions" if note else ""))}
    new.append(json.dumps(rec))
with open(SB, "w") as fo:
    for l in keep + new:
        fo.write(l + "\n")
print("kept other lines", len(keep), "c7 lines", len(new))
