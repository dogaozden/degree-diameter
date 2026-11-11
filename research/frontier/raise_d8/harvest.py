#!/usr/bin/env python3
"""Find new cost-0 solution files (*.sol) in the squad round folders and runs/, check each with save.sh
(haarcheck_gen) and save VALID ones as research/frontier/sols/d<d>D<D>_<fam>_<p>_<n>_orb<k-m-f>_<tag>.txt.
usage: harvest.py DIR...   (tag = r<round><card> for squad folders, s<seed> for runs/)"""
import sys, os, re, glob, subprocess
here = os.path.dirname(os.path.abspath(__file__))
done_p = os.path.join(here, "harvested.txt")
done = set(open(done_p).read().split()) if os.path.exists(done_p) else set()
for d in sys.argv[1:]:
    for sol in sorted(glob.glob(os.path.join(d, "**", "*.sol"), recursive=True)):
        rp = os.path.realpath(sol)
        if rp in done or "/c16/" in rp: continue
        try: hdr = open(sol).readline().split()
        except Exception: continue
        if len(hdr) < 7 or hdr[2] not in ("sl", "psl"): continue
        dd, D, fam, p, n = hdr[0], hdr[1], hdr[2], hdr[3], hdr[5]
        orb = None
        for lg in glob.glob(os.path.join(os.path.dirname(sol), "*.log")):
            for line in open(lg, errors="ignore"):
                m = re.search(r"RESULT d=%s D=%s group=%s %s x Z_%s .*best=0 .*orbit k=(\d+) m=(\d+) f=(\d+)" % (dd, D, fam, p, n), line)
                if m: orb = "-".join(m.groups())
        if orb is None: orb = "unk"
        m = re.search(r"raise_d8b/r(\d+)/([a-z]\d+)/", rp)
        tag = ("r%s%s" % m.groups()) if m else "s" + (re.search(r"_s(\d+)", os.path.basename(sol)) or re.search("", "")).group(0)[2:] if re.search(r"_s(\d+)", os.path.basename(sol)) else "dir"
        name = "d%sD%s_%s_%s_%s_orb%s_%s" % (dd, D, fam, p, n, orb, tag)
        r = subprocess.run([os.path.join(here, "save.sh"), sol, name], capture_output=True, text=True)
        print(name, "|", (r.stdout + r.stderr).strip().splitlines()[0][:110] if (r.stdout + r.stderr).strip() else "?")
        with open(done_p, "a") as f: f.write(rp + "\n")
