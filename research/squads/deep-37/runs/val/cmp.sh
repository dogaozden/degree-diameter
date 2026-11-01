#!/bin/bash
# cmp.sh GROUPFILE D : brute force vs orbdfs iso classes
G=$1; D=$2; tag=$(basename $G .txt)_D$D
python3 ../../src/brute_ginv.py $G $D brute_$tag.cert
rm -rf o_$tag; mkdir o_$tag
MAXSOL=1000000 SOLPREFIX=o_$tag/s ../../bin/orbdfs $G $D 2>/dev/null | grep DONE
ls o_$tag | head -1 >/dev/null
python3 - "$tag" <<'PY'
import sys, glob, subprocess
sys.path.insert(0, '../../src'); from iso import g6; from gutil import load
tag = sys.argv[1]; fs = glob.glob(f"o_{tag}/*.edges"); lines = []
for f in fs:
    n, E, adj = load(f); lines.append(g6(n, adj))
cs = set(subprocess.run(["nauty-labelg","-q"], input="\n".join(lines)+"\n", capture_output=True, text=True).stdout.split()) if lines else set()
bs = set(open(f"brute_{tag}.cert").read().split())
print(f"{tag}: orbdfs {len(fs)} sols {len(cs)} classes; brute {len(bs)} classes; missing_in_orbdfs {len(bs-cs)} extra {len(cs-bs)}")
PY
