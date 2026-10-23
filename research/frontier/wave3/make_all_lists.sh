#!/bin/bash
# Regenerate the wave-3 job lists (screened). Run from research/frontier after building haar_gen3.
#   bash wave3/make_all_lists.sh            (takes ~10-30 min of one core: screening)
# Each line: cell lo hi seconds samples topK
set -e
cd "$(dirname "$0")/.."
while read -r cell d D lo hi secs M K; do
  [ -z "$cell" ] && continue; case "$cell" in \#*) continue;; esac
  python3 wave3/make_jobs3.py $d $D $lo $hi $secs --seeds 1 --seed0 301 --screen $M --show --fam prod,sl,psl,pgl \
    2>/dev/null | python3 wave3/pick_top.py $K > wave3/jobs3_${cell}.base
  # 4 seeds per group: 301..304 (distinct from the watchers' 1-2 and this session's 101-102)
  python3 - "$cell" <<'PY'
import sys
cell = sys.argv[1]
base = [l.split() for l in open(f"wave3/jobs3_{cell}.base") if l.strip()]
out = []
for s in (301, 302, 303, 304):
    for t in base:
        t2 = list(t); t2[3] = str(s); out.append(" ".join(t2))
# interleave: all groups with seed 301 first (smallest order first), then 302, ...
open(f"wave3/jobs3_{cell}.txt", "w").write("\n".join(out) + "\n")
PY
  rm wave3/jobs3_${cell}.base
  echo "$cell: $(wc -l < wave3/jobs3_${cell}.txt) jobs"
done <<'LIST'
# cell   d  D  lo       hi       secs samples topK
d6D9     6  9  58753    63000    300  400  16
d7D8     7  8  44065    46500    300  600  16
d8D8     8  8  109621   115000   300  300  16
d6D10    6  10 245701   256000   300  200  16
d9D8     9  8  241921   252000   300  200  16
d7D9     7  9  205321   225000   300  150  16
d7D10    7  10 1058401  1180000  600  60   16
d8D9     8  9  604801   680000   600  80   16
d9D9     9  9  1488241  1650000  900  30   16
d13D8    13 8  3036961  3500000  1200 12   12
d8D10    8  10 3571777  3900000  1200 12   12
d10D9    10 9  3674809  4000000  1200 10   12
LIST
