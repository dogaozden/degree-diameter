#!/bin/bash
# Round-2 exhaustive-style screen of orbit-symmetric S for (d,D) = (6,7), N in [4441, 5300].
# One job per line:  ORBIT | AR | group...   (AR = "-" for the automatic scaling, else the second cube root of 1 mod n)
# RANDORB samples m random alpha-invariant generator sets; with m = 3e7 and a space of ~1.1e6-1.5e6 orbit pairs
# every orbit pair is seen with probability 1 - exp(-20) or better, so min = 0 means a solution exists in the space.
# usage: screen.sh JOBFILE OUTDIR BIN [SAMPLES]
JOBS=$1; OUT=$2; BIN=$3; M=${4:-30000000}
mkdir -p "$OUT"
run() {
  line=$1; IFS='|' read -r orb ar grp <<< "$line"
  orb=$(echo $orb | xargs); ar=$(echo $ar | xargs); grp=$(echo $grp | xargs)
  tag=$(echo "$orb $ar $grp" | tr ' ' '_')
  if [ "$ar" = "-" ]; then env ORBIT="$orb" RANDORB=$M "$BIN" 6 7 1 1 8 /dev/null $grp > "$OUT/$tag.log" 2>&1
  else env ORBIT="$orb" AR=$ar RANDORB=$M "$BIN" 6 7 1 1 8 /dev/null $grp > "$OUT/$tag.log" 2>&1; fi
  echo "$tag: $(grep -h 'RANDORB d=' "$OUT/$tag.log" | sed 's/.*N=/N=/')"
}
export -f run; export OUT BIN M
grep -v '^#' "$JOBS" | grep -v '^$' | xargs -P 4 -I{} bash -c 'run "{}"'
