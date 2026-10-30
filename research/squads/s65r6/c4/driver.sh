#!/bin/bash
# c4 driver: chunks of 40 ids; each .dc2 annealed with SA=1 SECS=2 SEED=1; keep best<=40 in keep/.
C=/home/user/degree-diameter/research/squads/s65r6/c4
T=/home/user/degree-diameter/research/s65/tools
IDSFILE=/home/user/degree-diameter/research/s65/c3p256/r6_d.txt
START=$(date -d "2026-10-30 09:51:41 UTC" +%s)
NEWCHUNK_CUTOFF=$((START+28*60))
DL=$(date -d "2026-10-30 10:21:30 UTC" +%s)
cd $C; mkdir -p d keep
note(){ echo "$(date -u +%H:%M:%S) $*" >> progress.txt; }

anneal_dir(){
  for f in $(ls d/*.dc2 2>/dev/null | sort); do
    if [ $(date +%s) -ge $DL ]; then note "deadline reached inside chunk, stopping annealing"; return 1; fi
    if grep -q "^$f " results.txt 2>/dev/null; then continue; fi
    out=$(SA=1 SECS=2 SEED=1 timeout 60 nice -n 10 $T/dcenum $f 6 5 $f.edges 2>&1 | grep '^RESULT')
    b=$(echo "$out" | awk '{for(i=1;i<=NF;i++) if($i=="best") print $(i+1)}')
    [ -z "$b" ] && b=NA
    echo "$f $b" >> results.txt
    if [ "$b" != NA ] && [ "$b" -le 40 ]; then
      mv "$f" "$f.edges" keep/ 2>/dev/null
    else
      rm -f "$f" "$f.edges"
    fi
    if [ "$b" = 0 ]; then note "!!! RECORD CANDIDATE $f best 0"; fi
  done
  return 0
}

summ(){ # chunk label
  awk -v L="$1" '$2!="NA"{print $2}' results.txt | sort -n | awk '{a[NR]=$1} END{ if(NR) printf "%s n=%d min=%d median=%d\n", L, NR, a[1], a[int((NR+1)/2)]}'
}

for k in $(seq 1 10); do
  if [ $k -gt 1 ]; then
    if [ $(date +%s) -ge $NEWCHUNK_CUTOFF ]; then note "28-minute cutoff: no new chunk $k"; break; fi
    if [ $(date +%s) -ge $DL ]; then break; fi
    ids=$(sed -n "$(( (k-1)*40+1 )),$(( k*40 ))p" $IDSFILE | paste -sd, -)
    note "chunk $k export ids $ids"
    rm -f d/*.dc2 d/*.edges
    gap -q -c "PORD:=256; IDS:=[$ids]; OUTDIR:=\"d\";" c3p_export.g > gap_chunk$k.log 2>&1
    note "chunk $k exported $(ls d/*.dc2 | wc -l) dc2 files"
  fi
  anneal_dir || break
  note "chunk $k annealing done: $(summ chunk$k-cumulative)"
done

# re-anneal best 2 kept graphs with SECS=60 SEED=2
note "re-anneal phase"
for f in $(awk '$2!="NA"{print $2" "$1}' results.txt | sort -n | awk '{print $2}' | while read x; do [ -f keep/$(basename $x) ] && echo $x; done | head -2); do
  bn=$(basename $f)
  out=$(SA=1 SECS=60 SEED=2 timeout 120 nice -n 10 $T/dcenum keep/$bn 6 5 keep/$bn.s60.edges 2>&1 | grep '^RESULT')
  b=$(echo "$out" | awk '{for(i=1;i<=NF;i++) if($i=="best") print $(i+1)}')
  echo "RE keep/$bn $b" >> results.txt
  note "re-anneal keep/$bn SECS=60 SEED=2 best ${b:-NA}"
done
note "DRIVER FINISHED"
