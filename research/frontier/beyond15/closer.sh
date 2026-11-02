#!/bin/bash
# closer.sh STATE LINKS SECS TAG [SEEDBASE] : chain hmeta links from a saved state (new seed each link, T0 4/8 alternating); stops at cost 0
cd "$(dirname "$0")"; S=$1; L=$2; T=$3; tag=$4; SB=${5:-1000}; set -- $(head -1 $S); d=$1 D=$2 m=$4 k=$5 r=$6
cp $S closers/$tag.start; cur=closers/$tag.start
for i in $(seq 1 $L); do t0=$([ $((i % 2)) = 1 ] && echo 8 || echo 4)
  res=$(env START=$cur T0=$t0 T1=1 REHEAT=400 THREADS=1 timeout $((T + 20)) ./bin/hmeta $d $D $T $((SB + i * 7)) 8 closers/${tag}_$i $m $k $r 2>/dev/null | grep RESULT)
  echo "$tag link $i: $res"
  case "$res" in *best=0\ *) echo "FOUND closers/${tag}_$i"; exit 0;; esac
  [ -f closers/${tag}_$i.best ] && cur=closers/${tag}_$i.best
done
