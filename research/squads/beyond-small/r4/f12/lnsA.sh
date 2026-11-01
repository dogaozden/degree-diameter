#!/bin/bash
# lnsA.sh: exact-repair loop on side A (swapped graph). Drop R=4..6 random orbits, rebuild a pool of key-free
# compatible covers (repA sampling), exact max clique on the pool (time-limited), accept if count >= current.
cd "$(dirname "$0")"
G=../../data/Gswap.edges
END=$(( $(date +%s) + 2400 ))
it=0
while [ $(date +%s) -lt $END ]; do
  it=$((it+1))
  a=$(wc -l < bestA.txt)
  R=$((4 + RANDOM % 3))
  shuf bestA.txt | head -n -$R > fixA.txt
  timeout 100 nice -n 10 ./repA $G fixA.txt tryA.txt 70 $RANDOM 6 20000 1 20 > /dev/null 2> log_$it.err
  b=$(wc -l < tryA.txt 2>/dev/null || echo 0)
  res=$(grep -h "exact:" log_$it.err | tr '\n' ' ')
  if [ "$b" -ge "$a" ]; then cp tryA.txt bestA.txt; fi
  echo "it $it drop $R: $a -> $b (best $(wc -l < bestA.txt)) $res" >> lnsA.log
  rm -f log_$it.err
done
echo DONE >> lnsA.log
