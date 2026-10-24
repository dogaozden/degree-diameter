#!/bin/bash
# run1.sh SECS SEED FAM P N [VAR=x ...]: one (15,10) orbit search with haar_lean (k=3 m=5 f=0 unless ORBIT="k m f" is
# given among the VAR=x), K = 8, nice 5.  Solution to ../frontier/sols/<tag>.txt, log to runs/<tag>.log.
secs=$1; seed=$2; fam=$3; p=$4; n=$5; shift 5
orb="3 5 0"
for v in "$@"; do case $v in ORBIT=*) orb=${v#ORBIT=};; esac; done
read -r ok om of <<< "$orb"
tag=d15D10_${fam}_${p}_${n}_orb${ok}f${of}_s${seed}
extra=""; for v in "$@"; do case $v in ORBIT=*) ;; *) extra="${extra}_${v%%=*}${v#*=}";; esac; done
tag=$tag$extra
out=../frontier/sols/$tag.txt
log=runs/$tag.log
echo "start $(date -u +%FT%TZ) | ORBIT=$orb $* | haar_lean 15 10 $secs $seed 8 $out $fam $p $n" > "$log"
env ORBIT="$orb" "$@" nice -n 5 timeout $((secs + 900)) ./haar_lean_run 15 10 "$secs" "$seed" 8 "$out" "$fam" "$p" "$n" >> "$log" 2>&1
echo "exit $? $(date -u +%FT%TZ)" >> "$log"
