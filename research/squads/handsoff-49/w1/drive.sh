#!/bin/bash
# drive.sh LISTFILE SECS SEED : LISTFILE lines "KIND<TAB>NAME<TAB>SPEC" with KIND in abc|grp|nat.
# Builds tables (cached in tabs/) and runs haar_tab SECS seconds; appends "NAME N cost" to res/screen.tsv
H=/home/user/degree-diameter/research/squads/handsoff-49
W=$H/w1; T=$H/tools
LIST=$1; SECS=${2:-6}; SEED=${3:-1}
while IFS=$'\t' read -r kind name spec; do
  [ -z "$kind" ] && continue
  bin=$W/tabs/$name.bin
  case $kind in
    abc) [ -f $bin ] || (cd $T && timeout 200 nice -n 10 python3 abc.py build "$spec" $bin >/dev/null 2>&1) ;;
    grp) [ -f $bin ] || (cd $T && timeout 200 nice -n 10 python3 groups.py "$spec" $bin >/dev/null 2>&1) ;;
  esac
  if [ "$kind" = nat ]; then
    line=$(timeout 100 nice -n 10 $T/haar_tab 4 9 $SECS $SEED 8 $W/t/$name.s$SEED.sol $spec 1 2>&1 | grep RESULT)
  else
    if [ ! -f $bin ]; then echo -e "$name\tNOBUILD\t$spec" >> $W/res/screen.tsv; continue; fi
    line=$(timeout 100 nice -n 10 $T/haar_tab 4 9 $SECS $SEED 8 $W/t/$name.s$SEED.sol tab $bin 1 2>&1 | grep RESULT)
  fi
  N=$(echo "$line" | sed -n 's/.*N=\([0-9]*\).*/\1/p'); best=$(echo "$line" | sed -n 's/.* best=\([0-9]*\).*/\1/p')
  echo -e "$name\t$N\t$best\tseed$SEED\t${SECS}s" >> $W/res/screen.tsv
  if [ -n "$best" ] && [ "$best" -eq 0 ]; then echo "$(date -u +%H:%M) ZERO $name N=$N" >> $W/res/zero.log; fi
done < $LIST
