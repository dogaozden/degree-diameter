#!/bin/bash
# usage: run_one.sh LOGDIR NAME DMAX DMIN NLO NHI MINTOT TIMEOUT   (one GAP process per table-of-marks group)
d="$1"; nm="$2"; safe=$(echo "$nm" | tr -c 'A-Za-z0-9_\n' '_')
mkdir -p "$d"
cat > "$d/run_$safe.g" << EOG
Read("cosetsearch2.g");
log := "$d/$safe.log";
PrintTo(log, "");
SearchTom2("$nm", $3, $4, $5, $6, $7, log);
QUIT;
EOG
timeout $8 gap -q -b -o 6g "$d/run_$safe.g" < /dev/null > "$d/$safe.stdout" 2>&1
echo "exit $? $nm" >> "$d/$safe.log"
