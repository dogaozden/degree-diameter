#!/bin/bash
# usage: run_one.sh NAME DMAX DMIN NLO NHI MINTOT TIMEOUT   (one GAP process per table-of-marks group)
nm="$1"; safe=$(echo "$nm" | tr -c 'A-Za-z0-9_\n' '_')
mkdir -p logs
cat > logs/run_$safe.g << EOG
Read("cosetsearch2.g");
log := "logs/$safe.log";
PrintTo(log, "");
SearchTom2("$nm", $2, $3, $4, $5, $6, log);
QUIT;
EOG
timeout $7 gap -q -b -o 6g logs/run_$safe.g < /dev/null > logs/$safe.stdout 2>&1
echo "exit $? $nm" >> logs/$safe.log
