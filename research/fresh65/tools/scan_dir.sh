#!/bin/bash
# Consume exported bi-coset files: scan each with bicoset.c, append the DONE/VALID lines to LOG, keep any
# cost-0 graph's edge list and check it with apsp. Stops when GAPLOG says ALLDONE and no file is left.
# usage: scan_dir.sh DIR LOG GAPLOG [MAXFIX] [MAXCAND]
DIR=$1; LOG=$2; GAPLOG=$3; export MAXFIX=${4:-99}; MAXCAND=${5:-20000000}
T=$(dirname "$0")
while true; do
    f=$(ls "$DIR"/*.txt 2>/dev/null | head -1)
    if [ -z "$f" ]; then
        if grep -q ALLDONE "$GAPLOG" 2>/dev/null; then break; fi
        sleep 5; continue
    fi
    lab=$(basename "$f" .txt)
    nice -n 5 timeout 1800 "$T/bicoset" "$f" 6 5 "$DIR/$lab" "$MAXCAND" >> "$LOG" 2>&1
    if [ -f "$DIR/$lab.edges" ]; then
        "$T/apsp" "$DIR/$lab.edges" 6 5 >> "$LOG" 2>&1
        mkdir -p "$DIR/../found"; gzip -c "$DIR/$lab.edges" > "$DIR/../found/$lab.edges.gz"; cp "$f" "$DIR/../found/"
        rm -f "$DIR/$lab.edges"
    fi
    rm -f "$f"
done
echo "SCANDONE" >> "$LOG"
