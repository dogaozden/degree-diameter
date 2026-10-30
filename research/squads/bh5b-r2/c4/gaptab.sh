#!/bin/bash
# usage: gaptab.sh ORDER ID... ; writes grp/sg_ORDER_ID.txt
o=$1; shift
ids=""
for i in "$@"; do ids="$ids,$i"; done
ids=${ids#,}
cd /home/user/degree-diameter/research/squads/bh5b-r2/c4
timeout 600 nice -n 10 gap -q -c "ORDER:=$o; OUTDIR:=\"grp\"; IDS:=[$ids];" /home/user/degree-diameter/research/beyond-haar-d5b/src/gap_tables.g
