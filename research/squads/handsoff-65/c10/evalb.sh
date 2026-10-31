#!/bin/bash
# evalb.sh SOLBASE TAB : lift a voltage base (vl format, voltages = indices of TAB) and print far-pair count
cd /home/user/degree-diameter/research/squads/handsoff-65/c10
python3 lift.py "$1" "$2" > "${1%.sol}.edges" 2>/dev/null
../shared/score65 "${1%.sol}.edges" | tail -1 | sed 's/.*n=\([0-9]*\).*bad=\([0-9]*\).*/n=\1 bad=\2/'
