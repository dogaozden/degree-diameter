#!/bin/bash
# stop the screen loop (bash PID 30677) once the line for bt13_2 is in the table; kill its running child; write DONE
D=/home/user/degree-diameter/research/squads/d12D5-r2/c8
cd $D
until grep -q '^bt12_2 ' screen1_table.txt; do sleep 2; done
C=$(ps --ppid 30677 -o pid= | tr -d ' ')
kill 30677 2>/dev/null
for p in $C; do kill $p 2>/dev/null; done
echo "STOPPED_BY_WATCHER after bt12_2 (killed child: ${C:-none})" >> screen1_table.txt
echo DONE >> screen1_table.txt
