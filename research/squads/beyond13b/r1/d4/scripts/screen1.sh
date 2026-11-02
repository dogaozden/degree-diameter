#!/bin/bash
# RANDORB screen of wildcard orbit shapes at 2N ~ 3.1-3.3e8 (no search). One line per shape in out/screen1.log.
B=/home/user/degree-diameter/research/frontier/beyond13/bin
run() { ORBIT="$1" RANDORB=12 $B/haar_big0 7 13 0 1 32 /dev/null $2 $3 $4 2>&1 | grep -E "^RANDORB d=|cost 0|rror|no element|only|needs|not" | sed "s/^/[$1] /"; }
run "3 1 4" sl 229 13
run "5 1 2" sl 229 13
run "5 1 2" sl 109 121
run "5 1 2" psl 101 305
run "7 1 0" psl 113 217
run "7 1 0" psl 97 343
run "7 1 0" psl 181 53
run "7 1 0" psl 197 41
run "7 1 0" sl 379 3
echo SCREEN_DONE
