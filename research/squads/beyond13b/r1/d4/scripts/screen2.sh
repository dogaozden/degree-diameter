#!/bin/bash
# RANDORB screen 2 (k = 7 shapes need zr=y: r of order 7 mod n, else all orbit z equal -> disconnected)
B=/home/user/degree-diameter/research/frontier/beyond13/bin
run() { ORBIT="$1" RANDORB=12 $B/haar_big0 7 13 0 1 32 /dev/null $2 $3 $4 2>&1 | grep -E "^RANDORB d=|cost 0|rror|no element|only|needs|not" | sed "s/^/[$1] /"; }
run "7 1 0" psl 97 343
run "7 1 0" sl 97 172
run "5 1 2" sl 199 20
echo SCREEN_DONE
