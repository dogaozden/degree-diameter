#!/bin/bash
cd /home/user/degree-diameter/research/squads/r1/c2
timeout 900 nice -n 10 python3 -I /tmp/claude-0/-home-user-degree-diameter/2744c2da-0db8-5a6f-87c3-01a128c9c95e/scratchpad/src/research/structured/tools/orb_screen.py 11 5 2926 3400 "3 3 2" --bin /tmp/claude-0/-home-user-degree-diameter/2744c2da-0db8-5a6f-87c3-01a128c9c95e/scratchpad/bin/haar_sym --samples 300 --anyn > screen_332.txt 2>&1
timeout 900 nice -n 10 python3 -I /tmp/claude-0/-home-user-degree-diameter/2744c2da-0db8-5a6f-87c3-01a128c9c95e/scratchpad/src/research/structured/tools/orb_screen.py 11 5 2926 3400 "5 2 1" --bin /tmp/claude-0/-home-user-degree-diameter/2744c2da-0db8-5a6f-87c3-01a128c9c95e/scratchpad/bin/haar_sym --samples 300 --anyn > screen_521.txt 2>&1
timeout 900 nice -n 10 python3 -I /tmp/claude-0/-home-user-degree-diameter/2744c2da-0db8-5a6f-87c3-01a128c9c95e/scratchpad/src/research/structured/tools/orb_screen.py 11 5 2926 3400 "2 5 1" --bin /tmp/claude-0/-home-user-degree-diameter/2744c2da-0db8-5a6f-87c3-01a128c9c95e/scratchpad/bin/haar_sym --samples 300 --anyn > screen_251.txt 2>&1
echo DONE > chain2.done
