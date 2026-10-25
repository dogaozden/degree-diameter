#!/bin/bash
export DEADLINE=$(date -u -d "2026-10-25 04:59:00" +%s)
exec /home/user/degree-diameter/research/squads/r2-smallfam/c7/run_loop2.sh
