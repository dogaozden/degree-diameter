#!/bin/bash
# stop the 4+4 screen runner (after b44_0) so the re-anneal fits in the 20-minute box
for p in $(pgrep -f "run_screen" ) $(pgrep -f "lscreen.py bases/b44_"); do kill "$p" 2>/dev/null; done
echo "screen stopped at $(date +%T)"
