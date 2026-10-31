#!/bin/bash
# killsweep.sh: stop every sweep worker (bash running src/sweep.sh) and every fsd process
for pid in $(pgrep -x bash); do args=$(tr '\0' ' ' < /proc/$pid/cmdline 2>/dev/null); case "$args" in *"/swe""ep.sh "*) kill $pid && echo "killed worker $pid";; esac; done
for pid in $(pgrep -x fsd); do kill $pid && echo "killed fsd $pid"; done
