#!/bin/bash
# killfsd.sh "ARGS": kill the fsd processes (exact name fsd) whose arguments contain ARGS (never this shell); the
# driver scripts above them keep running (stop those with killsweep.sh)
for pid in $(pgrep -x fsd); do args=$(tr '\0' ' ' < /proc/$pid/cmdline 2>/dev/null); case "$args" in *"$1"*) kill $pid && echo "killed $pid: $args";; esac; done
