#!/bin/bash
# usage: run_job.sh TABLE PATTERN IDCOL OUT   (one chart-aware search, wrapped for the shared machine)
timeout 900 nice -n 10 /tmp/claude-0/r2c6/ctrl_chart "$1" "$2" 3 "$3" > "$4" 2>&1
