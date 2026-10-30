#!/bin/bash
# stop_sweep.sh: stop the director's sweep (xargs driver and its haar75/gap children under /tmp/d75), not the squad's.
for p in $(ps -eo pid,args | awk '$2=="xargs" && $0 ~ /src\/run1.sh/ {print $1}'); do kill $p; done
for p in $(ps -eo pid,args | awk '$0 ~ /bin\/bash .*sweep1.sh/ && $0 !~ /stop_sweep/ && $0 !~ /snapshot/ {print $1}'); do kill $p; done
for p in $(ps -eo pid,args | awk '$0 ~ /haar75 \/tmp\/d75\// {print $1}'); do kill $p; done
