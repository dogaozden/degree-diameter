#!/bin/bash
# kp.sh ARG : kill po7/po7L/wpo/nuj7 processes whose last argument equals ARG; kp.sh : list them
for p in $(pgrep -x po7) $(pgrep -x po7L) $(pgrep -x po7R) $(pgrep -x wpo) $(pgrep -x nuj7) $(pgrep -x wpoL); do
  c=$(tr '\0' ' ' < /proc/$p/cmdline 2>/dev/null); last=$(echo $c | awk '{print $NF}')
  if [ -z "$1" ]; then echo "$p $c $(ps -o time= -p $p)"; elif [ "$last" == "$1" ]; then kill $p && echo killed $p $c; fi
done
