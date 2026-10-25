#!/bin/sh
# watch_ckpt.sh CKPT K: test every new checkpoint of a search against the real 7-copy graph (freed sources BFS);
# stop with the first checkpoint that has no far pair (copied to sols/valid_K{K}.sol). cell-15-7 job.
CK=$1; K=$2; last=""
while true; do
  if [ -f "$CK" ]; then
    m=$(stat -c %Y "$CK")
    if [ "$m" != "$last" ]; then
      last=$m; cp "$CK" /tmp/wck_$K.sol
      r=$(nice -n 5 ./kcopy_hub checkf hex/hex_q11.bin /tmp/wck_$K.sol 3 | tail -1)
      echo "$(date -u +%H:%M:%S) $r"
      case "$r" in *"far pairs 0 -> OK"*) cp /tmp/wck_$K.sol sols/valid_K$K.sol; echo "VALID checkpoint saved as sols/valid_K$K.sol"; exit 0;; esac
    fi
  fi
  sleep 20
done
