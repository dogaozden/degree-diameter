#!/bin/bash
cd "$(dirname "$0")/.."
for i in $(seq -w 0 23); do
  python3 chartflags.py charts/perm43/p$i.txt 3 4 charts/perm43/p$i.flags > /dev/null
  echo "p$i $(timeout 200 nice -n 5 ./ctrl_search bases_k33m_col.txt cyclic:19 charts/perm43/p$i.flags 60 1 runs/perm43/p$i | cut -c1-80)"
done
