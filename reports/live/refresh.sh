#!/bin/bash
# Rebuild the live page's documents from the islands' latest pushes.
# Prints one line per changed document: "<collection> <doc_id> <file> <if_version>" (if_version 0 = new document).
# After writing them, run: .venv/bin/python reports/live/build.py --mark-pushed
set -e
cd "$(dirname "$0")/../.."
git fetch -q --all --prune
.venv/bin/python reports/timeline/extract.py >/dev/null 2>&1
.venv/bin/python reports/live/build.py 2>/dev/null | while read -r id ver; do
  col=${id%%/*}; doc=${id#*/}
  if [ "$id" = "live/now" ]; then f=reports/live/out/now.json; else f=reports/live/out/graph-$doc.json; fi
  echo "$col $doc $PWD/$f $ver"
done
