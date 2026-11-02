#!/bin/bash
# commit_small.sh MSGFILE PATH...: git add the paths, unstage every file larger than 2 MB (generated group tables,
# big edge lists; record graphs are committed gzipped elsewhere), commit with the message in MSGFILE.
msg=$1; shift
git add -A "$@" 2>/dev/null
git diff --cached --name-only -z | while IFS= read -r -d '' f; do
  [ -f "$f" ] && [ $(stat -c %s "$f") -gt 2000000 ] && git reset -q -- "$f" && echo "skipped (>2MB): $f"
done
git commit -q -F "$msg"
