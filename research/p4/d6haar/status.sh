#!/usr/bin/env bash
# Best cost per job: local logs and the cloud branches p4-d6haar-1..3 (fetched). Final lines show "done".
cd "$(dirname "$0")"
summ() {  # stdin: log text; prints best so far and whether finished
  awk '/best=/{for(i=1;i<=NF;i++) if($i ~ /^best=/) b=$i; if($0 ~ /evals_per_s/) f="done"; if($1 ~ /^t=/) t=$1} END{print b, (f?f:t)}'
}
echo "== local"; for f in logs/D*.log; do printf "%-48s %s\n" "$(basename $f .log)" "$(summ < $f)"; done
git fetch -q origin 'refs/heads/p4-d6haar-*:refs/remotes/origin/p4-d6haar-*' 2>/dev/null
for b in 1 2 3 1b 2b 3b; do
  r=origin/p4-d6haar-$b; git rev-parse -q --verify $r >/dev/null || { echo "== cloud $b: no branch yet"; continue; }
  echo "== cloud $b ($(git log -1 --format=%cr $r))"
  for f in $(git ls-tree --name-only $r logs/ | grep "/D"); do
    printf "%-48s %s\n" "$(basename $f .log)" "$(git show $r:./$f | summ)"; done
  git ls-tree --name-only $r sols/ | grep -v "gitkeep\|\.best" | sed 's/^/SOLVED: /'
done
