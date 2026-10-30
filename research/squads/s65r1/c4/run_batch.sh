#!/bin/bash
# exhaustive runs over batch.txt (name A configs), one process at a time
cd /home/user/degree-diameter/research/squads/s65r1/c4
G0=/home/user/degree-diameter/research/s65/groups/sg
while read name A cfg; do
  o=$(echo $name | cut -d_ -f2); i=$(echo $name | cut -d_ -f3)
  tag=${name}_a${A}
  OUT=sol/$tag.sol timeout 300 nice -n 10 ./bin/a2inv $G0/sg_${o}_${i}.txt alpha/$name.txt $A > logs/$tag.txt 2>&1
  echo "$tag configs=$cfg $(grep RESULT logs/$tag.txt) $(grep evaluated logs/$tag.txt)" >> results.txt
done < batch.txt
echo DONE >> results.txt
