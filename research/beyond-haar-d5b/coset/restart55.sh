#!/bin/bash
# restart the (5,5) |H| = 2 sweep (exhaustive mode) on the orders not yet done, then the follow-up queue
cd "$(dirname "$0")"
while pgrep -f "[s]weep.sh 392 2 5" > /dev/null; do sleep 10; done
done55=$(awk '{print $1}' logs/queue55.log | tr '\n' ' ')
todo=""; for o in 392 394 396 398 402 404 406 408 410 412 414 418 420 422 424 426 428 430 434 436 438 440 400 416; do
  case " $done55 " in *" $o "*) ;; *) todo="$todo $o";; esac; done
echo "392 done (sweep.sh, annealing) $(date -u +%H:%M)" >> logs/queue55.log
./queue55.sh 3 $(echo $todo | sed 's/^392 //')
./queue_next.sh
