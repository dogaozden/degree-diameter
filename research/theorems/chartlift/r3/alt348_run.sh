#!/bin/bash
# r3/alt348_run.sh BASE GROUP START TAG
r3/alt348.sh $1 $2 $3 3 60 r3/alt/$4 > r3/alt/$4.log 2>&1; echo "$4: $(tail -n 1 r3/alt/$4.log)"
