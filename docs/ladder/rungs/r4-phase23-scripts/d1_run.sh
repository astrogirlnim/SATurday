#!/bin/bash
# usage: d1_run.sh GRAPH q p s t mode mmin mmax timeout_sec ; stops at first SAT
g=$1;q=$2;p=$3;s=$4;t=$5;mode=$6;a=$7;b=$8;to=${9:-600}
for m in $(seq $a $b); do
  out=$(timeout $to python3 "$(dirname "$0")/d1_search.py" $g $q $p $s $t $mode $m 2>&1); rc=$?
  if [ $rc -eq 124 ]; then echo "$g q=$q p=$p s=$s t=$t $mode m=$m: TIMEOUT(${to}s)"; exit 0; fi
  echo "$out"
  echo "$out" | grep -q ": SAT" && exit 0
done
