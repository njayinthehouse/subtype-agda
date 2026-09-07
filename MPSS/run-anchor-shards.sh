#!/bin/sh
# Run the history-aware probe as parallel shards over configuration ranges, memory-capped.
# usage: ./run-anchor-shards.sh [all|adv]
cd "$(dirname "$0")"
launch() { k=$1; mr=$2; a=$3; b=$4
  (ulimit -v 3500000; nohup timeout 30000 python3 anchor-probe.py $k $mr $a $b > ../.search-logs/anchor_k${k}_${a}_${b}.log 2>&1 &)
}
if [ "${1:-all}" = all ]; then
  launch 1 20000 0 15; launch 1 20000 15 30; launch 1 20000 30 34; launch 1 20000 34 38; launch 1 20000 38 44
  launch 2 4000 0 15;  launch 2 4000 15 30;  launch 2 2000 30 37;  launch 2 2000 37 44
fi
launch 1 20000 44 50; launch 2 2000 44 50
