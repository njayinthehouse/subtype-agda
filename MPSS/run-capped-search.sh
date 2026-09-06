#!/bin/sh
# Runs the capped diamond search in the background, one pass over the Ω families and one random
# pass, with progress lines and a completion marker. Logs go to ../.search-logs/.
cd "$(dirname "$0")"
mkdir -p ../.search-logs
LOG=../.search-logs/capped_$(date +%Y%m%d_%H%M%S).log
rm -f ../.search-logs/capped_DONE
echo "log: $LOG  (tail -f it to watch; percentages print every 20s)"
{
  echo "=== families k=1 kc=1 K=3 Kmax=5 ==="
  python3 diamond-search-capped.py --family omega --k 1 --kc 1 --K 3 --Kmax 5
  echo "=== families k=2 kc=1 K=3 Kmax=5 ==="
  python3 diamond-search-capped.py --family omega --k 2 --kc 1 --K 3 --Kmax 5
  echo "=== random 400 k=1 kc=1 K=3 Kmax=5 ==="
  python3 diamond-search-capped.py --random 400 --seed 11 --k 1 --kc 1 --K 3 --Kmax 5
  echo "=== ALL DONE ==="
} 2>&1 | tee "$LOG"
cp "$LOG" ../.search-logs/capped_latest.log
echo "finished: $LOG" > ../.search-logs/capped_DONE
echo "$LOG"
