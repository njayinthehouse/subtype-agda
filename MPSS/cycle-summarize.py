"""Aggregate results/cycle_<shard>.json into cycle-summary.md."""
import json, glob, os, re, collections
D=os.path.dirname(os.path.abspath(__file__))
LOGS='/home/egret/gimmick/1/MPSS/.search-logs'
ST=collections.Counter(); EX={}
shards=sorted(glob.glob(os.path.join(D,'results','cycle_*.json')))
for f in shards:
    d=json.load(open(f))
    for k,v in d['stats'].items(): ST[k]+=v
    for name,ex in d['examples'].items():
        if name not in EX or ex['key']<EX[name]['key']: EX[name]=ex
done=[]; items=collections.Counter(); skipped=[]
for f in sorted(glob.glob(os.path.join(LOGS,'cycle_*.log'))):
    txt=open(f).read()
    sh=os.path.basename(f)
    done.append((sh,'DONE' in txt, txt.count('\n[')))
    for line in txt.splitlines():
        if 'skipped' in line: skipped.append(line)
out=[]
out.append("# Cycle-detection sweep over the diamond recursion\n")
out.append("Script: `scratchpad/cycle-sweep.py` (hist4.py plus exact-state cycle detection, canonical up to renaming). "
           "Configurations: `families()` from diamond-search-capped.py, hist4.py's three extras, hist4cfg.py's configuration, "
           "and 200 `S.rand_cfg` draws (seed 20260912), filtered and deduplicated; k in {2,3}, kc in {1,2}; "
           "at most 1000 quadruples per configuration for k=2 and 300 for k=3 (exhaustive when fewer exist); "
           "configurations with more than 30000 derivations or context reductions skipped; 100000-call budget per run.\n")
out.append("## Shards\n")
for sh,fin,n in done: out.append(f"- {sh}: {'finished' if fin else 'NOT finished'}, {n} items logged")
out.append("")
out.append("## Totals\n")
out.append(f"- runs completed: {ST['runs']}")
out.append(f"- calls: {ST['calls']}")
out.append(f"- pulls: {ST['pulls']} (ext {ST['ext']}, int {ST['int']})")
out.append(f"- budget hits (100000 calls): {ST['budget']}; crashes (MemoryError/RecursionError in a run): {ST['crash']}")
out.append(f"- items skipped: size {ST['skipped_size']}, memory {ST['skipped_memory']}, enumeration timeout {ST['skipped_timeout']}, recursion {ST['skipped_recursion']}")
out.append("")
out.append("## Violations\n")
out.append(f"- A (trigger id consumed twice on a path): {ST['A_trigger_repeat']}")
out.append(f"- B (pair of origin ids recurs on a path): {ST['B_pair_repeat']}")
out.append(f"- C (stored premise stamp fetched twice on a path): {ST['C_stored_piece_refetched']}")
out.append(f"- V ((side, frame, origin id) visited twice on a path): {ST['V_frame_position_revisit']}")
out.append(f"- CYCLE (exact state repeats on a path, up to renaming): {ST['CYCLE']}")
out.append("")
out.append(f"Other counters: int_fetch_original {ST['int_fetch_original']}, ext_fetch_stored {ST['ext_fetch_stored']}, "
           f"fetched_stored_before_own_last_pull {ST['fetched_stored_before_own_last_pull']}, "
           f"fetched_stored_after_own_last_pull {ST['fetched_stored_after_own_last_pull']}\n")
for name in ('C','V','CYCLE'):
    out.append(f"## Smallest example of {name}\n")
    if name not in EX: out.append("none found\n"); continue
    ex=EX[name]
    out.append(f"- configuration: `{ex['cfg']}`  (k={ex['k']}, kc={ex['kc']}, quadruple indices {tuple(ex['quad'])})")
    out.append(f"- inputs: t1 = `{ex['inputs']['t1']}`, t2 = `{ex['inputs']['t2']}`, c1 -> `{ex['inputs']['c1']}`, c2 -> `{ex['inputs']['c2']}`")
    out.append(f"- key (cfg size, path length, call index): {ex['key']}")
    out.append("")
    out.append("```")
    out.append(f"EXAMPLE {name} {ex['extra']}")
    for ev in ex['path']: out.append(f"    {ev}")
    if name=='CYCLE':
        out.append("  calls from the first occurrence of the state to its repeat (depth, rule1, rule2, source):")
        for r in ex['extra'].get('loop',[]): out.append(f"    {r}")
    out.append("```\n")
if skipped:
    out.append("## Skipped items\n")
    out.append("```")
    out += skipped
    out.append("```")
open(os.path.join(D,'cycle-summary.md'),'w').write("\n".join(out)+"\n")
print("\n".join(out))
