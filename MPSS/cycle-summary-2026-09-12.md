# Cycle-detection sweep over the diamond recursion

Script: `MPSS/cycle-sweep.py` (hist4.py plus exact-state cycle detection, canonical up to renaming). Configurations: `families()` from diamond-search-capped.py, hist4.py's three extras, hist4cfg.py's configuration, and 200 `S.rand_cfg` draws (seed 20260912), filtered and deduplicated; k in {2,3}, kc in {1,2}; at most 1000 quadruples per configuration for k=2 and 300 for k=3 (exhaustive when fewer exist); configurations with more than 30000 derivations or context reductions skipped; 100000-call budget per run.

## Shards

- cycle_0.log: finished, 166 items logged
- cycle_1.log: finished, 166 items logged
- cycle_2.log: finished, 165 items logged
- cycle_3.log: finished, 165 items logged
- cycle_4.log: finished, 165 items logged
- cycle_5.log: finished, 165 items logged

## Totals

- runs completed: 533894
- calls: 11255758
- pulls: 1000164 (ext 974170, int 25994)
- budget hits (100000 calls): 0; crashes (MemoryError/RecursionError in a run): 0
- items skipped: size 73, memory 32, enumeration timeout 0, recursion 0

## Violations

- A (trigger id consumed twice on a path): 4
- B (pair of origin ids recurs on a path): 0
- C (stored premise stamp fetched twice on a path): 42
- V ((side, frame, origin id) visited twice on a path): 126
- CYCLE (exact state repeats on a path, up to renaming): 0

Other counters: int_fetch_original 0, ext_fetch_stored 178270, fetched_stored_before_own_last_pull 17851, fetched_stored_after_own_last_pull 186413

## Smallest example of C

- configuration: `((λ⊤.(0 0)) (λ⊤.(0 0))) @ ε;[]`  (k=3, kc=2, quadruple indices (15, 0, 0, 0))
- inputs: t1 = `((λ⊤.((λ⊤.((λ⊤.(0 0)) 0)) (λ⊤.(0 0)))) (λ⊤.(0 0)))`, t2 = `((λ⊤.(0 0)) (λ⊤.(0 0)))`, c1 -> `ε;[]`, c2 -> `ε;[]`
- key (cfg size, path length, call index): [11, 2, 10]

```
EXAMPLE C {'time': 10, 'depth': 7, 'side': 1, 'var': 'z0', 'var_bt': 0, 'kind': 'ext', 'fetched': ['stk', 1, 1, ['d2', ['p']], ['orig', 1]], 'frame_from': ['orig', 1], 'frame_to': ['orig', 1], 'trigger': ['d1', ['o', 'F', 'o', 'e', 'F', 'o', 'e']], 'piece_root': ['d2', ['p']], 'puller_root': ['d2', ['o', 'F', 'p']], 'psize': 5, 'osize': 6, 'stack': 1, 'ctx': 2}
    {'time': 5, 'depth': 3, 'side': 1, 'var': 'z0', 'var_bt': 0, 'kind': 'ext', 'fetched': ['stk', 1, 1, ['d2', ['p']], ['orig', 1]], 'frame_from': ['orig', 1], 'frame_to': ['orig', 1], 'trigger': ['d1', ['o', 'F', 'o']], 'piece_root': ['d2', ['p']], 'puller_root': ['d2', ['o', 'F', 'o']], 'psize': 5, 'osize': 12, 'stack': 1, 'ctx': 1}
    {'time': 9, 'depth': 6, 'side': 1, 'var': 'z1', 'var_bt': 1, 'kind': 'ext', 'fetched': ['stk', 4, 1, ['d2', ['o', 'F', 'p']], ['orig', 1]], 'frame_from': ['orig', 1], 'frame_to': ['orig', 1], 'trigger': ['d1', ['o', 'F', 'o', 'e', 'F', 'o']], 'piece_root': ['d2', ['o', 'F', 'p']], 'puller_root': ['d2', ['p', 'F', 'o']], 'psize': 1, 'osize': 7, 'stack': 1, 'ctx': 2}
```

## Smallest example of V

- configuration: `((λ⊤.(0 0)) (λ⊤.(0 0))) @ ε;[]`  (k=3, kc=2, quadruple indices (15, 0, 0, 0))
- inputs: t1 = `((λ⊤.((λ⊤.((λ⊤.(0 0)) 0)) (λ⊤.(0 0)))) (λ⊤.(0 0)))`, t2 = `((λ⊤.(0 0)) (λ⊤.(0 0)))`, c1 -> `ε;[]`, c2 -> `ε;[]`
- key (cfg size, path length, call index): [11, 3, 11]

```
EXAMPLE V [1, ['orig', 1], ['d2', ['p']]]
    {'time': 5, 'depth': 3, 'side': 1, 'var': 'z0', 'var_bt': 0, 'kind': 'ext', 'fetched': ['stk', 1, 1, ['d2', ['p']], ['orig', 1]], 'frame_from': ['orig', 1], 'frame_to': ['orig', 1], 'trigger': ['d1', ['o', 'F', 'o']], 'piece_root': ['d2', ['p']], 'puller_root': ['d2', ['o', 'F', 'o']], 'psize': 5, 'osize': 12, 'stack': 1, 'ctx': 1}
    {'time': 9, 'depth': 6, 'side': 1, 'var': 'z1', 'var_bt': 1, 'kind': 'ext', 'fetched': ['stk', 4, 1, ['d2', ['o', 'F', 'p']], ['orig', 1]], 'frame_from': ['orig', 1], 'frame_to': ['orig', 1], 'trigger': ['d1', ['o', 'F', 'o', 'e', 'F', 'o']], 'piece_root': ['d2', ['o', 'F', 'p']], 'puller_root': ['d2', ['p', 'F', 'o']], 'psize': 1, 'osize': 7, 'stack': 1, 'ctx': 2}
    {'time': 10, 'depth': 7, 'side': 1, 'var': 'z0', 'var_bt': 0, 'kind': 'ext', 'fetched': ['stk', 1, 1, ['d2', ['p']], ['orig', 1]], 'frame_from': ['orig', 1], 'frame_to': ['orig', 1], 'trigger': ['d1', ['o', 'F', 'o', 'e', 'F', 'o', 'e']], 'piece_root': ['d2', ['p']], 'puller_root': ['d2', ['o', 'F', 'p']], 'psize': 5, 'osize': 6, 'stack': 1, 'ctx': 2}
```

## Smallest example of CYCLE

none found

## Skipped items

```
[30 k=2 kc=1] (x x) @ w≡(((⊤ ⊤) (⊤ ⊤)) ((⊤ ⊤) (⊤ ⊤))), x≡((λ⊤.((λ⊤.0) (0 0))) w);[] skipped (42025 d, 3469 c)
[180 k=2 kc=1] (λv1.((λv1.(v1 1)) v1)) @ v0≡(⊤ (λ⊤.(⊤ (λ⊤.1)))), v1≡(λ(λv0.v0).((v0 v0) (λ0.(λv0.⊤))));[] skipped (memory)
[246 k=2 kc=1] (v1 (λv1.((λv0.1) 0))) @ v0≡((⊤ ⊤) ((λ⊤.0) (⊤ ⊤))), v1≡(λv0.(λ⊤.((v0 v0) ⊤))), v2≡(λ⊤.0);[] skipped (9592200 d, 12395 c)
[40 k=2 kc=2] (λ⊤.0) @ x≡(((⊤ ⊤) (⊤ ⊤)) ((⊤ ⊤) (⊤ ⊤)));[((λ⊤.((λ⊤.0) (0 0))) x)] skipped (205 d, 561833 c)
[70 k=2 kc=2] (λv0.(⊤ ⊤)) @ v0≡(λ⊤.(λ0.1)), v1≡(λv0.(⊤ (0 (⊤ v0)))), v2≡(v1 (⊤ ⊤));[(λv2.v1), (λ⊤.(λ0.v2))] skipped (4 d, 719347 c)
[196 k=2 kc=2] ((v0 (v1 (v0 (v1 v1)))) v0) @ v0≡(λ⊤.⊤), v1≡(λv0.((⊤ (v0 v0)) v0));[] skipped (74088 d, 41 c)
[202 k=2 kc=2] (λv0.((⊤ (λv0.(0 (λ1.2)))) v2)) @ v0≡((⊤ (⊤ (λ⊤.⊤))) ⊤), v1≤(λv0.(v0 ⊤)), v2≤((v0 (v0 (λv1.(λv0.0)))) ⊤);[(λv1.0), (v2 ⊤)] skipped (68 d, 39299 c)
[220 k=2 kc=2] ((λv0.(λ⊤.0)) (λv0.((0 v1) v2))) @ v0≡(λ⊤.((0 ⊤) (λ⊤.0))), v1≡(λ⊤.(((λ⊤.1) (λ0.1)) 0)), v2≡(v1 (λv0.(v0 v0)));[(v1 v0)] skipped (3150 d, 266575 c)
[244 k=2 kc=2] ((λv1.v2) v2) @ v0≡((λ⊤.(λ0.((1 ⊤) 1))) ⊤), v1≡(v0 v0), v2≡(((λv0.0) v1) ((v0 ⊤) v1));[((v0 v1) v1), ⊤] skipped (memory)
[32 k=3 kc=1] x @ w≡(((⊤ ⊤) (⊤ ⊤)) ((⊤ ⊤) (⊤ ⊤))), x≡((λ⊤.((λ⊤.0) (0 0))) w);[w] skipped (33049 d, 124662 c)
[38 k=3 kc=1] ((λ⊤.0) ((λ⊤.((λ⊤.0) (0 0))) x)) @ x≡(((⊤ ⊤) (⊤ ⊤)) ((⊤ ⊤) (⊤ ⊤)));[] skipped (memory)
[134 k=3 kc=1] (λ⊤.(0 (λv0.(v1 0)))) @ v0≡(⊤ ⊤), v1≡(λv0.(λv0.(1 v0))), v2≡((λv0.v0) (λv1.v1));[(λv2.(⊤ v0))] skipped (32505 d, 51181 c)
[152 k=3 kc=1] ((λ⊤.(λ0.v1)) ((λv1.v1) (λv2.v0))) @ v0≡((⊤ ⊤) ⊤), v1≡((λ⊤.⊤) ⊤), v2≡((λv0.v0) (λv1.⊤));[v2] skipped (5330664 d, 1624 c)
[218 k=3 kc=1] (v1 v0) @ v0≡(⊤ ⊤), v1≡((λv0.0) (v0 ⊤)), v2≡(((v0 ⊤) v1) (v1 ⊤));[(v0 v0)] skipped (120 d, 48151 c)
[30 k=3 kc=2] (x x) @ w≡(((⊤ ⊤) (⊤ ⊤)) ((⊤ ⊤) (⊤ ⊤))), x≡((λ⊤.((λ⊤.0) (0 0))) w);[] skipped (memory)
[42 k=3 kc=2] ((λ⊤.0) ((λ⊤.((λ⊤.0) (0 0))) x)) @ x≡(λ⊤.(0 0));[] skipped (43560 d, 2 c)
[144 k=3 kc=2] ((λ⊤.(0 v0)) v0) @ v0≡((λ⊤.(0 ⊤)) (⊤ ⊤)), v1≡v0;[((λv1.v1) v0)] skipped (891 d, 32608 c)
[180 k=3 kc=2] (λv1.((λv1.(v1 1)) v1)) @ v0≡(⊤ (λ⊤.(⊤ (λ⊤.1)))), v1≡(λ(λv0.v0).((v0 v0) (λ0.(λv0.⊤))));[] skipped (memory)
[246 k=3 kc=2] (v1 (λv1.((λv0.1) 0))) @ v0≡((⊤ ⊤) ((λ⊤.0) (⊤ ⊤))), v1≡(λv0.(λ⊤.((v0 v0) ⊤))), v2≡(λ⊤.0);[] skipped (memory)
skipped_memory 6
skipped_size 13
[163 k=2 kc=1] ((v1 v0) (v1 (v1 v1))) @ v0≡((λ⊤.0) (λ⊤.(0 0))), v1≡(λv0.((0 (v0 0)) v0));[] skipped (memory)
[29 k=2 kc=2] x @ w≡(((⊤ ⊤) (⊤ ⊤)) ((⊤ ⊤) (⊤ ⊤))), x≡((λ⊤.((λ⊤.0) (0 0))) w);[] skipped (205 d, 561817 c)
[41 k=2 kc=2] (λ⊤.(0 0)) @ x≡(((⊤ ⊤) (⊤ ⊤)) ((⊤ ⊤) (⊤ ⊤)));[((λ⊤.((λ⊤.0) (0 0))) x)] skipped (42025 d, 561833 c)
[65 k=2 kc=2] (v1 v0) @ v0≡(λ⊤.⊤), v1≡(λ(λv0.0).((0 (0 (v0 ⊤))) ⊤)), v2≡((λv1.(λv0.(v0 v1))) v0);[(v2 ⊤), (λ⊤.(⊤ v2))] skipped (34 d, 5663380 c)
[245 k=2 kc=2] (v0 ((λv0.(λ⊤.(λv0.1))) (λ⊤.v0))) @ v0≡((λ⊤.((λ0.⊤) 0)) (⊤ ⊤));[⊤, v0] skipped (551124 d, 861 c)
[33 k=3 kc=1] (x w) @ w≡(((⊤ ⊤) (⊤ ⊤)) ((⊤ ⊤) (⊤ ⊤))), x≡((λ⊤.((λ⊤.0) (0 0))) w);[] skipped (561833 d, 3469 c)
[39 k=3 kc=1] ((λ⊤.(0 0)) ((λ⊤.((λ⊤.0) (0 0))) x)) @ x≡(((⊤ ⊤) (⊤ ⊤)) ((⊤ ⊤) (⊤ ⊤)));[] skipped (memory)
[57 k=3 kc=1] (λ⊤.(λ⊤.((0 v1) (λ1.v2)))) @ v0≡((⊤ ⊤) (⊤ ⊤)), v1≤(λv0.(λ⊤.((0 (v0 ⊤)) ⊤))), v2≡(λv0.(λv1.(λv0.v0)));[(λv0.v1)] skipped (756 d, 251381 c)
[105 k=3 kc=1] (λ⊤.((λv1.(λv1.v2)) v1)) @ v0≡⊤, v1≡((⊤ v0) (⊤ ⊤)), v2≡(v0 (λv1.(λv1.(1 (λv1.2)))));[] skipped (269304 d, 3251 c)
[117 k=3 kc=1] (λv1.(v0 (v1 (λv1.1)))) @ v0≡((⊤ ⊤) ((⊤ ⊤) ⊤)), v1≡(λ⊤.(λv0.(0 (λ1.v0))));[] skipped (256880 d, 126 c)
[207 k=3 kc=1] (λv2.((λv0.0) (((λ0.⊤) v0) 0))) @ v0≡(λ⊤.((λ0.⊤) (λ0.1))), v1≡(v0 ((⊤ v0) (⊤ ⊤))), v2≡(v1 v0);[((λv2.v2) v1)] skipped (memory)
[31 k=3 kc=2] x @ w≡(((⊤ ⊤) (⊤ ⊤)) ((⊤ ⊤) (⊤ ⊤))), x≡((λ⊤.((λ⊤.0) (0 0))) w);[x] skipped (memory)
[55 k=3 kc=2] ((λv1.v2) v0) @ v0≡(⊤ ⊤), v1≡v0, v2≡((λv1.⊤) ((v1 ⊤) (v1 ⊤)));[v1, (v0 v0)] skipped (1215 d, 153161 c)
[163 k=3 kc=2] ((v1 v0) (v1 (v1 v1))) @ v0≡((λ⊤.0) (λ⊤.(0 0))), v1≡(λv0.((0 (v0 0)) v0));[] skipped (memory)
[235 k=3 kc=2] (λv0.⊤) @ v0≡((⊤ ⊤) (⊤ (λ⊤.⊤))), v1≡(λv0.(λ⊤.v0));[(λv1.(λ0.0)), v0] skipped (5 d, 38632 c)
skipped_memory 5
skipped_size 10
[32 k=2 kc=1] x @ w≡(((⊤ ⊤) (⊤ ⊤)) ((⊤ ⊤) (⊤ ⊤))), x≡((λ⊤.((λ⊤.0) (0 0))) w);[w] skipped (205 d, 124662 c)
[38 k=2 kc=1] ((λ⊤.0) ((λ⊤.((λ⊤.0) (0 0))) x)) @ x≡(((⊤ ⊤) (⊤ ⊤)) ((⊤ ⊤) (⊤ ⊤)));[] skipped (6807888 d, 17 c)
[134 k=2 kc=1] (λ⊤.(0 (λv0.(v1 0)))) @ v0≡(⊤ ⊤), v1≡(λv0.(λv0.(1 v0))), v2≡((λv0.v0) (λv1.v1));[(λv2.(⊤ v0))] skipped (2145 d, 51181 c)
[152 k=2 kc=1] ((λ⊤.(λ0.v1)) ((λv1.v1) (λv2.v0))) @ v0≡((⊤ ⊤) ⊤), v1≡((λ⊤.⊤) ⊤), v2≡((λv0.v0) (λv1.⊤));[v2] skipped (439560 d, 1624 c)
[218 k=2 kc=1] (v1 v0) @ v0≡(⊤ ⊤), v1≡((λv0.0) (v0 ⊤)), v2≡(((v0 ⊤) v1) (v1 ⊤));[(v0 v0)] skipped (66 d, 48151 c)
[30 k=2 kc=2] (x x) @ w≡(((⊤ ⊤) (⊤ ⊤)) ((⊤ ⊤) (⊤ ⊤))), x≡((λ⊤.((λ⊤.0) (0 0))) w);[] skipped (42025 d, 561817 c)
[144 k=2 kc=2] ((λ⊤.(0 v0)) v0) @ v0≡((λ⊤.(0 ⊤)) (⊤ ⊤)), v1≡v0;[((λv1.v1) v0)] skipped (567 d, 32608 c)
[180 k=2 kc=2] (λv1.((λv1.(v1 1)) v1)) @ v0≡(⊤ (λ⊤.(⊤ (λ⊤.1)))), v1≡(λ(λv0.v0).((v0 v0) (λ0.(λv0.⊤))));[] skipped (memory)
[246 k=2 kc=2] (v1 (λv1.((λv0.1) 0))) @ v0≡((⊤ ⊤) ((λ⊤.0) (⊤ ⊤))), v1≡(λv0.(λ⊤.((v0 v0) ⊤))), v2≡(λ⊤.0);[] skipped (9592200 d, 83523 c)
[40 k=3 kc=1] (λ⊤.0) @ x≡(((⊤ ⊤) (⊤ ⊤)) ((⊤ ⊤) (⊤ ⊤)));[((λ⊤.((λ⊤.0) (0 0))) x)] skipped (33049 d, 3485 c)
[196 k=3 kc=1] ((v0 (v1 (v0 (v1 v1)))) v0) @ v0≡(λ⊤.⊤), v1≡(λv0.((⊤ (v0 v0)) v0));[] skipped (74088 d, 41 c)
[202 k=3 kc=1] (λv0.((⊤ (λv0.(0 (λ1.2)))) v2)) @ v0≡((⊤ (⊤ (λ⊤.⊤))) ⊤), v1≤(λv0.(v0 ⊤)), v2≤((v0 (v0 (λv1.(λv0.0)))) ⊤);[(λv1.0), (v2 ⊤)] skipped (68 d, 39299 c)
[220 k=3 kc=1] ((λv0.(λ⊤.0)) (λv0.((0 v1) v2))) @ v0≡(λ⊤.((0 ⊤) (λ⊤.0))), v1≡(λ⊤.(((λ⊤.1) (λ0.1)) 0)), v2≡(v1 (λv0.(v0 v0)));[(v1 v0)] skipped (478782 d, 1759 c)
[244 k=3 kc=1] ((λv1.v2) v2) @ v0≡((λ⊤.(λ0.((1 ⊤) 1))) ⊤), v1≡(v0 v0), v2≡(((λv0.0) v1) ((v0 ⊤) v1));[((v0 v1) v1), ⊤] skipped (memory)
[32 k=3 kc=2] x @ w≡(((⊤ ⊤) (⊤ ⊤)) ((⊤ ⊤) (⊤ ⊤))), x≡((λ⊤.((λ⊤.0) (0 0))) w);[w] skipped (33049 d, 20192346 c)
[38 k=3 kc=2] ((λ⊤.0) ((λ⊤.((λ⊤.0) (0 0))) x)) @ x≡(((⊤ ⊤) (⊤ ⊤)) ((⊤ ⊤) (⊤ ⊤)));[] skipped (memory)
[134 k=3 kc=2] (λ⊤.(0 (λv0.(v1 0)))) @ v0≡(⊤ ⊤), v1≡(λv0.(λv0.(1 v0))), v2≡((λv0.v0) (λv1.v1));[(λv2.(⊤ v0))] skipped (memory)
[152 k=3 kc=2] ((λ⊤.(λ0.v1)) ((λv1.v1) (λv2.v0))) @ v0≡((⊤ ⊤) ⊤), v1≡((λ⊤.⊤) ⊤), v2≡((λv0.v0) (λv1.⊤));[v2] skipped (5330664 d, 10226 c)
[218 k=3 kc=2] (v1 v0) @ v0≡(⊤ ⊤), v1≡((λv0.0) (v0 ⊤)), v2≡(((v0 ⊤) v1) (v1 ⊤));[(v0 v0)] skipped (120 d, 4784350 c)
skipped_memory 4
skipped_size 15
[39 k=2 kc=1] ((λ⊤.(0 0)) ((λ⊤.((λ⊤.0) (0 0))) x)) @ x≡(((⊤ ⊤) (⊤ ⊤)) ((⊤ ⊤) (⊤ ⊤)));[] skipped (memory)
[57 k=2 kc=1] (λ⊤.(λ⊤.((0 v1) (λ1.v2)))) @ v0≡((⊤ ⊤) (⊤ ⊤)), v1≤(λv0.(λ⊤.((0 (v0 ⊤)) ⊤))), v2≡(λv0.(λv1.(λv0.v0)));[(λv0.v1)] skipped (756 d, 251381 c)
[105 k=2 kc=1] (λ⊤.((λv1.(λv1.v2)) v1)) @ v0≡⊤, v1≡((⊤ v0) (⊤ ⊤)), v2≡(v0 (λv1.(λv1.(1 (λv1.2)))));[] skipped (98392 d, 3251 c)
[117 k=2 kc=1] (λv1.(v0 (v1 (λv1.1)))) @ v0≡((⊤ ⊤) ((⊤ ⊤) ⊤)), v1≡(λ⊤.(λv0.(0 (λ1.v0))));[] skipped (172380 d, 126 c)
[207 k=2 kc=1] (λv2.((λv0.0) (((λ0.⊤) v0) 0))) @ v0≡(λ⊤.((λ0.⊤) (λ0.1))), v1≡(v0 ((⊤ v0) (⊤ ⊤))), v2≡(v1 v0);[((λv2.v2) v1)] skipped (memory)
[31 k=2 kc=2] x @ w≡(((⊤ ⊤) (⊤ ⊤)) ((⊤ ⊤) (⊤ ⊤))), x≡((λ⊤.((λ⊤.0) (0 0))) w);[x] skipped (memory)
[55 k=2 kc=2] ((λv1.v2) v0) @ v0≡(⊤ ⊤), v1≡v0, v2≡((λv1.⊤) ((v1 ⊤) (v1 ⊤)));[v1, (v0 v0)] skipped (195 d, 153161 c)
[163 k=2 kc=2] ((v1 v0) (v1 (v1 v1))) @ v0≡((λ⊤.0) (λ⊤.(0 0))), v1≡(λv0.((0 (v0 0)) v0));[] skipped (memory)
[235 k=2 kc=2] (λv0.⊤) @ v0≡((⊤ ⊤) (⊤ (λ⊤.⊤))), v1≡(λv0.(λ⊤.v0));[(λv1.(λ0.0)), v0] skipped (5 d, 38632 c)
[29 k=3 kc=1] x @ w≡(((⊤ ⊤) (⊤ ⊤)) ((⊤ ⊤) (⊤ ⊤))), x≡((λ⊤.((λ⊤.0) (0 0))) w);[] skipped (33049 d, 3469 c)
[41 k=3 kc=1] (λ⊤.(0 0)) @ x≡(((⊤ ⊤) (⊤ ⊤)) ((⊤ ⊤) (⊤ ⊤)));[((λ⊤.((λ⊤.0) (0 0))) x)] skipped (memory)
[245 k=3 kc=1] (v0 ((λv0.(λ⊤.(λv0.1))) (λ⊤.v0))) @ v0≡((λ⊤.((λ0.⊤) 0)) (⊤ ⊤));[⊤, v0] skipped (551124 d, 321 c)
[33 k=3 kc=2] (x w) @ w≡(((⊤ ⊤) (⊤ ⊤)) ((⊤ ⊤) (⊤ ⊤))), x≡((λ⊤.((λ⊤.0) (0 0))) w);[] skipped (561833 d, 561817 c)
[39 k=3 kc=2] ((λ⊤.(0 0)) ((λ⊤.((λ⊤.0) (0 0))) x)) @ x≡(((⊤ ⊤) (⊤ ⊤)) ((⊤ ⊤) (⊤ ⊤)));[] skipped (memory)
[57 k=3 kc=2] (λ⊤.(λ⊤.((0 v1) (λ1.v2)))) @ v0≡((⊤ ⊤) (⊤ ⊤)), v1≤(λv0.(λ⊤.((0 (v0 ⊤)) ⊤))), v2≡(λv0.(λv1.(λv0.v0)));[(λv0.v1)] skipped (756 d, 251381 c)
[105 k=3 kc=2] (λ⊤.((λv1.(λv1.v2)) v1)) @ v0≡⊤, v1≡((⊤ v0) (⊤ ⊤)), v2≡(v0 (λv1.(λv1.(1 (λv1.2)))));[] skipped (269304 d, 8919 c)
[117 k=3 kc=2] (λv1.(v0 (v1 (λv1.1)))) @ v0≡((⊤ ⊤) ((⊤ ⊤) ⊤)), v1≡(λ⊤.(λv0.(0 (λ1.v0))));[] skipped (256880 d, 126 c)
[207 k=3 kc=2] (λv2.((λv0.0) (((λ0.⊤) v0) 0))) @ v0≡(λ⊤.((λ0.⊤) (λ0.1))), v1≡(v0 ((⊤ v0) (⊤ ⊤))), v2≡(v1 v0);[((λv2.v2) v1)] skipped (memory)
[231 k=3 kc=2] (λ⊤.v0) @ v0≡((λ⊤.(λ0.((0 ⊤) ⊤))) ⊤), v1≡(λv0.(λv0.v0)), v2≡((⊤ ⊤) v1);[v2, v2] skipped (13 d, 76531 c)
skipped_memory 7
skipped_size 12
[196 k=2 kc=1] ((v0 (v1 (v0 (v1 v1)))) v0) @ v0≡(λ⊤.⊤), v1≡(λv0.((⊤ (v0 v0)) v0));[] skipped (74088 d, 41 c)
[202 k=2 kc=1] (λv0.((⊤ (λv0.(0 (λ1.2)))) v2)) @ v0≡((⊤ (⊤ (λ⊤.⊤))) ⊤), v1≤(λv0.(v0 ⊤)), v2≤((v0 (v0 (λv1.(λv0.0)))) ⊤);[(λv1.0), (v2 ⊤)] skipped (68 d, 39299 c)
[244 k=2 kc=1] ((λv1.v2) v2) @ v0≡((λ⊤.(λ0.((1 ⊤) 1))) ⊤), v1≡(v0 v0), v2≡(((λv0.0) v1) ((v0 ⊤) v1));[((v0 v1) v1), ⊤] skipped (10086 d, 104217 c)
[32 k=2 kc=2] x @ w≡(((⊤ ⊤) (⊤ ⊤)) ((⊤ ⊤) (⊤ ⊤))), x≡((λ⊤.((λ⊤.0) (0 0))) w);[w] skipped (205 d, 20192346 c)
[38 k=2 kc=2] ((λ⊤.0) ((λ⊤.((λ⊤.0) (0 0))) x)) @ x≡(((⊤ ⊤) (⊤ ⊤)) ((⊤ ⊤) (⊤ ⊤)));[] skipped (memory)
[134 k=2 kc=2] (λ⊤.(0 (λv0.(v1 0)))) @ v0≡(⊤ ⊤), v1≡(λv0.(λv0.(1 v0))), v2≡((λv0.v0) (λv1.v1));[(λv2.(⊤ v0))] skipped (memory)
[152 k=2 kc=2] ((λ⊤.(λ0.v1)) ((λv1.v1) (λv2.v0))) @ v0≡((⊤ ⊤) ⊤), v1≡((λ⊤.⊤) ⊤), v2≡((λv0.v0) (λv1.⊤));[v2] skipped (439560 d, 10226 c)
[218 k=2 kc=2] (v1 v0) @ v0≡(⊤ ⊤), v1≡((λv0.0) (v0 ⊤)), v2≡(((v0 ⊤) v1) (v1 ⊤));[(v0 v0)] skipped (66 d, 4784350 c)
[30 k=3 kc=1] (x x) @ w≡(((⊤ ⊤) (⊤ ⊤)) ((⊤ ⊤) (⊤ ⊤))), x≡((λ⊤.((λ⊤.0) (0 0))) w);[] skipped (memory)
[42 k=3 kc=1] ((λ⊤.0) ((λ⊤.((λ⊤.0) (0 0))) x)) @ x≡(λ⊤.(0 0));[] skipped (43560 d, 2 c)
[180 k=3 kc=1] (λv1.((λv1.(v1 1)) v1)) @ v0≡(⊤ (λ⊤.(⊤ (λ⊤.1)))), v1≡(λ(λv0.v0).((v0 v0) (λ0.(λv0.⊤))));[] skipped (memory)
[246 k=3 kc=1] (v1 (λv1.((λv0.1) 0))) @ v0≡((⊤ ⊤) ((λ⊤.0) (⊤ ⊤))), v1≡(λv0.(λ⊤.((v0 v0) ⊤))), v2≡(λ⊤.0);[] skipped (memory)
[40 k=3 kc=2] (λ⊤.0) @ x≡(((⊤ ⊤) (⊤ ⊤)) ((⊤ ⊤) (⊤ ⊤)));[((λ⊤.((λ⊤.0) (0 0))) x)] skipped (33049 d, 561833 c)
[70 k=3 kc=2] (λv0.(⊤ ⊤)) @ v0≡(λ⊤.(λ0.1)), v1≡(λv0.(⊤ (0 (⊤ v0)))), v2≡(v1 (⊤ ⊤));[(λv2.v1), (λ⊤.(λ0.v2))] skipped (4 d, 719347 c)
[196 k=3 kc=2] ((v0 (v1 (v0 (v1 v1)))) v0) @ v0≡(λ⊤.⊤), v1≡(λv0.((⊤ (v0 v0)) v0));[] skipped (74088 d, 41 c)
[202 k=3 kc=2] (λv0.((⊤ (λv0.(0 (λ1.2)))) v2)) @ v0≡((⊤ (⊤ (λ⊤.⊤))) ⊤), v1≤(λv0.(v0 ⊤)), v2≤((v0 (v0 (λv1.(λv0.0)))) ⊤);[(λv1.0), (v2 ⊤)] skipped (68 d, 39299 c)
[220 k=3 kc=2] ((λv0.(λ⊤.0)) (λv0.((0 v1) v2))) @ v0≡(λ⊤.((0 ⊤) (λ⊤.0))), v1≡(λ⊤.(((λ⊤.1) (λ0.1)) 0)), v2≡(v1 (λv0.(v0 v0)));[(v1 v0)] skipped (478782 d, 266575 c)
[244 k=3 kc=2] ((λv1.v2) v2) @ v0≡((λ⊤.(λ0.((1 ⊤) 1))) ⊤), v1≡(v0 v0), v2≡(((λv0.0) v1) ((v0 ⊤) v1));[((v0 v1) v1), ⊤] skipped (memory)
skipped_memory 6
skipped_size 12
[41 k=2 kc=1] (λ⊤.(0 0)) @ x≡(((⊤ ⊤) (⊤ ⊤)) ((⊤ ⊤) (⊤ ⊤)));[((λ⊤.((λ⊤.0) (0 0))) x)] skipped (42025 d, 3485 c)
[245 k=2 kc=1] (v0 ((λv0.(λ⊤.(λv0.1))) (λ⊤.v0))) @ v0≡((λ⊤.((λ0.⊤) 0)) (⊤ ⊤));[⊤, v0] skipped (551124 d, 321 c)
[33 k=2 kc=2] (x w) @ w≡(((⊤ ⊤) (⊤ ⊤)) ((⊤ ⊤) (⊤ ⊤))), x≡((λ⊤.((λ⊤.0) (0 0))) w);[] skipped (3485 d, 561817 c)
[39 k=2 kc=2] ((λ⊤.(0 0)) ((λ⊤.((λ⊤.0) (0 0))) x)) @ x≡(((⊤ ⊤) (⊤ ⊤)) ((⊤ ⊤) (⊤ ⊤)));[] skipped (memory)
[57 k=2 kc=2] (λ⊤.(λ⊤.((0 v1) (λ1.v2)))) @ v0≡((⊤ ⊤) (⊤ ⊤)), v1≤(λv0.(λ⊤.((0 (v0 ⊤)) ⊤))), v2≡(λv0.(λv1.(λv0.v0)));[(λv0.v1)] skipped (756 d, 251381 c)
[105 k=2 kc=2] (λ⊤.((λv1.(λv1.v2)) v1)) @ v0≡⊤, v1≡((⊤ v0) (⊤ ⊤)), v2≡(v0 (λv1.(λv1.(1 (λv1.2)))));[] skipped (98392 d, 8919 c)
[117 k=2 kc=2] (λv1.(v0 (v1 (λv1.1)))) @ v0≡((⊤ ⊤) ((⊤ ⊤) ⊤)), v1≡(λ⊤.(λv0.(0 (λ1.v0))));[] skipped (172380 d, 126 c)
[207 k=2 kc=2] (λv2.((λv0.0) (((λ0.⊤) v0) 0))) @ v0≡(λ⊤.((λ0.⊤) (λ0.1))), v1≡(v0 ((⊤ v0) (⊤ ⊤))), v2≡(v1 v0);[((λv2.v2) v1)] skipped (memory)
[231 k=2 kc=2] (λ⊤.v0) @ v0≡((λ⊤.(λ0.((0 ⊤) ⊤))) ⊤), v1≡(λv0.(λv0.v0)), v2≡((⊤ ⊤) v1);[v2, v2] skipped (7 d, 76531 c)
[31 k=3 kc=1] x @ w≡(((⊤ ⊤) (⊤ ⊤)) ((⊤ ⊤) (⊤ ⊤))), x≡((λ⊤.((λ⊤.0) (0 0))) w);[x] skipped (33049 d, 20608 c)
[163 k=3 kc=1] ((v1 v0) (v1 (v1 v1))) @ v0≡((λ⊤.0) (λ⊤.(0 0))), v1≡(λv0.((0 (v0 0)) v0));[] skipped (memory)
[29 k=3 kc=2] x @ w≡(((⊤ ⊤) (⊤ ⊤)) ((⊤ ⊤) (⊤ ⊤))), x≡((λ⊤.((λ⊤.0) (0 0))) w);[] skipped (33049 d, 561817 c)
[41 k=3 kc=2] (λ⊤.(0 0)) @ x≡(((⊤ ⊤) (⊤ ⊤)) ((⊤ ⊤) (⊤ ⊤)));[((λ⊤.((λ⊤.0) (0 0))) x)] skipped (memory)
[65 k=3 kc=2] (v1 v0) @ v0≡(λ⊤.⊤), v1≡(λ(λv0.0).((0 (0 (v0 ⊤))) ⊤)), v2≡((λv1.(λv0.(v0 v1))) v0);[(v2 ⊤), (λ⊤.(⊤ v2))] skipped (74 d, 5663380 c)
[245 k=3 kc=2] (v0 ((λv0.(λ⊤.(λv0.1))) (λ⊤.v0))) @ v0≡((λ⊤.((λ0.⊤) 0)) (⊤ ⊤));[⊤, v0] skipped (551124 d, 861 c)
skipped_memory 4
skipped_size 11
```
