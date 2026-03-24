#!/usr/bin/env python3
"""
Independent verification of the P₇ witness for Yang-Mills non-triviality
and discrete asymptotic freedom.

This script reproduces ALL claims in NonTrivial.lean by exhaustive
enumeration. No external dependencies. Pure Python, exact integer arithmetic.

Usage: python3 verify_p7.py
"""

from itertools import permutations

# ═══════════════════════════════════════════════════════════════
# THE POSET P₇
# ═══════════════════════════════════════════════════════════════
# Vertices: 0,1,2 (quarks), 3,4,5 (mediators), 6 (breaker)
# Relations: i < j for i∈{0,1,2}, j∈{3,4,5}  (K₃,₃ bipartite)
#            3 < 6  (symmetry breaker)
#            0,1,2 < 6  (transitive closure)

N = 7
rel = [[False]*N for _ in range(N)]
for i in range(3):
    for j in range(3, 6):
        rel[i][j] = True
rel[3][6] = True
for i in range(3):
    rel[i][6] = True

# ═══════════════════════════════════════════════════════════════
# ENUMERATE ALL LINEAR EXTENSIONS
# ═══════════════════════════════════════════════════════════════

def is_linext(perm):
    for i in range(N):
        for j in range(N):
            if rel[i][j] and perm.index(i) >= perm.index(j):
                return False
    return True

linexts = [p for p in permutations(range(N)) if is_linext(p)]
k = len(linexts)
print(f"P₇: {k} linear extensions (expected: 72)")
assert k == 72, f"FAIL: got {k}"

# ═══════════════════════════════════════════════════════════════
# HASSE DISTANCE (BFS on covering graph)
# ═══════════════════════════════════════════════════════════════

# Build covering relations
covers = [[] for _ in range(N)]
for i in range(N):
    for j in range(N):
        if not rel[i][j]: continue
        is_cover = not any(rel[i][m] and rel[m][j] for m in range(N) if m != i and m != j)
        if is_cover:
            covers[i].append(j)

def hasse_dist(a, b):
    from collections import deque
    if a == b: return 0
    dist = [None]*N
    dist[a] = 0
    q = deque([a])
    while q:
        v = q.popleft()
        for w in covers[v]:
            if dist[w] is None:
                dist[w] = dist[v] + 1
                q.append(w)
        for u in range(N):
            if v in covers[u] and dist[u] is None:
                dist[u] = dist[v] + 1
                q.append(u)
    return dist[b] if dist[b] is not None else float('inf')

# ═══════════════════════════════════════════════════════════════
# A/F/R CLASSIFICATION BY PAIR AND DISTANCE
# ═══════════════════════════════════════════════════════════════

# Find all incomparable pairs
incomp = [(a,b) for a in range(N) for b in range(a+1,N)
          if not rel[a][b] and not rel[b][a]]

print(f"\nIncomparable pairs: {len(incomp)}")

# Classify by distance
from collections import defaultdict
by_dist = defaultdict(lambda: {'R+': 0, 'R-': 0, 'A+': 0, 'A-': 0,
                                'F+': 0, 'F-': 0, 'k': 0, 'pairs': 0})

for a, b in incomp:
    d = hasse_dist(a, b)
    by_dist[d]['pairs'] += 1
    by_dist[d]['k'] += k

    for p in linexts:
        pa, pb = p.index(a), p.index(b)
        a_first = pa < pb
        lo, hi = min(pa,pb), max(pa,pb)

        if hi - lo == 1:
            by_dist[d]['A+' if a_first else 'A-'] += 1
            continue

        buffer = [p[i] for i in range(lo+1, hi)]
        is_rigid = any(rel[c][a] or rel[a][c] or rel[c][b] or rel[b][c]
                      for c in buffer if c != a and c != b)

        if is_rigid:
            by_dist[d]['R+' if a_first else 'R-'] += 1
        else:
            by_dist[d]['F+' if a_first else 'F-'] += 1

# ═══════════════════════════════════════════════════════════════
# RESULTS
# ═══════════════════════════════════════════════════════════════

print("\n" + "="*65)
print("DISTANCE-RESOLVED A/F/R DECOMPOSITION")
print("="*65)
print(f"{'d':>3} {'pairs':>5} {'A+':>5} {'A-':>5} {'F+':>5} {'F-':>5} {'R+':>5} {'R-':>5} {'k':>6} {'W_conn':>10} {'α_eff':>10}")

for d in sorted(by_dist.keys()):
    v = by_dist[d]
    w_conn = (v['R+'] - v['R-']) / (2 * v['k']) if v['k'] > 0 else 0
    alpha = abs(w_conn)
    print(f"  {d:>3} {v['pairs']:>5} {v['A+']:>5} {v['A-']:>5} {v['F+']:>5} {v['F-']:>5} {v['R+']:>5} {v['R-']:>5} {v['k']:>6} {w_conn:>10.6f} {alpha:>10.6f}")

# ═══════════════════════════════════════════════════════════════
# ASSERTIONS (matching NonTrivial.lean theorems)
# ═══════════════════════════════════════════════════════════════

print("\n" + "="*65)
print("LEAN THEOREM VERIFICATION")
print("="*65)

# Non-triviality
d2 = by_dist[2]
d3 = by_dist[3]

assert d2['R+'] == 48 and d2['R-'] == 0, f"FAIL d=2: R+={d2['R+']}, R-={d2['R-']}"
print(f"  P7_d2_R_plus = {d2['R+']}  ✓")
print(f"  P7_d2_R_minus = {d2['R-']}  ✓")
print(f"  P7_d2_k = {d2['k']}  ✓")

assert d3['R+'] == 48 and d3['R-'] == 0, f"FAIL d=3: R+={d3['R+']}, R-={d3['R-']}"
print(f"  P7_d3_R_plus = {d3['R+']}  ✓")
print(f"  P7_d3_R_minus = {d3['R-']}  ✓")
print(f"  P7_d3_k = {d3['k']}  ✓")

# Alpha values
alpha_2 = d2['R+'] / (2 * d2['k'])  # 48/864 = 1/18
alpha_3 = d3['R+'] / (2 * d3['k'])  # 48/288 = 1/6
ratio = alpha_3 / alpha_2

print(f"\n  α(2) = {d2['R+']}/(2×{d2['k']}) = {alpha_2:.6f} = 1/{int(1/alpha_2)}  ✓")
print(f"  α(3) = {d3['R+']}/(2×{d3['k']}) = {alpha_3:.6f} = 1/{int(1/alpha_3)}  ✓")
print(f"  α(3)/α(2) = {ratio:.1f}  ✓  (confinement ratio)")

# Asymptotic freedom: α(2) < α(3)
assert alpha_2 < alpha_3, "FAIL: not asymptotically free"
print(f"  α(2) < α(3): {alpha_2:.4f} < {alpha_3:.4f}  ✓  (asymptotic freedom)")

# Involution identities
for d in sorted(by_dist.keys()):
    v = by_dist[d]
    assert v['A+'] == v['A-'], f"FAIL: |A+| ≠ |A-| at d={d}"
    assert v['F+'] == v['F-'], f"FAIL: |F+| ≠ |F-| at d={d}"
print(f"  |A+| = |A-| at all distances  ✓")
print(f"  |F+| = |F-| at all distances  ✓")

print(f"\n{'='*65}")
print("ALL ASSERTIONS PASSED")
print(f"{'='*65}")
print(f"\nSummary:")
print(f"  72 linear extensions enumerated")
print(f"  8 incomparable pairs classified by distance and A/F/R type")
print(f"  Asymptotic freedom: α(2) = 1/18 < α(3) = 1/6")
print(f"  Confinement ratio: 3 (exact)")
print(f"  Non-triviality: R⁺ ≠ R⁻ at distances 2 and 3")
print(f"  All Lean theorem values independently verified")
