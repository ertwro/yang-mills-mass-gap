# Gaps Registry — Yang-Mills Mass Gap

## Gap 1: The wrong operator for the mass gap
- **Location**: §8 (Mass Gap), Theorem 8.1 (Exponential Clustering)
- **Why current proof fails**: The extension graph Laplacian λ₁(E(P)) → 0 as π²/n², regardless of Hasse degree. Computational evidence on all posets n=2..6 confirms this. Bounded Hasse degree does NOT rescue the gap. The extension graph spectral gap is the wrong quantity for a uniform mass gap.
- **What would fix it**: Find a DIFFERENT operator whose spectral gap is uniform. Candidates:
  1. The causal set d'Alembertian □_C (Sorkin's operator on functions on the causal set, not on linear extensions)
  2. A transfer matrix T acting on a restricted state space (not all linexts — perhaps only the rigid sector)
  3. A renormalization-group fixed-point Hamiltonian that emerges in the continuum limit
- **Priority**: CRITICAL — this is the load-bearing gap. Everything downstream depends on it.

## Gap 2: Lorentzian reconstruction
- **Location**: §7 (Vacuum/Continuum), passage from discrete correlators to Wightman functions
- **Why current proof fails**: No rigorous theorem takes discrete Lorentzian correlators to continuum QFT. OS reconstruction requires Euclidean signature. Causal sets have no natural Wick rotation.
- **What would fix it**: Either (a) a Lorentzian reconstruction theorem for causal sets, (b) a rigorous Wick rotation for causal set correlators, or (c) a direct algebraic QFT construction.
- **Priority**: CRITICAL — but depends on Gap 1 being resolved first.

## Gap 3: P^μ not defined
- **Location**: §9 (Wightman W2), spectral condition
- **Why current proof fails**: Paper defines H_ρ (graph Laplacian = P⁰) but never constructs P¹, P², P³. Joint spectral condition requires all four operators.
- **What would fix it**: Construct P^μ from the Poisson process translation invariance. Show strong continuity of U(a) = exp(iP^μ a_μ). Prove joint spectrum in V̄₊.
- **Priority**: HIGH — but may cascade from Gap 2 if reconstruction is done properly.

## Gap 4: Vacuum convergence overstated
- **Location**: §7 (Theorem 5.1)
- **Why current proof fails**: Theorem claims full limit, proof gives subsequential convergence of Poisson-averaged (annealed) expectations.
- **What would fix it**: (a) Uniqueness of cluster point via ergodicity, (b) concentration inequality for quenched-to-annealed. OR: honestly restate as subsequential convergence.
- **Priority**: MODERATE — restatement suffices for GNS.

## Gap 5: "For any G" quantifier mismatch
- **Location**: Main theorem, §1
- **Why current proof fails**: Clay asks for universal quantifier over all compact simple G. Paper only has SU(3) and SO(5).
- **What would fix it**: Either extend construction to all G, or drop Clay claim.
- **Priority**: HIGH — but orthogonal to the physics gaps.

## Gap 6: Single-axiom overclaim
- **Location**: Title, §4
- **Why current proof fails**: Bounded degree theorem requires BH + local area growth + independent DOF.
- **What would fix it**: Acknowledge extra hypotheses explicitly.
- **Priority**: LOW — restatement only.
