# Claims Registry — Yang-Mills Mass Gap

## Claim 1: τ(G) ≥ 81 for non-planar G
- **Statement**: For any connected non-planar graph G, τ(G) ≥ min(τ(K_{3,3}), τ(K_5)) = 81
- **Assumptions**: Kuratowski's theorem, deletion-contraction monotonicity
- **Dependencies**: K33.lean, K5.lean, Kirchhoff.lean
- **Status**: PROVED (Lean-verified for τ values, axiom for Kuratowski)

## Claim 2: Extension graph E(P) is connected
- **Statement**: For any finite poset P, E(P) is connected
- **Assumptions**: None beyond definitions
- **Dependencies**: ExtGraph.lean
- **Status**: PROVED (Lean-verified)

## Claim 3: λ₁(E(P)) > 0 for each finite P
- **Statement**: The graph Laplacian of E(P) has spectral gap > 0
- **Assumptions**: E(P) connected
- **Dependencies**: Claim 2
- **Status**: PROVED (immediate from connectivity)

## Claim 4: Uniform spectral gap λ₁(E(P)) ≥ c > 0
- **Statement**: There exists c > 0 independent of |P| such that λ₁(E(P)) ≥ c
- **Assumptions**: Bounded Hasse degree Δ_max
- **Dependencies**: Claim 3
- **Status**: **FALSE** — computational evidence shows λ₁ ~ π²/n² for ALL Hasse degrees 1 through n-2. The gap vanishes universally.
- **Evidence**: spectral_gap binary, tested on all posets n=2..6 (129K+ posets at n=6)

## Claim 5: Exponential clustering of rigid linexts
- **Statement**: |R⁺ - R⁻|/(2k) ≤ C·exp(-m·d_H(a,b)) with m > 0 uniform in ρ
- **Assumptions**: Was conditional on Claim 4
- **Dependencies**: Claim 4 (now falsified)
- **Status**: **BLOCKED** — depends on a false claim. Needs a different operator.

## Claim 6: Continuum mass gap
- **Statement**: spec(M²) ⊆ {0} ∪ [Δ², ∞) with Δ > 0
- **Assumptions**: Exponential clustering, Lorentzian reconstruction
- **Dependencies**: Claim 5 (blocked), Lorentzian reconstruction (open problem)
- **Status**: **BLOCKED** — two dependencies are unresolved

## Claim 7: Wightman spectral condition
- **Statement**: spec(P^μ) ⊆ V̄₊
- **Assumptions**: Needs P^μ defined
- **Dependencies**: P^μ never constructed
- **Status**: **GAP** — spatial momentum operators not defined

## Claim 8: Vacuum state convergence
- **Statement**: ω(O) = lim_{n→∞} ⟨Ω_n|O|Ω_n⟩ exists for all O ∈ 𝔄
- **Assumptions**: Balance Preservation, bounded causal diamond
- **Dependencies**: Claim 2
- **Status**: **OVERSTATED** — proof gives subsequential convergence of Poisson-averaged expectations, not full pointwise convergence
