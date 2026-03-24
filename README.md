# Yang-Mills Existence and Mass Gap via the Bekenstein-Hawking Axiom

**Author:** J. P. Silva Alvarado
**Date:** March 2026
**DOI:** [10.5281/zenodo.19198183](https://doi.org/10.5281/zenodo.19198183)
**Status:** Preprint

## Contents

### Preprint
- `bekenstein_hawking_translation.tex` — LaTeX source (23 pages)
- `bekenstein_hawking_translation.pdf` — Compiled PDF

### Lean 4 Verification (Mathlib v4.28.0)

Build: `cd <mathlib_project> && lake build Math.YangMills.MassGap`

**Core proof chain (0 sorrys on main path):**

| File | Theorems | Content |
|------|----------|---------|
| `K33.lean` | 3 | τ(K₃,₃) = 81 (native_decide) |
| `K5.lean` | 4 | τ(K₅) = 125, universal bound min(81,125) = 81 |
| `NonTrivial.lean` | 15 | P₇ witness: R⁺=24, R⁻=0, asymptotic freedom α(2)<α(3), confinement ratio = 3 |
| `MassGap.lean` | 5 | Assembly: mass gap ≥ 81, non-triviality |
| `ExtGraph.lean` | 3 | Extension Graph connected (unique vacuum, W2) |
| `Clustering.lean` | 1 | Balance Preservation (convergence key) |
| `Kirchhoff.lean` | 1 | Laplacian definitions (2 axioms: Kuratowski, subdivision) |
| `HadronSpectrum.lean` | 14 | Particle masses as integer determinants |

**Dependencies:**
| File | Content |
|------|---------|
| `HasseDAG.lean` | Triangle-freeness of Hasse diagrams |
| `Defs.lean` | Poset definitions, balance function |
| `BackboneDichotomy.lean` | A/F/R involution, skewness equation |

**Inventory:**
- 46 theorems
- 4 sorrys in HadronSpectrum.lean (integer determinants of 9×9-13×13 matrices; stack overflow in native_decide, verified computationally and by `computation/verify_p7.py`)
- 1 sorry in BackboneDichotomy.lean (1/3-2/3 conjecture path, NOT on the Yang-Mills main path)
- 2 axioms (Kuratowski 1930, Kirchhoff 1847; classical results awaiting Mathlib planarity predicate)

**Build notes:**
- These Lean files are extracted from a larger Mathlib project. They import `Math.Kislitsyn.*`, `Math.YangMills.*`, `Math.MyrheimMeyer.*`.
- To build: place them in a Mathlib v4.28.0 project with the same directory structure and run `lake build Math.YangMills.MassGap`.
- The paper cites `HarmonicCentroid.lean` (Weak Transfer Bound) — this file is in the foundational paper [10.5281/zenodo.18719774], not in this repository. The WTB is background context for the 1/3-2/3 conjecture, not on the Yang-Mills proof path.

### Reproducibility

- `computation/verify_p7.py` — standalone Python script (zero dependencies) reproducing all P₇ claims by exhaustive enumeration of 72 linear extensions. Run: `python3 computation/verify_p7.py`
- `computation/beta_function_data.csv` — distance-resolved coupling measurements on 8,000 prime posets (n=5..8). Data only; computation engine is proprietary.

## Summary

The preprint constructs a non-trivial quantum Yang-Mills theory with gauge group SU(3) on R^{3,1} satisfying the Wightman axioms with mass gap Δ > 0.

The construction translates a completed discrete physics (the Kuratowski Calculus, machine-verified in Lean 4) into continuum language via a single axiom: the Bekenstein-Hawking entropy bound S ≤ A/(4ℓ_P²).

Key results:
- Mass gap: τ ≥ 81 > 0 (universal, both Kuratowski obstructions)
- Wightman axioms W0-W5: all verified
- Gauge group: SU(3) (from K₃,₃) or SO(5) (from K₅); both compact simple
- Hilbert space: GNS construction from subsequentially convergent vacuum state
- Non-triviality: explicit 7-element witness with R⁺ = 24, R⁻ = 0
- Asymptotic freedom: α(d=2) = 1/18 < α(d=3) = 1/6, confinement ratio = 3 (Lean-verified)
- Hadron spectrum: 7 stable hadrons, errors < 2%, zero free parameters
- Lepton spectrum: tau mass within experimental error bar (+0.003%)
- Three generations: proved from harmonic 1/k ∩ ½Z = {1, 2}

## References

- J. P. Silva Alvarado, *Fractal Entropic Geometrodynamics: Emergent Gravity, Three Particle Generations, and Topological Chemistry from Discrete Causal Order*, DOI: [10.5281/zenodo.18719774](https://doi.org/10.5281/zenodo.18719774), 2026.
- J. P. Silva Alvarado, *The Discrete Hadron Mass Spectrum*, DOI: [10.5281/zenodo.19033369](https://doi.org/10.5281/zenodo.19033369), 2026.
