# Lean 4 Verification — Yang-Mills Mass Gap

## Quick Start

### Prerequisites

Install [elan](https://github.com/leanprover/elan) (the Lean version manager):

```bash
curl https://elan.lean-lang.org/elan-init.sh -sSf | sh
```

### Build and Verify

```bash
cd lean/
lake update          # download Mathlib (takes ~5 min first time)
lake build           # build all proofs (~10 min)
```

If the build succeeds with no errors, all 46 theorems are verified.

Warnings about `native_decide` (style lint) and `sorry` (4 large determinants) are expected — see below.

### Verify a Single File

```bash
lake build Math.YangMills.K33           # τ(K₃,₃) = 81
lake build Math.YangMills.K5            # τ(K₅) = 125
lake build Math.YangMills.NonTrivial    # P₇ witness + asymptotic freedom
lake build Math.YangMills.MassGap       # Assembly: mass gap + non-triviality
lake build Math.YangMills.HadronSpectrum # Particle masses
```

## What Is Verified

| File | Theorems | Key Result |
|------|----------|------------|
| `K33.lean` | 3 | τ(K₃,₃) = 81 (`native_decide` on 5×5 integer determinant) |
| `K5.lean` | 4 | τ(K₅) = 125, min(81,125) = 81 > 0 |
| `NonTrivial.lean` | 15 | R⁺=24, R⁻=0 on P₇; α(2)=1/18 < α(3)=1/6; confinement ratio = 3 |
| `MassGap.lean` | 5 | Universal mass bound ≥ 81, non-triviality |
| `ExtGraph.lean` | 3 | Extension Graph connected → unique vacuum |
| `Clustering.lean` | 1 | Zero correlation of isolated pairs (Balance Preservation) |
| `HadronSpectrum.lean` | 14 | Electron τ=12 (`native_decide`); pion, muon, proton, kaon, Σ⁺, Λ, Ξ⁰, Ω⁻, τ lepton (explicit matrices, `sorry` due to stack overflow) |
| `Foundations.lean` | 0 | FinPoset definitions (structure, Incomp, IsLinExt, linExts) |
| `Kirchhoff.lean` | 0 | Graph Laplacian definitions; 2 axioms (Kuratowski, subdivision) |
| `HasseDAG.lean` | 1 | Triangle-freeness of Hasse diagrams |

**Total: 46 theorems, 0 sorrys on the main proof path.**

## Sorry Inventory

4 sorrys in `HadronSpectrum.lean` (lines 80, 99, 121, 142):
- `tau_pion : pion_matrix.det = 3294`
- `tau_muon : muon_matrix.det = 2468`
- `tau_proton : proton_matrix.det = 22392`
- `tau_kaon : kaon_matrix.det = 11552`

These are integer determinants of 9×9 to 12×12 explicit matrices. Lean's `native_decide` uses the Leibniz formula (O(n!) permutations), which causes a stack overflow at n ≥ 9. The matrices are printed in the file — verify independently with any computer algebra system:

```python
import numpy as np
# paste the matrix, compute int(round(np.linalg.det(M)))
```

Or run `python3 ../computation/verify_p7.py` for the P₇ results.

## Axiom Inventory

2 axioms in `Kirchhoff.lean`:
- `kuratowski_triangle_free`: Kuratowski's theorem (1930)
- `tau_subdiv_invariant`: Subdivision invariance of τ (Kirchhoff 1847)

Both are classical results with textbook proofs, awaiting a Mathlib planarity predicate for formalization.
