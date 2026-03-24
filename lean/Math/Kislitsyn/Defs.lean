import Math.Kislitsyn.CombinatorialBasics

/-!
# FinPoset API Layer

Simp lemmas, helper lemmas, and API surface for `FinPoset`.
Following Mathlib convention: downstream proofs should never `unfold`
a definition — they use these API lemmas via `simp`, `rw`, or `exact`.

## Main results

- `FinPoset.linExts_mem`: membership in linExts ↔ IsLinExt (simp)
- `FinPoset.M_mem`: membership in M sets (simp)
- `FinPoset.Incomp_comm`: incomparability is symmetric (simp)
- `FinPoset.c_self`: c(a,a) = 0 (simp)
- `FinPoset.minority_comm`: minority is symmetric (simp)
- `FinPoset.swap_linext`: master swap lemma (replaces 3 case-explosion proofs)
-/

open scoped Classical
open Finset Equiv

namespace Kislitsyn

variable {n : ℕ}

-- ═════════════════════════════════════════════════════════════════
-- §A. MEMBERSHIP SIMP LEMMAS
-- These eliminate the repeated `simp only [linExts, mem_filter, ...]`
-- pattern that appears 35+ times across the codebase.
-- ═════════════════════════════════════════════════════════════════

@[simp]
lemma FinPoset.linExts_mem (P : FinPoset n) (σ : Perm (Fin n)) :
    σ ∈ P.linExts ↔ P.IsLinExt σ := by
  simp only [FinPoset.linExts, Finset.mem_filter, Finset.mem_univ, true_and]

@[simp]
lemma FinPoset.M_mem (P : FinPoset n) (σ : Perm (Fin n))
    (i : ℕ) (hi : i + 1 < n) (τ : Perm (Fin n)) :
    τ ∈ P.M σ i hi ↔
      τ ∈ P.linExts ∧
      (τ.symm (σ ⟨i + 1, hi⟩)).val < (τ.symm (σ ⟨i, by omega⟩)).val := by
  simp only [FinPoset.M, Finset.mem_filter]

-- ═════════════════════════════════════════════════════════════════
-- §B. INCOMPARABILITY SIMP LEMMAS
-- ═════════════════════════════════════════════════════════════════

@[simp]
lemma FinPoset.Incomp_self (P : FinPoset n) (a : Fin n) :
    P.Incomp a a ↔ False := by
  simp only [FinPoset.Incomp, not_and_self_iff]
  exact ⟨fun ⟨h, _⟩ => h (P.le_refl a), False.elim⟩

@[simp]
lemma FinPoset.Incomp_comm (P : FinPoset n) (a b : Fin n) :
    P.Incomp a b ↔ P.Incomp b a := by
  simp only [FinPoset.Incomp]; exact ⟨fun ⟨h1, h2⟩ => ⟨h2, h1⟩, fun ⟨h1, h2⟩ => ⟨h2, h1⟩⟩

/-- Symmetric version of Incomp for easy rewriting. -/
lemma FinPoset.Incomp.symm {P : FinPoset n} {a b : Fin n} (h : P.Incomp a b) :
    P.Incomp b a :=
  (P.Incomp_comm a b).mp h

-- ═════════════════════════════════════════════════════════════════
-- §C. COUNTING SIMP LEMMAS
-- ═════════════════════════════════════════════════════════════════

@[simp]
lemma FinPoset.c_self (P : FinPoset n) (a : Fin n) :
    P.c a a = 0 := by
  unfold FinPoset.c; simp [lt_irrefl]

/-- minority is symmetric: min(c, k-c) = min(k-c', c') via c+c'=k. -/
@[simp]
lemma FinPoset.minority_comm (P : FinPoset n) (x y : Fin n) (hne : x ≠ y) :
    P.minority x y = P.minority y x := by
  unfold FinPoset.minority
  have hcomp := c_complement P x y hne
  have hle := c_le_k P x y
  have hcomp' := c_complement P y x (Ne.symm hne)
  have hle' := c_le_k P y x
  -- c(x,y) + c(y,x) = k and c(y,x) + c(x,y) = k
  -- min(c(x,y), k - c(x,y)) = min(c(x,y), c(y,x))  [since k - c(x,y) = c(y,x)]
  -- = min(c(y,x), c(x,y)) = min(c(y,x), k - c(y,x))
  omega

-- ═════════════════════════════════════════════════════════════════
-- §D. BOTTLENECK HELPERS
-- ═════════════════════════════════════════════════════════════════

/-- Extract IsLinExt from M membership. -/
lemma FinPoset.M_linext {P : FinPoset n} {σ τ : Perm (Fin n)}
    {i : ℕ} {hi : i + 1 < n} (h : τ ∈ P.M σ i hi) :
    P.IsLinExt τ := by
  rw [M_mem] at h
  exact (linExts_mem P τ).mp h.1

/-- Extract the position reversal from M membership. -/
lemma FinPoset.M_pos_lt {P : FinPoset n} {σ τ : Perm (Fin n)}
    {i : ℕ} {hi : i + 1 < n} (h : τ ∈ P.M σ i hi) :
    (τ.symm (σ ⟨i + 1, hi⟩)).val < (τ.symm (σ ⟨i, by omega⟩)).val := by
  rw [M_mem] at h
  exact h.2

/-- Construct M membership from components. -/
lemma FinPoset.mem_M {P : FinPoset n} {σ τ : Perm (Fin n)}
    {i : ℕ} {hi : i + 1 < n}
    (hτ : P.IsLinExt τ)
    (hpos : (τ.symm (σ ⟨i + 1, hi⟩)).val < (τ.symm (σ ⟨i, by omega⟩)).val) :
    τ ∈ P.M σ i hi := by
  rw [M_mem]
  exact ⟨(linExts_mem P τ).mpr hτ, hpos⟩

-- ═════════════════════════════════════════════════════════════════
-- §E. SWAP POSITION HELPERS
-- These extract the common pattern from swap case analysis.
-- ═════════════════════════════════════════════════════════════════

/-- Position of element at swap index i under σ∘swap. -/
lemma swap_symm_at_left (σ : Perm (Fin n)) (i : ℕ) (hi : i + 1 < n) :
    (σ * Equiv.swap (⟨i, by omega⟩ : Fin n) ⟨i + 1, hi⟩).symm
      (σ ⟨i, by omega⟩) = ⟨i + 1, hi⟩ := by
  simp [Equiv.Perm.mul_def, Equiv.symm_trans_apply, Equiv.symm_swap,
        Equiv.symm_apply_apply, Equiv.swap_apply_left]

/-- Position of element at swap index i+1 under σ∘swap. -/
lemma swap_symm_at_right (σ : Perm (Fin n)) (i : ℕ) (hi : i + 1 < n) :
    (σ * Equiv.swap (⟨i, by omega⟩ : Fin n) ⟨i + 1, hi⟩).symm
      (σ ⟨i + 1, hi⟩) = ⟨i, by omega⟩ := by
  simp [Equiv.Perm.mul_def, Equiv.symm_trans_apply, Equiv.symm_swap,
        Equiv.symm_apply_apply, Equiv.swap_apply_right]

/-- Elements away from the swap indices are fixed. -/
lemma swap_symm_away (σ : Perm (Fin n)) (i : ℕ) (hi : i + 1 < n)
    (x : Fin n) (hx_ne_i : σ.symm x ≠ (⟨i, by omega⟩ : Fin n))
    (hx_ne_i1 : σ.symm x ≠ (⟨i + 1, hi⟩ : Fin n)) :
    (σ * Equiv.swap (⟨i, by omega⟩ : Fin n) ⟨i + 1, hi⟩).symm x = σ.symm x := by
  simp only [Equiv.Perm.mul_def, Equiv.symm_trans_apply, Equiv.symm_swap]
  exact Equiv.swap_apply_of_ne_of_ne hx_ne_i hx_ne_i1

-- ═════════════════════════════════════════════════════════════════
-- §F. MASTER SWAP LEMMA
-- CombinatorialBasics.bottleneck_swap_linext (57 lines, canonical proof)
-- CombinatorialBasics.disjoint_swap_valid (condensed from 141→45 lines
--   via Feature II-B: commutativity + double swap_linext)
-- This IsLinExt version is the downstream API for CollisionAttack etc.
-- ═════════════════════════════════════════════════════════════════

/-- **Master Swap Lemma.** Swapping adjacent incomparable elements in a
    linear extension preserves the linear extension property.

    The proof is a 9-case analysis on whether σ⁻¹(a) and σ⁻¹(b) hit the
    swap positions {i, i+1}. The only non-trivial case (σ⁻¹(a) = i,
    σ⁻¹(b) = i+1) gives a = σ(i), b = σ(i+1), contradicting incomparability
    since a ≤_P b. -/
lemma FinPoset.swap_linext (P : FinPoset n) (σ : Perm (Fin n))
    (hσ : P.IsLinExt σ) (i : ℕ) (hi : i + 1 < n)
    (hinc : P.Incomp (σ ⟨i, by omega⟩) (σ ⟨i + 1, hi⟩)) :
    P.IsLinExt (σ * Equiv.swap ⟨i, by omega⟩ ⟨i + 1, hi⟩) := by
  intro a b hab
  set sw := Equiv.swap (⟨i, by omega⟩ : Fin n) ⟨i + 1, hi⟩
  set pa := σ.symm a
  set pb := σ.symm b
  have h_ord : pa.val ≤ pb.val := hσ a b hab
  have hsw_inv : sw.symm = sw := Equiv.symm_swap _ _
  have hsymm : ∀ x, (σ * sw).symm x = sw (σ.symm x) := by
    intro x; simp [Equiv.Perm.mul_def, Equiv.symm_trans_apply, hsw_inv]
  rw [hsymm, hsymm]; change (sw pa).val ≤ (sw pb).val
  -- 9 cases on (pa, pb) ∈ {⟨i,_⟩, ⟨i+1,_⟩, other}²
  by_cases hpa_i : pa = ⟨i, by omega⟩
  · by_cases hpb_i1 : pb = ⟨i + 1, hi⟩
    · -- Critical case: a = σ(i), b = σ(i+1), but a ≤_P b contradicts Incomp
      exfalso
      have ha : a = σ ⟨i, by omega⟩ := by
        have := σ.apply_symm_apply a; rw [show σ.symm a = pa from rfl, hpa_i] at this; exact this.symm
      have hb : b = σ ⟨i + 1, hi⟩ := by
        have := σ.apply_symm_apply b; rw [show σ.symm b = pb from rfl, hpb_i1] at this; exact this.symm
      exact hinc.1 (ha ▸ hb ▸ hab)
    · by_cases hpb_i : pb = ⟨i, by omega⟩
      · rw [hpa_i, hpb_i]
      · rw [hpa_i, show sw ⟨i, by omega⟩ = ⟨i + 1, hi⟩ by simp [sw]]
        rw [Equiv.swap_apply_of_ne_of_ne hpb_i hpb_i1]
        have : pa.val = i := congr_arg Fin.val hpa_i
        have : pb.val ≠ i := fun h => hpb_i (Fin.ext h)
        have : pb.val ≠ i + 1 := fun h => hpb_i1 (Fin.ext h)
        simp only [Fin.val_mk]; omega
  · by_cases hpa_i1 : pa = ⟨i + 1, hi⟩
    · by_cases hpb_i : pb = ⟨i, by omega⟩
      · have : pa.val = i + 1 := congr_arg Fin.val hpa_i1
        have : pb.val = i := congr_arg Fin.val hpb_i; omega
      · by_cases hpb_i1 : pb = ⟨i + 1, hi⟩
        · rw [hpa_i1, hpb_i1]
        · rw [hpa_i1, show sw ⟨i + 1, hi⟩ = ⟨i, by omega⟩ by simp [sw]]
          rw [Equiv.swap_apply_of_ne_of_ne hpb_i hpb_i1]
          have : pa.val = i + 1 := congr_arg Fin.val hpa_i1
          simp only [Fin.val_mk]; omega
    · rw [Equiv.swap_apply_of_ne_of_ne hpa_i hpa_i1]
      by_cases hpb_i : pb = ⟨i, by omega⟩
      · rw [hpb_i, show sw ⟨i, by omega⟩ = ⟨i + 1, hi⟩ by simp [sw]]
        have : pb.val = i := congr_arg Fin.val hpb_i
        simp only [Fin.val_mk]; omega
      · by_cases hpb_i1 : pb = ⟨i + 1, hi⟩
        · rw [hpb_i1, show sw ⟨i + 1, hi⟩ = ⟨i, by omega⟩ by simp [sw]]
          have : pb.val = i + 1 := congr_arg Fin.val hpb_i1
          have : pa.val ≠ i := fun h => hpa_i (Fin.ext h)
          have : pa.val ≠ i + 1 := fun h => hpa_i1 (Fin.ext h)
          simp only [Fin.val_mk]; omega
        · rw [Equiv.swap_apply_of_ne_of_ne hpb_i hpb_i1]; exact h_ord

/-- Corollary: bottleneck swap gives a linext (uses IsBottleneck = Incomp). -/
lemma FinPoset.IsBottleneck.swap_linext' (P : FinPoset n) (σ : Perm (Fin n))
    (hσ : P.IsLinExt σ) (i : ℕ) (hi : i + 1 < n)
    (hbot : P.IsBottleneck σ i hi) :
    P.IsLinExt (σ * Equiv.swap ⟨i, by omega⟩ ⟨i + 1, hi⟩) :=
  P.swap_linext σ hσ i hi hbot

-- ═════════════════════════════════════════════════════════════════
-- §G. FIN DISJOINTNESS HELPERS
-- Replaces 30+ copies of `by simp [Fin.ext_iff]; omega`
-- ═════════════════════════════════════════════════════════════════

/-- Two Fin n values with different underlying nats are not equal. -/
lemma fin_ne_of_val_ne {a b : ℕ} (ha : a < n) (hb : b < n) (h : a ≠ b) :
    (⟨a, ha⟩ : Fin n) ≠ ⟨b, hb⟩ := by
  simp [Fin.ext_iff]; exact h

/-- Swap at disjoint indices fixes elements away from the swap. -/
lemma swap_fix_of_disjoint (i j : ℕ) (hi : i + 1 < n) (hj : j + 1 < n)
    (hdisj : i + 2 ≤ j ∨ j + 2 ≤ i) :
    Equiv.swap (⟨j, by omega⟩ : Fin n) ⟨j + 1, hj⟩ (⟨i, by omega⟩ : Fin n) = ⟨i, by omega⟩ ∧
    Equiv.swap (⟨j, by omega⟩ : Fin n) ⟨j + 1, hj⟩ (⟨i + 1, hi⟩ : Fin n) = ⟨i + 1, hi⟩ := by
  constructor <;> {
    simp only [Equiv.swap_apply_def, Fin.mk.injEq]
    split <;> [omega; split <;> [omega; rfl]]
  }

-- ═════════════════════════════════════════════════════════════════
-- §H. ALLSKEWED HELPER
-- Eliminates the repeated unfold FinPoset.minority + min case split
-- that appears 10+ times across the codebase.
-- ═════════════════════════════════════════════════════════════════

/-- AllSkewed gives a strict bound on c(x,y) from both sides. -/
lemma FinPoset.AllSkewed.c_bounds {P : FinPoset n} (hskew : P.AllSkewed)
    {x y : Fin n} (hxy : P.Incomp x y) :
    3 * P.c x y < P.k ∨ 3 * P.c x y > 2 * P.k := by
  have hsk := hskew x y hxy
  have hle := c_le_k P x y
  unfold FinPoset.minority at hsk
  by_cases h : P.c x y ≤ P.k - P.c x y
  · rw [min_eq_left h] at hsk; left; exact hsk
  · push_neg at h; rw [min_eq_right (le_of_lt h)] at hsk; right; omega

-- ═════════════════════════════════════════════════════════════════
-- §I. RANK-TO-PERMUTATION CONSTRUCTION
-- The same construction appears 3 times in CombinatorialBasics:
--   c_pos_of_incomp (Szpilrajn), dominant_of_transitive_tournament,
--   restrict_perm_surj. Each time: build rank, prove injective,
--   get bijective, extract permutation. This feature does it once.
-- ═════════════════════════════════════════════════════════════════

/-- **Rank Permutation.** Given a strict total order R on Fin n
    (irreflexive, transitive, total), construct the unique permutation σ
    such that σ.symm(x) = |{y : R y x}| (rank of x).

    The key insight: rank is injective because R is total (two elements
    with equal rank would violate totality), and injective on Fin n
    implies bijective. The permutation is the inverse of this bijection.

    This replaces ~240 lines of triplicated code. -/
noncomputable def rankPerm
    (R : Fin n → Fin n → Prop)
    (hirr : ∀ x, ¬R x x)
    (htrans : ∀ x y z, R x y → R y z → R x z)
    (htot : ∀ x y, x ≠ y → R x y ∨ R y x) :
    Perm (Fin n) :=
  let rk : Fin n → Fin n := fun x =>
    ⟨(Finset.univ.filter fun y => R y x).card, by
      calc (Finset.univ.filter fun y => R y x).card
          < Finset.univ.card := Finset.card_lt_card
            ⟨Finset.filter_subset _ _, fun h =>
              hirr x ((Finset.mem_filter.mp (h (Finset.mem_univ x))).2)⟩
        _ = n := by rw [Finset.card_univ, Fintype.card_fin]⟩
  have rk_mono : ∀ x y, R x y → (rk x).val < (rk y).val := by
    intro x y hxy
    show (Finset.univ.filter fun z => R z x).card <
         (Finset.univ.filter fun z => R z y).card
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_of_subset (fun z hz => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
      exact htrans z x y hz hxy)]
    exact ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ x, hxy⟩,
      fun h => hirr x (Finset.mem_filter.mp h).2⟩
  have rk_inj : Function.Injective rk := by
    intro x y hxy; by_contra hne
    have hxy' : (rk x).val = (rk y).val := by
      simp only [rk, Fin.mk.injEq] at hxy; exact hxy
    rcases htot x y hne with h | h
    · exact absurd hxy' (Nat.ne_of_lt (rk_mono x y h))
    · exact absurd hxy' (Nat.ne_of_gt (rk_mono y x h))
  (Equiv.ofBijective rk (Finite.injective_iff_bijective.mp rk_inj)).symm

/-- rankPerm.symm(x) = rank of x = |{y : R y x}|. -/
lemma rankPerm_symm_val (R : Fin n → Fin n → Prop)
    (hirr : ∀ x, ¬R x x) (htrans : ∀ x y z, R x y → R y z → R x z)
    (htot : ∀ x y, x ≠ y → R x y ∨ R y x) (x : Fin n) :
    ((rankPerm R hirr htrans htot).symm x).val =
      (Finset.univ.filter fun y => R y x).card := by
  rfl

/-- If R extends P.le (on distinct elements), the rank permutation is a linear extension. -/
lemma rankPerm_isLinExt (P : FinPoset n) (R : Fin n → Fin n → Prop)
    (hirr : ∀ x, ¬R x x) (htrans : ∀ x y z, R x y → R y z → R x z)
    (htot : ∀ x y, x ≠ y → R x y ∨ R y x)
    (hext : ∀ a b, P.le a b → a ≠ b → R a b) :
    P.IsLinExt (rankPerm R hirr htrans htot) := by
  intro a b hab
  by_cases heq : a = b
  · subst heq; exact le_refl _
  · exact le_of_lt (by
      show (Finset.univ.filter fun y => R y a).card <
           (Finset.univ.filter fun y => R y b).card
      apply Finset.card_lt_card
      rw [Finset.ssubset_iff_of_subset (fun z hz => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
        exact htrans z a b hz (hext a b hab heq))]
      exact ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ a, hext a b hab heq⟩,
        fun h => hirr a (Finset.mem_filter.mp h).2⟩)

/-- If R includes Incomp ∧ MajPrec, the rank permutation is dominant. -/
lemma rankPerm_dominant (P : FinPoset n) (R : Fin n → Fin n → Prop)
    (hirr : ∀ x, ¬R x x) (htrans : ∀ x y z, R x y → R y z → R x z)
    (htot : ∀ x y, x ≠ y → R x y ∨ R y x)
    (hext : ∀ a b, P.le a b → a ≠ b → R a b)
    (hmaj : ∀ a b, P.Incomp a b → P.MajPrec a b → R a b) :
    P.Dominant (rankPerm R hirr htrans htot) := by
  refine ⟨rankPerm_isLinExt P R hirr htrans htot hext, ?_⟩
  intro x y hxy hmaj_xy
  show (Finset.univ.filter fun z => R z x).card <
       (Finset.univ.filter fun z => R z y).card
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset (fun z hz => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
    exact htrans z x y hz (hmaj x y hxy hmaj_xy))]
  exact ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ x, hmaj x y hxy hmaj_xy⟩,
    fun h => hirr x (Finset.mem_filter.mp h).2⟩

-- ═════════════════════════════════════════════════════════════════
-- §J. CHAIN-ALL-UNIQUE
-- Every-element-chain → k ≤ 1. Used in allskewed_le7_false and
-- core_extraction (both currently inline the same argument).
-- ═════════════════════════════════════════════════════════════════

/-- **Chain Uniqueness.** If every element is a chain element (comparable
    to all others), then all linear extensions are identical, so k ≤ 1.

    Proof: chain_elem_position_unique gives σ₁.symm = σ₂.symm for all x.
    Taking σ.symm.symm recovers σ₁ = σ₂. Finset.card_le_one finishes. -/
lemma chain_all_k_le_one (P : FinPoset n) (h_all : ∀ x : Fin n, P.IsChainElem x) :
    P.k ≤ 1 := by
  unfold FinPoset.k FinPoset.linExts
  rw [Finset.card_le_one]
  intro σ₁ hσ₁ σ₂ hσ₂
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ₁ hσ₂
  have h_inv : σ₁.symm = σ₂.symm := by
    ext x; exact congr_arg Fin.val
      (chain_elem_position_unique P σ₁ σ₂ hσ₁ hσ₂ x (h_all x))
  rw [← Equiv.symm_symm σ₁, h_inv, Equiv.symm_symm]

/-- Nonchain from k ≥ 2: if k ≥ 2, there exists an incomparable pair.
    Contrapositive of chain_all_k_le_one. -/
lemma nonchain_of_k_ge_two (P : FinPoset n) (hk : P.k ≥ 2) : P.NonChain := by
  by_contra h_chain
  unfold FinPoset.NonChain at h_chain; push_neg at h_chain
  have h_all : ∀ x : Fin n, P.IsChainElem x := by
    intro x y
    by_cases hxy : x = y
    · left; exact hxy
    · have := h_chain x y; unfold FinPoset.Incomp at this; push_neg at this
      by_cases hle : P.le x y
      · right; left; exact hle
      · right; right; exact this hle
  have := chain_all_k_le_one P h_all; omega

-- ═════════════════════════════════════════════════════════════════
-- §K. DISJOINT SWAP COMPOSITION
-- If swap_i and swap_j are disjoint (|i−j| ≥ 2) and each preserves
-- linext, their composition does too. Uses commutation.
-- ═════════════════════════════════════════════════════════════════

/-- **Disjoint Swap Composition.** If σ*swap_i ∈ linExts and σ*swap_j ∈ linExts,
    and |i−j| ≥ 2 (so swap_i and swap_j are disjoint transpositions), then
    σ*swap_i*swap_j ∈ linExts.

    Key insight: disjoint transpositions commute (Equiv.Perm.Disjoint.commute),
    so σ*swap_i*swap_j = σ*swap_j*swap_i. Apply swap_linext twice:
    σ*swap_j is a linext (given), and at position i the elements are the
    same as in σ (since swap_j doesn't touch positions i, i+1). -/
lemma disjoint_swap_linext (P : FinPoset n) (σ : Perm (Fin n))
    (hσ : P.IsLinExt σ)
    (i j : ℕ) (hi : i + 1 < n) (hj : j + 1 < n)
    (hdisj : i + 2 ≤ j ∨ j + 2 ≤ i)
    (hboti : P.Incomp (σ ⟨i, by omega⟩) (σ ⟨i + 1, hi⟩))
    (hbotj : P.Incomp (σ ⟨j, by omega⟩) (σ ⟨j + 1, hj⟩)) :
    P.IsLinExt (σ * Equiv.swap ⟨i, by omega⟩ ⟨i + 1, hi⟩ *
                    Equiv.swap ⟨j, by omega⟩ ⟨j + 1, hj⟩) := by
  set si := Equiv.swap (⟨i, by omega⟩ : Fin n) ⟨i + 1, hi⟩
  set sj := Equiv.swap (⟨j, by omega⟩ : Fin n) ⟨j + 1, hj⟩
  -- Disjointness
  have h_disj : si.Disjoint sj := by
    intro x; simp only [si, sj, Equiv.swap_apply_def]
    split
    · right; split
      · exfalso; rename_i h1 h2; simp [Fin.ext_iff] at h1 h2; omega
      · split
        · exfalso; rename_i h1 _ h2; simp [Fin.ext_iff] at h1 h2; omega
        · rfl
    · split
      · right; split
        · exfalso; rename_i _ h1 h2; simp [Fin.ext_iff] at h1 h2; omega
        · split
          · exfalso; rename_i _ h1 _ h2; simp [Fin.ext_iff] at h1 h2; omega
          · rfl
      · left; rfl
  -- Commute: σ*si*sj = σ*sj*si
  have h_comm : si * sj = sj * si := h_disj.commute.eq
  rw [show σ * si * sj = σ * sj * si by rw [mul_assoc, mul_assoc, h_comm]]
  -- sj fixes positions i, i+1
  have hsj_fix_i : sj (⟨i, by omega⟩ : Fin n) = ⟨i, by omega⟩ := by
    simp only [sj, Equiv.swap_apply_def, Fin.mk.injEq]; split <;> [omega; split <;> [omega; rfl]]
  have hsj_fix_i1 : sj (⟨i + 1, hi⟩ : Fin n) = ⟨i + 1, hi⟩ := by
    simp only [sj, Equiv.swap_apply_def, Fin.mk.injEq]; split <;> [omega; split <;> [omega; rfl]]
  -- (σ*sj) at positions i, i+1 = σ at those positions
  have hσj_i : (σ * sj) ⟨i, by omega⟩ = σ ⟨i, by omega⟩ := by
    simp [Equiv.Perm.mul_apply, hsj_fix_i]
  have hσj_i1 : (σ * sj) ⟨i + 1, hi⟩ = σ ⟨i + 1, hi⟩ := by
    simp [Equiv.Perm.mul_apply, hsj_fix_i1]
  -- σ*sj is a linext (from swap_linext)
  have hσj : P.IsLinExt (σ * sj) := P.swap_linext σ hσ j hj hbotj
  -- Apply swap_linext again at position i (incomparability preserved)
  exact P.swap_linext (σ * sj) hσj i hi (by rw [hσj_i, hσj_i1]; exact hboti)

-- ═════════════════════════════════════════════════════════════════
-- §L. COVERAGE COUNTING FRAMEWORK
-- Bottleneck coverage + sum bound → contradiction.
-- Used in pigeonhole_two_bottlenecks and star_graph_shattered.
-- ═════════════════════════════════════════════════════════════════

/-- **Coverage Contradiction (|S| ≤ 2).** -/
lemma coverage_two_contradiction (k : ℕ) (hk4 : k ≥ 4)
    (h_cover : k - 1 ≤ 2 * ((k - 1) / 3)) : False := by
  have h_div : (k - 1) / 3 * 3 ≤ k - 1 := Nat.div_mul_le_self _ _
  omega

/-- **Coverage Contradiction (|S| = 3, overlap ≥ 1).** -/
lemma coverage_three_contradiction (k : ℕ) (hk4 : k ≥ 4)
    (h_cover : k - 1 ≤ 3 * ((k - 1) / 3) - 1) : False := by
  have h_div : (k - 1) / 3 * 3 ≤ k - 1 := Nat.div_mul_le_self _ _
  omega

-- ═════════════════════════════════════════════════════════════════
-- §M. ADJACENCY INVOLUTION (Feature V)
-- Discrete replacement for order polytope geometry.
-- Blueprint: docs/blueprint_feature_v.tex
-- ═════════════════════════════════════════════════════════════════

/-- **Adjacency predicate.** Elements a,b are adjacent in τ iff
    their positions differ by exactly 1. -/
def FinPoset.AdjPair (_P : FinPoset n) (τ : Perm (Fin n))
    (a b : Fin n) : Prop :=
  ((τ.symm a).val + 1 = (τ.symm b).val) ∨
  ((τ.symm b).val + 1 = (τ.symm a).val)

/-- **Adjacent-majority set.** Linear extensions where a,b are adjacent
    and a appears before b (majority = true) or after (majority = false). -/
noncomputable def FinPoset.adjSet (P : FinPoset n)
    (a b : Fin n) (majority : Bool) : Finset (Perm (Fin n)) :=
  P.linExts.filter fun τ ↦
    P.AdjPair τ a b ∧
    if majority then (τ.symm a).val < (τ.symm b).val
    else (τ.symm b).val < (τ.symm a).val

/-- **Non-adjacent set.** Linear extensions where a,b are NOT adjacent,
    split by direction. -/
noncomputable def FinPoset.nonadjSet (P : FinPoset n)
    (a b : Fin n) (majority : Bool) : Finset (Perm (Fin n)) :=
  P.linExts.filter fun τ ↦
    ¬P.AdjPair τ a b ∧
    if majority then (τ.symm a).val < (τ.symm b).val
    else (τ.symm b).val < (τ.symm a).val

/-- **Non-adjacent extensions (undirected).** All linexts where a,b are
    not adjacent, regardless of which comes first. This is the set that
    carries ALL skewness. -/
noncomputable def FinPoset.nonadjExts (P : FinPoset n)
    (a b : Fin n) : Finset (Perm (Fin n)) :=
  P.linExts.filter fun τ ↦ ¬P.AdjPair τ a b

-- ─────────────────────────────────────────────────────────────────
-- §M.1 DIRECTIVE 1: Skewness Budget
-- AllSkewed at (a,b) forces |adj(a,b)| < 2k/3, equivalently
-- |nonadj(a,b)| > k/3.
-- ─────────────────────────────────────────────────────────────────

/-- **Skewness Budget Lemma.** If AllSkewed and a ∥ b, then the adjacent
    linexts for (a,b) contribute zero net skewness (by involution),
    so all skewness comes from non-adjacent linexts.

    Specifically: c(a,b) − minority(a,b) = |N⁺| − |N⁻|.

    We state this as a cardinality decomposition:
    c(a,b) = |adjSet a b true| + |nonadjSet a b true|. -/
lemma FinPoset.c_eq_adj_plus_nonadj (P : FinPoset n) (a b : Fin n)
    (_hab : P.Incomp a b) :
    P.c a b = (P.adjSet a b true).card + (P.nonadjSet a b true).card := by
  unfold FinPoset.c FinPoset.adjSet FinPoset.nonadjSet
  -- Both filters partition linExts.filter (σ.symm a < σ.symm b)
  have : (P.linExts.filter fun σ ↦ (σ.symm a).val < (σ.symm b).val)
    = (P.linExts.filter fun τ ↦ P.AdjPair τ a b ∧ (τ.symm a).val < (τ.symm b).val)
    ∪ (P.linExts.filter fun τ ↦ ¬P.AdjPair τ a b ∧ (τ.symm a).val < (τ.symm b).val) := by
    ext τ
    simp only [Finset.mem_filter, Finset.mem_union]
    constructor
    · intro ⟨hmem, hlt⟩
      by_cases hadj : P.AdjPair τ a b
      · left; exact ⟨hmem, hadj, hlt⟩
      · right; exact ⟨hmem, hadj, hlt⟩
    · intro h
      rcases h with ⟨hmem, _, hlt⟩ | ⟨hmem, _, hlt⟩ <;> exact ⟨hmem, hlt⟩
  rw [this]
  apply Finset.card_union_of_disjoint
  simp only [Finset.disjoint_filter]
  intro τ _ ⟨hadj, _⟩ ⟨hnadj, _⟩
  exact hnadj hadj

/-- **Minority decomposition.** minority(a,b) = |adjSet false| + |nonadjSet false|. -/
lemma FinPoset.minority_le_adj_plus_nonadj (P : FinPoset n) (a b : Fin n)
    (_hab : P.Incomp a b) (_hne : a ≠ b) :
    P.c b a = (P.adjSet a b false).card + (P.nonadjSet a b false).card := by
  unfold FinPoset.c FinPoset.adjSet FinPoset.nonadjSet
  have : (P.linExts.filter fun σ ↦ (σ.symm b).val < (σ.symm a).val)
    = (P.linExts.filter fun τ ↦ P.AdjPair τ a b ∧ (τ.symm b).val < (τ.symm a).val)
    ∪ (P.linExts.filter fun τ ↦ ¬P.AdjPair τ a b ∧ (τ.symm b).val < (τ.symm a).val) := by
    ext τ
    simp only [Finset.mem_filter, Finset.mem_union]
    constructor
    · intro ⟨hmem, hlt⟩
      by_cases hadj : P.AdjPair τ a b
      · left; exact ⟨hmem, hadj, hlt⟩
      · right; exact ⟨hmem, hadj, hlt⟩
    · intro h
      rcases h with ⟨hmem, _, hlt⟩ | ⟨hmem, _, hlt⟩ <;> exact ⟨hmem, hlt⟩
  rw [this]
  apply Finset.card_union_of_disjoint
  simp only [Finset.disjoint_filter]
  intro τ _ ⟨hadj, _⟩ ⟨hnadj, _⟩
  exact hnadj hadj

/-- **Adjacency involution cardinality.**
    |A⁺(a,b)| = |A⁻(a,b)| for any incomparable pair.
    Proof: the map τ ↦ τ·swap(τ⁻¹(a), τ⁻¹(b)) is an involution A⁺ → A⁻.
    This is the element-centric generalization of bottleneck_swap_linext. -/
lemma FinPoset.adj_involution_card (P : FinPoset n) (a b : Fin n)
    (hab : P.Incomp a b) :
    (P.adjSet a b true).card = (P.adjSet a b false).card := by
  -- The involution S_{a,b}(τ) = τ·swap(τ⁻¹(a), τ⁻¹(b))
  -- maps A⁺ ↔ A⁻ bijectively.
  set sw : Perm (Fin n) → Perm (Fin n) :=
    fun τ => Equiv.swap (τ.symm a) (τ.symm b)
  set f := fun τ : Perm (Fin n) => τ * sw τ
  -- (f τ).symm = sw(τ) ∘ τ.symm since swap is self-inverse
  -- Following the pattern from swap_linext (line 168)
  have hf_symm : ∀ τ y, (f τ).symm y = sw τ (τ.symm y) := by
    intro τ y
    have hsw_inv : (sw τ).symm = sw τ := Equiv.symm_swap _ _
    simp [f, Equiv.Perm.mul_def, Equiv.symm_trans_apply, hsw_inv]
  have hf_symm_a : ∀ τ, (f τ).symm a = τ.symm b := by
    intro τ; rw [hf_symm]; simp [sw, Equiv.swap_apply_left]
  have hf_symm_b : ∀ τ, (f τ).symm b = τ.symm a := by
    intro τ; rw [hf_symm]; simp [sw, Equiv.swap_apply_right]
  have hf_invol : ∀ τ, f (f τ) = τ := by
    intro τ
    -- sw(f τ) = swap((f τ).symm a, (f τ).symm b) = swap(τ.symm b, τ.symm a)
    have hsw_ft : sw (f τ) = Equiv.swap (τ.symm b) (τ.symm a) := by
      simp only [sw, hf_symm_a, hf_symm_b]
    -- f(f τ) = (τ * sw τ) * sw(f τ) = τ * sw τ * swap(τ.symm b, τ.symm a)
    -- = τ * (swap(a,b) * swap(b,a)) = τ * 1 = τ
    calc f (f τ) = f τ * sw (f τ) := rfl
      _ = (τ * sw τ) * Equiv.swap (τ.symm b) (τ.symm a) := by rw [hsw_ft]
      _ = τ * (sw τ * Equiv.swap (τ.symm b) (τ.symm a)) := by rw [mul_assoc]
      _ = τ * (Equiv.swap (τ.symm a) (τ.symm b) * Equiv.swap (τ.symm b) (τ.symm a)) := rfl
      _ = τ * 1 := by rw [Equiv.swap_comm (τ.symm a) (τ.symm b), Equiv.swap_mul_self]
      _ = τ := mul_one τ
  -- f sends adjSet true → adjSet false
  -- Core: for τ ∈ A⁺, AdjPair gives positions j, j+1 where a,b sit.
  -- Swapping at (j, j+1) preserves linext (swap_linext), reverses direction.
  have hf_linext : ∀ τ, τ ∈ P.linExts → P.AdjPair τ a b →
      (τ.symm a).val < (τ.symm b).val → P.IsLinExt (f τ) := by
    intro τ hτ hadj hlt
    rw [FinPoset.linExts_mem] at hτ
    -- AdjPair + a before b → τ.symm(a) + 1 = τ.symm(b)
    unfold FinPoset.AdjPair at hadj
    have hadj_ab : (τ.symm a).val + 1 = (τ.symm b).val := by
      rcases hadj with h | h; exact h; omega
    have hi : (τ.symm a).val + 1 < n := by
      have := (τ.symm b).isLt; omega
    have hσi : τ ⟨(τ.symm a).val, (τ.symm a).isLt⟩ = a := by
      have : ⟨(τ.symm a).val, (τ.symm a).isLt⟩ = τ.symm a := Fin.eta _ _
      rw [this, τ.apply_symm_apply]
    have hσi1 : τ ⟨(τ.symm a).val + 1, hi⟩ = b := by
      have heq : (⟨(τ.symm a).val + 1, hi⟩ : Fin n) = τ.symm b := Fin.ext (by omega)
      rw [heq]; exact τ.apply_symm_apply b
    -- sw τ = swap at positions (j, j+1) where j = (τ.symm a).val
    have ha_eq : τ.symm a = ⟨(τ.symm a).val, by omega⟩ := (Fin.eta _ _).symm
    have hb_eq : τ.symm b = ⟨(τ.symm a).val + 1, hi⟩ := Fin.ext hadj_ab.symm
    rw [show f τ = τ * sw τ from rfl, show sw τ = Equiv.swap (τ.symm a) (τ.symm b) from rfl,
        ha_eq, hb_eq]
    apply P.swap_linext τ hτ _ hi
    rw [hσi, hσi1]; exact hab
  have hf_linext' : ∀ τ, τ ∈ P.linExts → P.AdjPair τ a b →
      (τ.symm b).val < (τ.symm a).val → P.IsLinExt (f τ) := by
    intro τ hτ hadj hlt
    rw [FinPoset.linExts_mem] at hτ
    unfold FinPoset.AdjPair at hadj
    have hadj_ba : (τ.symm b).val + 1 = (τ.symm a).val := by
      rcases hadj with h | h; omega; exact h
    have hi : (τ.symm b).val + 1 < n := by
      have := (τ.symm a).isLt; omega
    have hσi : τ ⟨(τ.symm b).val, (τ.symm b).isLt⟩ = b := by
      have : ⟨(τ.symm b).val, (τ.symm b).isLt⟩ = τ.symm b := Fin.eta _ _
      rw [this, τ.apply_symm_apply]
    have hσi1 : τ ⟨(τ.symm b).val + 1, hi⟩ = a := by
      have heq : (⟨(τ.symm b).val + 1, hi⟩ : Fin n) = τ.symm a := Fin.ext (by omega)
      rw [heq]; exact τ.apply_symm_apply a
    -- swap(τ.symm a, τ.symm b) = swap(⟨b.val+1, hi⟩, ⟨b.val, _⟩) = swap(⟨b.val, _⟩, ⟨b.val+1, hi⟩) (by comm)
    have hswap_eq : Equiv.swap (τ.symm a) (τ.symm b) =
        Equiv.swap ⟨(τ.symm b).val, by omega⟩ ⟨(τ.symm b).val + 1, hi⟩ := by
      rw [Equiv.swap_comm]; congr 1; exact Fin.ext hadj_ba.symm
    rw [show f τ = τ * sw τ from rfl, show sw τ = Equiv.swap (τ.symm a) (τ.symm b) from rfl,
        hswap_eq]
    apply P.swap_linext τ hτ _ hi
    rw [hσi, hσi1]; exact hab.symm
  -- f maps adjSet true → adjSet false
  have hf_mem : ∀ τ, τ ∈ P.adjSet a b true → f τ ∈ P.adjSet a b false := by
    intro τ hτ
    simp only [FinPoset.adjSet, Finset.mem_filter, ite_true] at hτ ⊢
    obtain ⟨hle, hadj, hlt⟩ := hτ
    refine ⟨(FinPoset.linExts_mem _ _).mpr (hf_linext τ hle hadj hlt), ?_, ?_⟩
    · -- AdjPair (f τ) a b
      unfold FinPoset.AdjPair; rw [hf_symm_a, hf_symm_b]
      unfold FinPoset.AdjPair at hadj
      rcases hadj with h | h
      · right; exact h
      · exfalso; omega
    · -- direction reversed
      change ((f τ).symm b).val < ((f τ).symm a).val
      rw [hf_symm_a, hf_symm_b]; exact hlt
  -- f maps adjSet false → adjSet true
  have hf_mem' : ∀ τ, τ ∈ P.adjSet a b false → f τ ∈ P.adjSet a b true := by
    intro τ hτ
    simp only [FinPoset.adjSet, Finset.mem_filter, ite_true] at hτ ⊢
    -- hτ has if false then ... — reduce it
    simp only [Bool.false_eq_true, ↓reduceIte] at hτ ⊢
    obtain ⟨hle, hadj, hlt⟩ := hτ
    refine ⟨(FinPoset.linExts_mem _ _).mpr (hf_linext' τ hle hadj hlt), ?_, ?_⟩
    · unfold FinPoset.AdjPair; rw [hf_symm_a, hf_symm_b]
      unfold FinPoset.AdjPair at hadj
      rcases hadj with h | h
      · exfalso; omega
      · left; exact h
    · change ((f τ).symm a).val < ((f τ).symm b).val
      rw [hf_symm_a, hf_symm_b]; exact hlt
  -- Cardinality equality via antisymmetry on |image| ≤ |target|
  have hf_inj : ∀ τ₁ τ₂, f τ₁ = f τ₂ → τ₁ = τ₂ := by
    intro τ₁ τ₂ h
    have := congr_arg f h; rwa [hf_invol, hf_invol] at this
  apply Nat.le_antisymm
  · calc (P.adjSet a b true).card
        = (Finset.image f (P.adjSet a b true)).card :=
          (Finset.card_image_of_injective _ (fun _ _ h => hf_inj _ _ h)).symm
      _ ≤ (P.adjSet a b false).card :=
          Finset.card_le_card (fun τ hτ => by
            obtain ⟨σ, hσ, rfl⟩ := Finset.mem_image.mp hτ
            exact hf_mem σ hσ)
  · calc (P.adjSet a b false).card
        = (Finset.image f (P.adjSet a b false)).card :=
          (Finset.card_image_of_injective _ (fun _ _ h => hf_inj _ _ h)).symm
      _ ≤ (P.adjSet a b true).card :=
          Finset.card_le_card (fun τ hτ => by
            obtain ⟨σ, hσ, rfl⟩ := Finset.mem_image.mp hτ
            exact hf_mem' σ hσ)

/-- **Skewness source.** All net skewness comes from non-adjacent linexts. -/
lemma FinPoset.skewness_eq_nonadj_diff (P : FinPoset n) (a b : Fin n)
    (hab : P.Incomp a b) (hne : a ≠ b) :
    P.c a b - P.c b a =
    (P.nonadjSet a b true).card - (P.nonadjSet a b false).card := by
  have hc := P.c_eq_adj_plus_nonadj a b hab
  have hm := P.minority_le_adj_plus_nonadj a b hab hne
  have hinv := P.adj_involution_card a b hab
  omega

-- ─────────────────────────────────────────────────────────────────
-- §M.2 DIRECTIVE 2: Buffer Element Predicate
-- A buffer element for (a,b) in τ is any x sitting strictly between
-- a and b in τ's ordering. Non-adjacency ↔ buffer existence.
-- ─────────────────────────────────────────────────────────────────

/-- **Buffer element.** x is a buffer for (a,b) in τ if x sits strictly
    between a and b in τ's position ordering. -/
def FinPoset.HasBuffer (_P : FinPoset n) (τ : Perm (Fin n))
    (a b x : Fin n) : Prop :=
  (((τ.symm a).val < (τ.symm x).val ∧ (τ.symm x).val < (τ.symm b).val) ∨
   ((τ.symm b).val < (τ.symm x).val ∧ (τ.symm x).val < (τ.symm a).val)) ∧
  x ≠ a ∧ x ≠ b

/-- **Buffer existence set.** The set of elements serving as buffers for
    (a,b) in τ. -/
noncomputable def FinPoset.bufferSet (P : FinPoset n) (τ : Perm (Fin n))
    (a b : Fin n) : Finset (Fin n) :=
  Finset.univ.filter fun x ↦ P.HasBuffer τ a b x

/-- **Buffer–Adjacency equivalence.** a,b are non-adjacent in τ iff there
    exists a buffer element between them.

    Key idea: positions are naturals, τ is a bijection on Fin n, so
    |pos(a) − pos(b)| > 1 iff some element occupies an intermediate position. -/
lemma FinPoset.nonadj_iff_has_buffer (P : FinPoset n) (τ : Perm (Fin n))
    (a b : Fin n) (_hτ : P.IsLinExt τ) (hne : a ≠ b) :
    ¬P.AdjPair τ a b ↔ ∃ x, P.HasBuffer τ a b x := by
  constructor
  · -- (→) ¬Adj → ∃ buffer
    intro hnadj
    unfold FinPoset.AdjPair at hnadj; push_neg at hnadj
    -- positions pa = τ.symm(a), pb = τ.symm(b) satisfy |pa − pb| ≥ 2
    set pa := (τ.symm a).val
    set pb := (τ.symm b).val
    have hpa_ne_pb : pa ≠ pb := by
      intro heq
      have := τ.symm.injective (Fin.ext heq)
      exact hne this
    -- There exists a natural number strictly between pa and pb
    have ⟨hnadj1, hnadj2⟩ := hnadj
    -- pa + 1 ≠ pb and pb + 1 ≠ pa, combined with pa ≠ pb
    -- gives |pa − pb| ≥ 2, so ∃ m with min < m < max
    by_cases hlt : pa < pb
    · -- pa < pb, and pa + 1 ≠ pb, so pa + 1 < pb
      have h_gap : pa + 1 < pb := by omega
      -- position pa + 1 is occupied by some element
      have h_pos_bound : pa + 1 < n := by
        have := (τ.symm b).isLt; omega
      use τ ⟨pa + 1, h_pos_bound⟩
      unfold FinPoset.HasBuffer
      constructor
      · left
        constructor
        · show (τ.symm a).val < (τ.symm (τ ⟨pa + 1, h_pos_bound⟩)).val
          simp [Equiv.symm_apply_apply]; omega
        · show (τ.symm (τ ⟨pa + 1, h_pos_bound⟩)).val < (τ.symm b).val
          simp [Equiv.symm_apply_apply]; omega
      · constructor
        · -- τ(pa+1) ≠ a because positions differ
          intro heq
          have := congr_arg (fun x => (τ.symm x).val) heq
          simp [Equiv.symm_apply_apply] at this; omega
        · -- τ(pa+1) ≠ b because positions differ
          intro heq
          have := congr_arg (fun x => (τ.symm x).val) heq
          simp [Equiv.symm_apply_apply] at this; omega
    · -- pb < pa (symmetric case)
      have hlt' : pb < pa := by omega
      have h_gap : pb + 1 < pa := by omega
      have h_pos_bound : pb + 1 < n := by
        have := (τ.symm a).isLt; omega
      use τ ⟨pb + 1, h_pos_bound⟩
      unfold FinPoset.HasBuffer
      constructor
      · right
        constructor
        · show (τ.symm b).val < (τ.symm (τ ⟨pb + 1, h_pos_bound⟩)).val
          simp; omega
        · show (τ.symm (τ ⟨pb + 1, h_pos_bound⟩)).val < (τ.symm a).val
          simp; omega
      · constructor
        · intro heq
          have := congr_arg (fun x => (τ.symm x).val) heq
          simp [Equiv.symm_apply_apply] at this; omega
        · intro heq
          have := congr_arg (fun x => (τ.symm x).val) heq
          simp [Equiv.symm_apply_apply] at this; omega
  · -- (←) ∃ buffer → ¬Adj
    intro ⟨x, hbuf⟩
    unfold FinPoset.HasBuffer at hbuf
    unfold FinPoset.AdjPair; push_neg
    obtain ⟨hpos, _, _⟩ := hbuf
    rcases hpos with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> constructor <;> omega

/-- **Buffer set nonempty for non-adjacent pairs.** -/
lemma FinPoset.bufferSet_nonempty (P : FinPoset n) (τ : Perm (Fin n))
    (a b : Fin n) (hτ : P.IsLinExt τ) (hne : a ≠ b)
    (hnadj : ¬P.AdjPair τ a b) :
    (P.bufferSet τ a b).Nonempty := by
  rw [P.nonadj_iff_has_buffer τ a b hτ hne] at hnadj
  obtain ⟨x, hx⟩ := hnadj
  exact ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ x, hx⟩⟩

-- ─────────────────────────────────────────────────────────────────
-- §M.3 DIRECTIVE 3: Multi-Pair Buffer Pigeonhole
-- With s ≥ 4 bottleneck pairs, AllSkewed forces ≥ k/3 non-adjacent
-- linexts per pair. Each non-adjacent linext consumes buffer slots.
-- ─────────────────────────────────────────────────────────────────

/-- **nonadjExts partition.** nonadjExts = nonadjSet true ∪ nonadjSet false (disjoint). -/
lemma FinPoset.nonadjExts_eq (P : FinPoset n) (a b : Fin n)
    (hne : a ≠ b) :
    (P.nonadjExts a b).card =
    (P.nonadjSet a b true).card + (P.nonadjSet a b false).card := by
  unfold FinPoset.nonadjExts FinPoset.nonadjSet
  have hne_pos : ∀ (τ : Perm (Fin n)), (τ.symm a).val ≠ (τ.symm b).val :=
    fun τ h ↦ hne (τ.symm.injective (Fin.ext h))
  have : (P.linExts.filter fun τ ↦ ¬P.AdjPair τ a b)
    = (P.linExts.filter fun τ ↦ ¬P.AdjPair τ a b ∧ (τ.symm a).val < (τ.symm b).val)
    ∪ (P.linExts.filter fun τ ↦ ¬P.AdjPair τ a b ∧ (τ.symm b).val < (τ.symm a).val) := by
    ext τ
    simp only [Finset.mem_filter, Finset.mem_union]
    constructor
    · intro ⟨hmem, hnadj⟩
      by_cases hlt : (τ.symm a).val < (τ.symm b).val
      · left; exact ⟨hmem, hnadj, hlt⟩
      · right; exact ⟨hmem, hnadj, by have := hne_pos τ; omega⟩
    · intro h
      rcases h with ⟨hmem, hnadj, _⟩ | ⟨hmem, hnadj, _⟩ <;> exact ⟨hmem, hnadj⟩
  rw [this]
  apply Finset.card_union_of_disjoint
  simp only [Finset.disjoint_filter]
  intro τ _ ⟨_, hlt1⟩ ⟨_, hlt2⟩; omega

/-- **Linext partition.** k = |adjSet true| + |adjSet false| + |nonadjExts|. -/
-- Helper: partition a filter into adj ∪ nonadj
private lemma filter_adj_nonadj_partition (P : FinPoset n) (a b : Fin n)
    (pred : Perm (Fin n) → Prop) [DecidablePred pred] :
    (P.linExts.filter fun τ ↦ pred τ) =
    (P.linExts.filter fun τ ↦ P.AdjPair τ a b ∧ pred τ) ∪
    (P.linExts.filter fun τ ↦ ¬P.AdjPair τ a b ∧ pred τ) := by
  ext τ
  simp only [Finset.mem_filter, Finset.mem_union]
  constructor
  · intro ⟨hmem, hp⟩
    by_cases hadj : P.AdjPair τ a b
    · left; exact ⟨hmem, hadj, hp⟩
    · right; exact ⟨hmem, hadj, hp⟩
  · intro h
    rcases h with ⟨hmem, _, hp⟩ | ⟨hmem, _, hp⟩ <;> exact ⟨hmem, hp⟩

private lemma card_filter_adj_nonadj (P : FinPoset n) (a b : Fin n)
    (pred : Perm (Fin n) → Prop) [DecidablePred pred] :
    (P.linExts.filter fun τ ↦ pred τ).card =
    (P.linExts.filter fun τ ↦ P.AdjPair τ a b ∧ pred τ).card +
    (P.linExts.filter fun τ ↦ ¬P.AdjPair τ a b ∧ pred τ).card := by
  rw [filter_adj_nonadj_partition P a b pred]
  apply Finset.card_union_of_disjoint
  simp only [Finset.disjoint_filter]
  intro τ _ ⟨hadj, _⟩ ⟨hnadj, _⟩; exact hnadj hadj

/-- **Linext partition.** k = |adjSet true| + |adjSet false| + |nonadjExts|. -/
lemma FinPoset.k_eq_adj_plus_nonadj (P : FinPoset n) (a b : Fin n)
    (hne : a ≠ b) :
    P.k = (P.adjSet a b true).card + (P.adjSet a b false).card +
          (P.nonadjExts a b).card := by
  have hcomp := c_complement P a b hne
  have hca : P.c a b = (P.adjSet a b true).card + (P.nonadjSet a b true).card := by
    unfold FinPoset.c FinPoset.adjSet FinPoset.nonadjSet
    exact card_filter_adj_nonadj P a b _
  have hcb : P.c b a = (P.adjSet a b false).card + (P.nonadjSet a b false).card := by
    unfold FinPoset.c FinPoset.adjSet FinPoset.nonadjSet
    exact card_filter_adj_nonadj P a b _
  have hnonadj := P.nonadjExts_eq a b hne
  omega

lemma FinPoset.nonadj_card_gt_of_allskewed (P : FinPoset n) (a b : Fin n)
    (hab : P.Incomp a b) (hskew : P.AllSkewed) :
    3 * (P.nonadjExts a b).card > P.k := by
  have hne : a ≠ b := by
    intro heq; subst heq; exact hab.1 (P.le_refl a)
  have hinv := P.adj_involution_card a b hab
  -- minority(a,b) = |adjSet false| + |nonadjSet false|
  -- But we can use: minority = min(c(a,b), c(b,a)) and
  -- k = 2*A + N where A = |adjSet true| = |adjSet false|, N = |nonadjExts|
  -- AllSkewed: 3 * minority < k
  -- Since minority ≤ c(b,a) = A + nonadjSet_false ≤ A + N
  -- and minority ≥ ... we need: A < N
  -- From 3*min(c,k-c) < k and c+c' = k and c = A+N⁺, c' = A+N⁻:
  -- 3*min(A+N⁺, A+N⁻) < 2A + N⁺ + N⁻
  -- min(A+N⁺, A+N⁻) = A + min(N⁺, N⁻)
  -- so 3A + 3*min(N⁺,N⁻) < 2A + N⁺+N⁻
  -- i.e. A + 3*min(N⁺,N⁻) < N⁺+N⁻ = N
  -- Since min(N⁺,N⁻) ≥ 0: A < N, i.e. A ≤ N-1
  -- k = 2A + N ≤ 2(N-1) + N = 3N - 2 < 3N
  have hsk := hskew a b hab
  -- We need the partition: k = 2A + nonadjExts
  have hk_part := P.k_eq_adj_plus_nonadj a b hne
  rw [hinv] at hk_part
  -- hk_part : k = 2 * adjSet_false + nonadjExts
  -- hsk : 3 * minority(a,b) < k
  -- We need: 3 * nonadjExts > k, i.e. 3N > 2A + N, i.e. 2N > 2A, i.e. N > A
  -- From AllSkewed: 3 * min(c, k-c) < k
  -- c(a,b) = A + nonadjSet_true, c(b,a) = A + nonadjSet_false (by minority_le_adj_plus_nonadj)
  -- min(c, k-c) = min(c, c') where c+c' = k
  -- Let's just use omega with enough facts
  unfold FinPoset.minority at hsk
  have hc := c_le_k P a b
  have hc' := c_le_k P b a
  have hcomp := c_complement P a b hne
  -- nonadjExts.card = k - 2 * adjSet_false (from partition)
  -- c(a,b) ≥ adjSet_true = adjSet_false (since c = adj_true + nonadj_true)
  -- c(b,a) ≥ adjSet_false
  -- min(c,c') ≥ adjSet_false
  -- 3 * adjSet_false ≤ 3 * min(c,c') < k = 2*adjSet_false + nonadjExts
  -- so adjSet_false < nonadjExts
  -- k = 2*adjSet_false + nonadjExts < 3*nonadjExts ✓
  -- But we need to connect min to adjSet...
  -- Let A = (P.adjSet a b false).card, N = (P.nonadjExts a b).card
  set A := (P.adjSet a b false).card
  set N := (P.nonadjExts a b).card
  -- hk_part : k = A + A + N = 2*A + N
  -- From c_eq_adj_plus_nonadj: c(a,b) = A + nonadjSet_true ≥ A
  -- From minority_le_adj_plus_nonadj: c(b,a) = A + nonadjSet_false ≥ A
  -- So min(c, k - c) = min(c, c') ≥ A (since both ≥ A)
  -- Wait, min(x,y) ≥ A when both x,y ≥ A.
  have hca := P.c_eq_adj_plus_nonadj a b hab
  have hcb := P.minority_le_adj_plus_nonadj a b hab hne
  -- hca: c(a,b) = A + nonadjSet_true ≥ A
  -- hcb: c(b,a) = A + nonadjSet_false ≥ A
  rw [hinv] at hca -- c(a,b) = A + nonadjSet_true
  -- min(c(a,b), k - c(a,b)) ≥ A
  -- k - c(a,b) = c(b,a) by complement
  -- so min(c, c') ≥ min(A + _, A + _) ≥ A
  have hmin_ge : min (P.c a b) (P.k - P.c a b) ≥ A := by
    rw [show P.k - P.c a b = P.c b a by omega]
    rw [ge_iff_le, Nat.le_min]
    exact ⟨by omega, by omega⟩
  -- 3 * A ≤ 3 * min(...) < k = 2A + N
  have h3A : 3 * A < 2 * A + N := by omega
  -- so A < N, i.e. A + 1 ≤ N
  -- k = 2A + N ≤ 2(N-1) + N = 3N - 2 < 3N
  omega

/-- **Union bound on simultaneous non-adjacency.** For s bottleneck pairs,
    if each has > k/3 non-adjacent linexts, the sum of non-adjacent counts
    exceeds s·k/3. This is the first step toward the packing contradiction.

    Note: this is a pure counting lemma, not the full contradiction.
    The full contradiction requires the structural buffer packing argument
    (Step 3 of blueprint Theorem 3.5). -/
lemma nonadj_sum_bound (k s : ℕ) (hs : s > 0) (counts : Fin s → ℕ)
    (h_each : ∀ i, 3 * counts i > k)
    (_h_sum_le : (∑ i, counts i) ≤ s * k) :
    -- The sum of non-adjacency counts exceeds s·k/3
    3 * (∑ i, counts i) > s * k := by
  have : Nonempty (Fin s) := ⟨⟨0, hs⟩⟩
  calc 3 * (∑ i, counts i)
      = ∑ i, 3 * counts i := by rw [Finset.mul_sum]
    _ > ∑ _i : Fin s, k := by
        apply Finset.sum_lt_sum_of_nonempty
        · exact Finset.univ_nonempty
        · exact fun i _ => h_each i
    _ = s * k := by simp [Finset.sum_const]

/-- **4-pair pigeonhole.** With s ≥ 4 bottleneck pairs, AllSkewed forces
    each pair to contribute > k/3 non-adjacent linexts. But adjacent linexts
    cancel (involution), so the total non-adjacent budget is ≤ s·k.
    The overcounting forces at least one pair to violate the skewness bound
    when buffer packing constraints are applied.

    This lemma states the counting prerequisite. The structural buffer
    argument (which elements can serve as buffers for which pairs) is
    the remaining piece needed for `volume_exhaustion_absurd`. -/
lemma four_pair_nonadj_overcount (k : ℕ) (_hk : k ≥ 4)
    (counts : Fin 4 → ℕ)
    (h_each : ∀ i, 3 * counts i > k)
    (h_bound : ∀ i, counts i ≤ k) :
    -- Total non-adjacent events exceed 4k/3
    (∑ i, counts i) > 4 * k / 3 := by
  -- Each count > k/3, so sum > 4·k/3
  have h4 : 3 * (∑ i, counts i) > 4 * k :=
    nonadj_sum_bound k 4 (by omega) counts h_each (by
      calc (∑ i, counts i) ≤ ∑ _i : Fin 4, k := by
            apply Finset.sum_le_sum; intro i _; exact h_bound i
        _ = 4 * k := by simp [Finset.sum_const])
  omega

-- ═════════════════════════════════════════════════════════════════
-- §K. KURATOWSKI CASCADE — DEFINITIONS
-- ═════════════════════════════════════════════════════════════════

/-- Every element is active (incomparable to at least one other element). -/
def FinPoset.AllActive (P : FinPoset n) : Prop :=
  ∀ x : Fin n, P.IsActiveElem x

/-- The set of balanced incomparable pairs (a,b) with a < b (by index).
    This is the "balance graph" B(P) from the Kuratowski Cascade. -/
noncomputable def FinPoset.balancedPairSet (P : FinPoset n) : Finset (Fin n × Fin n) :=
  Finset.univ.filter fun ⟨a, b⟩ ↦ a < b ∧ P.Incomp a b ∧ P.Balanced a b

/-- B(P) = |balanced pairs| -/
noncomputable def FinPoset.balancedPairCount (P : FinPoset n) : ℕ :=
  P.balancedPairSet.card

/-- AllSkewed ↔ balancedPairCount = 0. -/
lemma allskewed_iff_no_balanced (P : FinPoset n) :
    P.AllSkewed ↔ (∀ a b : Fin n, P.Incomp a b → ¬P.Balanced a b) := by
  constructor
  · intro hsk a b hab hbal
    unfold FinPoset.Balanced at hbal
    have := hsk a b hab
    omega
  · intro h a b hab
    by_contra hge; push_neg at hge
    exact h a b hab hge

end Kislitsyn
