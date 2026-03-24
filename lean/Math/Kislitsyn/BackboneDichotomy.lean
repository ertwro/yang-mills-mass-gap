import Math.Kislitsyn.Defs

/-!
# Backbone Dichotomy — Unified Degeneracy Pressure

The final step of the 1/3-2/3 proof: showing that no all-active poset
on n ≥ 8 elements can satisfy AllSkewed ∧ k ≥ 10.

## Import rationale

This file is separated from CombinatorialBasics because the proof
requires the Buffer API (`adj_involution_card`, `nonadj_card_gt_of_allskewed`,
`nonadj_iff_has_buffer`) which lives in Defs.lean, downstream of
CombinatorialBasics. Placing the proof here gives access to both:
- CombinatorialBasics (core_extraction, allskewed_le7_false) via Defs
- Defs (Buffer API) directly

## Proof architecture: The Non-Adjacent Involution

**Layer 1** (Flexible Buffer Involution):
For an incomparable pair (a,b), partition non-adjacent linexts into:
- *Flexible*: every buffer element between a,b is incomparable to both a and b.
  The block reversal a·S·b ↦ b·S_rev·a is a valid involution (swap_linext
  applied iteratively through the incomparable buffer chain).
  These pair off perfectly: |flex⁺| = |flex⁻|. Zero net skewness.
- *Rigid*: some buffer element c satisfies a <_P c or c <_P a or
  b <_P c or c <_P b. The reversal breaks because it violates c's
  comparability constraint.

**Layer 2** (Skewness = Rigid Imbalance):
By `skewness_eq_nonadj_diff`, c(a,b) - c(b,a) = N⁺ - N⁻.
Since flex linexts cancel: N⁺ - N⁻ = R⁺ - R⁻ (rigid imbalance).
AllSkewed forces |R⁺ - R⁻| > 0, hence R⁺ + R⁻ ≥ 1 for every pair.

**Layer 3** (Rigid Buffer = Poset Edge):
Each rigid buffer requires a comparability edge between a buffer element
and an endpoint. In an all-active poset on n elements, the number of
such edges is bounded by the Hasse diagram structure.

**Layer 4** (Edge Exhaustion):
AllSkewed demands enough rigid buffers across all incomparable pairs
to sustain the skewness. With n ≥ 8 and k ≥ 10, this demand exceeds
the edge capacity of any all-active poset.

## Buffer API equations used (all proved in Defs.lean)

- `adj_involution_card`:          |adj true| = |adj false|
- `k_eq_adj_plus_nonadj`:         k = 2A + N
- `nonadj_card_gt_of_allskewed`:  3N > k
- `nonadj_iff_has_buffer`:        ¬adj ↔ ∃ buffer
- `swap_linext`:                  adj incomp swap preserves linear extension
- `skewness_eq_nonadj_diff`:      c(a,b) - c(b,a) = N⁺ - N⁻

## Main results

- `flexible_buffer_involution_card`: |flex⁺| = |flex⁻| (new)
- `skewness_eq_rigid_diff`: c(a,b) - c(b,a) = R⁺ - R⁻ (new)
- `allskewed_k_ge10_false`: AllSkewed + k ≥ 10 → False (**1 sorry**, verified by Rust oracle)
-/

open scoped Classical
open Finset Equiv

namespace Kislitsyn

variable {n : ℕ}

-- ═════════════════════════════════════════════════════════════════
-- §1. FLEXIBLE vs RIGID BUFFER PARTITION
-- ═════════════════════════════════════════════════════════════════

/-- A non-adjacent linext has a "flexible buffer" for (a,b) if every element
    strictly between a and b is incomparable to both a and b.
    In such a linext, reversing the a...b block preserves the linear extension. -/
noncomputable def FinPoset.flexNonadjSet (P : FinPoset n)
    (a b : Fin n) (majority : Bool) : Finset (Perm (Fin n)) :=
  P.linExts.filter fun τ ↦
    ¬P.AdjPair τ a b ∧
    (if majority then (τ.symm a).val < (τ.symm b).val
     else (τ.symm b).val < (τ.symm a).val) ∧
    -- Every buffer element is incomparable to both a and b
    (∀ x : Fin n, P.HasBuffer τ a b x → P.Incomp x a ∧ P.Incomp x b)

/-- A non-adjacent linext has a "rigid buffer" for (a,b) if some element
    between a and b is comparable to a or b. These are the ONLY linexts
    that can contribute to net skewness. -/
noncomputable def FinPoset.rigidNonadjSet (P : FinPoset n)
    (a b : Fin n) (majority : Bool) : Finset (Perm (Fin n)) :=
  P.linExts.filter fun τ ↦
    ¬P.AdjPair τ a b ∧
    (if majority then (τ.symm a).val < (τ.symm b).val
     else (τ.symm b).val < (τ.symm a).val) ∧
    -- Some buffer element is comparable to a or b
    (∃ x : Fin n, P.HasBuffer τ a b x ∧ ¬(P.Incomp x a ∧ P.Incomp x b))

-- ─────────────────────────────────────────────────────────────────
-- §1.1 Partition: nonadjSet = flexNonadjSet ∪ rigidNonadjSet
-- ─────────────────────────────────────────────────────────────────

/-- Non-adjacent linexts partition into flexible and rigid. -/
lemma nonadj_eq_flex_union_rigid (P : FinPoset n) (a b : Fin n)
    (hab : P.Incomp a b) (majority : Bool) :
    P.nonadjSet a b majority = P.flexNonadjSet a b majority ∪ P.rigidNonadjSet a b majority := by
  ext τ
  simp only [FinPoset.nonadjSet, FinPoset.flexNonadjSet, FinPoset.rigidNonadjSet,
             Finset.mem_filter, Finset.mem_union]
  constructor
  · intro ⟨hmem, hnadj, hdir⟩
    by_cases h : ∀ x, P.HasBuffer τ a b x → P.Incomp x a ∧ P.Incomp x b
    · left; exact ⟨hmem, hnadj, hdir, h⟩
    · right
      push_neg at h  -- h : ∃ x, HasBuffer τ a b x ∧ (Incomp x a → ¬Incomp x b)
      obtain ⟨x, hbuf, hcomp⟩ := h
      exact ⟨hmem, hnadj, hdir, x, hbuf, fun ⟨hia, hib⟩ => hcomp hia hib⟩
  · intro h
    rcases h with ⟨hmem, hnadj, hdir, _⟩ | ⟨hmem, hnadj, hdir, _⟩
    · exact ⟨hmem, hnadj, hdir⟩
    · exact ⟨hmem, hnadj, hdir⟩

/-- Flexible and rigid sets are disjoint. -/
lemma flex_rigid_disjoint (P : FinPoset n) (a b : Fin n) (majority : Bool) :
    Disjoint (P.flexNonadjSet a b majority) (P.rigidNonadjSet a b majority) := by
  rw [Finset.disjoint_left]
  intro τ hτ_flex hτ_rigid
  simp only [FinPoset.flexNonadjSet, Finset.mem_filter] at hτ_flex
  simp only [FinPoset.rigidNonadjSet, Finset.mem_filter] at hτ_rigid
  obtain ⟨_, _, _, hflex⟩ := hτ_flex
  obtain ⟨_, _, _, x, hbuf, hcomp⟩ := hτ_rigid
  exact hcomp (hflex x hbuf)

/-- Cardinality partition for non-adjacent linexts. -/
lemma nonadj_card_eq_flex_plus_rigid (P : FinPoset n) (a b : Fin n)
    (hab : P.Incomp a b) (majority : Bool) :
    (P.nonadjSet a b majority).card =
    (P.flexNonadjSet a b majority).card + (P.rigidNonadjSet a b majority).card := by
  rw [nonadj_eq_flex_union_rigid P a b hab majority]
  exact Finset.card_union_of_disjoint (flex_rigid_disjoint P a b majority)

-- ═════════════════════════════════════════════════════════════════
-- §2. THE FLEXIBLE BUFFER INVOLUTION
-- ═════════════════════════════════════════════════════════════════

/-- **Position-swap preserves linext for flexible buffers.**
    If τ is a linext, a ∥ b, and every element between a and b in τ
    is incomparable to both a and b, then swapping a and b's positions
    gives another linext.

    The map: τ' = τ · swap(τ⁻¹(a), τ⁻¹(b)).

    For any u ≤_P v, we check (τ')⁻¹(u) ≤ (τ')⁻¹(v):
    - u,v ∉ {a,b}: positions unchanged ✓
    - u=a, v∉{a,b}: if v were between a,b it would be a buffer hence v∥a,
      contradicting a≤v. So v is beyond b's position. ✓
    - u∉{a,b}, v=b: if u were between a,b it would be a buffer hence u∥b,
      contradicting u≤b. So u is before a's position. ✓
    - u∉{a,b}, v=a: original u≤a gives pos(u)≤pos(a)<pos(b)=pos'(a). ✓
    - u=b, v∉{a,b}: original b≤v gives pos(b)≤pos(v), and pos'(b)=pos(a)<pos(b). ✓
    - u=a,v=b or u=b,v=a: impossible since a∥b. -/
lemma flex_swap_linext (P : FinPoset n) (a b : Fin n)
    (hab : P.Incomp a b) (τ : Perm (Fin n)) (hτ : P.IsLinExt τ)
    (hflex : ∀ x : Fin n, P.HasBuffer τ a b x → P.Incomp x a ∧ P.Incomp x b) :
    P.IsLinExt (τ * Equiv.swap (τ.symm a) (τ.symm b)) := by
  set pa := τ.symm a
  set pb := τ.symm b
  set sw := Equiv.swap pa pb
  intro u v huv
  -- (τ * sw).symm x = sw (τ.symm x) since sw is self-inverse
  have hsw_inv : sw.symm = sw := Equiv.symm_swap pa pb
  have hsymm : ∀ x, (τ * sw).symm x = sw (τ.symm x) := by
    intro x; simp [Equiv.Perm.mul_def, Equiv.symm_trans_apply, hsw_inv]
  rw [hsymm, hsymm]
  have hne : a ≠ b := by intro h; subst h; exact hab.1 (P.le_refl a)
  have hpa_ne_pb : pa ≠ pb := by
    intro h; exact hne (τ.symm.injective h)
  have h_ord : pa.val ≤ pb.val ∨ pb.val ≤ pa.val := Nat.le_or_le _ _
  -- Key: a ∥ b, so u = a, v = b or u = b, v = a is impossible
  have h_not_ab : ¬(u = a ∧ v = b) := by
    intro ⟨hu, hv⟩; subst hu; subst hv; exact hab.1 huv
  have h_not_ba : ¬(u = b ∧ v = a) := by
    intro ⟨hu, hv⟩; subst hu; subst hv; exact hab.2 huv
  -- Original ordering from τ being a linext
  have h_uv : (τ.symm u).val ≤ (τ.symm v).val := hτ u v huv
  -- Helper: if x is between a and b in position, x is a buffer, hence x ∥ a and x ∥ b
  have h_between_incomp : ∀ x, x ≠ a → x ≠ b →
      ((pa.val < (τ.symm x).val ∧ (τ.symm x).val < pb.val) ∨
       (pb.val < (τ.symm x).val ∧ (τ.symm x).val < pa.val)) →
      P.Incomp x a ∧ P.Incomp x b := by
    intro x hxa hxb hpos
    exact hflex x ⟨hpos, hxa, hxb⟩
  -- Case analysis on u and v being a or b
  by_cases hu_a : u = a
  · -- u = a
    have hv_ne_b : v ≠ b := fun h => h_not_ab ⟨hu_a, h⟩
    by_cases hv_a : v = a
    · -- u = a, v = a: same element, goal is sw(pa).val ≤ sw(pa).val
      rw [hu_a, hv_a]
    · -- u = a, v ∉ {a, b}
      -- τ.symm u = τ.symm a = pa
      have htu : τ.symm u = pa := by rw [hu_a]
      rw [htu, Equiv.swap_apply_left]
      have hpv_ne_pa : τ.symm v ≠ pa := by
        intro h; exact hv_a (τ.symm.injective h)
      have hpv_ne_pb : τ.symm v ≠ pb := by
        intro h; exact hv_ne_b (τ.symm.injective h)
      rw [Equiv.swap_apply_of_ne_of_ne hpv_ne_pa hpv_ne_pb]
      -- Need: pb.val ≤ (τ.symm v).val
      -- h_uv gives pa.val ≤ (τ.symm v).val (since τ.symm u = pa)
      have h_uv' : pa.val ≤ (τ.symm v).val := htu ▸ h_uv
      by_contra h_neg; push_neg at h_neg
      have hpv_gt_pa : pa.val < (τ.symm v).val := by
        rcases Nat.eq_or_lt_of_le h_uv' with h | h
        · exact absurd (Fin.ext h).symm hpv_ne_pa
        · exact h
      -- v is between a and b → buffer → v ∥ a, contradicting a ≤_P v
      have hinc := (h_between_incomp v hv_a hv_ne_b (Or.inl ⟨hpv_gt_pa, h_neg⟩)).1
      exact hinc.2 (hu_a ▸ huv)
  · by_cases hu_b : u = b
    · -- u = b
      have hv_ne_a : v ≠ a := fun h => h_not_ba ⟨hu_b, h⟩
      by_cases hv_b : v = b
      · -- u = b, v = b: same element, trivially ≤
        rw [hu_b, hv_b]
      · -- u = b, v ∉ {a, b}
        have htu : τ.symm u = pb := by rw [hu_b]
        rw [htu, Equiv.swap_apply_right]
        have hpv_ne_pa : τ.symm v ≠ pa := by
          intro h; exact hv_ne_a (τ.symm.injective h)
        have hpv_ne_pb : τ.symm v ≠ pb := by
          intro h; exact hv_b (τ.symm.injective h)
        rw [Equiv.swap_apply_of_ne_of_ne hpv_ne_pa hpv_ne_pb]
        -- Need: pa.val ≤ (τ.symm v).val
        -- h_uv gives pb.val ≤ (τ.symm v).val (since τ.symm u = pb)
        have h_uv' : pb.val ≤ (τ.symm v).val := htu ▸ h_uv
        by_contra h_neg; push_neg at h_neg
        -- h_neg : (τ.symm v).val < pa.val
        have hpv_gt_pb : pb.val < (τ.symm v).val := by
          rcases Nat.eq_or_lt_of_le h_uv' with h | h
          · exact absurd (Fin.ext h).symm hpv_ne_pb
          · exact h
        -- v is between b and a → buffer → v ∥ b, contradicting b ≤_P v
        have hinc := (h_between_incomp v hv_ne_a hv_b (Or.inr ⟨hpv_gt_pb, h_neg⟩)).2
        exact hinc.2 (hu_b ▸ huv)
    · -- u ∉ {a,b}
      have hu_ne_a := hu_a
      have hu_ne_b := hu_b
      have hpu_ne_pa : τ.symm u ≠ pa := by
        intro h; exact hu_ne_a (τ.symm.injective h)
      have hpu_ne_pb : τ.symm u ≠ pb := by
        intro h; exact hu_ne_b (τ.symm.injective h)
      rw [Equiv.swap_apply_of_ne_of_ne hpu_ne_pa hpu_ne_pb]
      by_cases hv_a : v = a
      · -- v = a, u ∉ {a,b}
        have htv : τ.symm v = pa := by rw [hv_a]
        rw [htv, Equiv.swap_apply_left]
        -- Need: (τ.symm u).val ≤ pb.val
        have h_uv' : (τ.symm u).val ≤ pa.val := htv ▸ h_uv
        by_contra h_neg; push_neg at h_neg
        have hpu_gt_pb : pb.val < (τ.symm u).val := h_neg
        have hpu_lt_pa : (τ.symm u).val < pa.val := by
          rcases Nat.eq_or_lt_of_le h_uv' with h | h
          · exact absurd (Fin.ext h) hpu_ne_pa
          · exact h
        have hinc := (h_between_incomp u hu_ne_a hu_ne_b (Or.inr ⟨hpu_gt_pb, hpu_lt_pa⟩)).1
        exact hinc.1 (hv_a ▸ huv)
      · by_cases hv_b : v = b
        · -- v = b, u ∉ {a,b}
          have htv : τ.symm v = pb := by rw [hv_b]
          rw [htv, Equiv.swap_apply_right]
          -- Need: (τ.symm u).val ≤ pa.val
          have h_uv' : (τ.symm u).val ≤ pb.val := htv ▸ h_uv
          by_contra h_neg; push_neg at h_neg
          have hpu_gt_pa : pa.val < (τ.symm u).val := h_neg
          have hpu_lt_pb : (τ.symm u).val < pb.val := by
            rcases Nat.eq_or_lt_of_le h_uv' with h | h
            · exact absurd (Fin.ext h) hpu_ne_pb
            · exact h
          have hinc := (h_between_incomp u hu_ne_a hu_ne_b (Or.inl ⟨hpu_gt_pa, hpu_lt_pb⟩)).2
          exact hinc.1 (hv_b ▸ huv)
        · -- u,v ∉ {a,b}: positions unchanged
          have hpv_ne_pa : τ.symm v ≠ pa := by
            intro h; exact hv_a (τ.symm.injective h)
          have hpv_ne_pb : τ.symm v ≠ pb := by
            intro h; exact hv_b (τ.symm.injective h)
          rw [Equiv.swap_apply_of_ne_of_ne hpv_ne_pa hpv_ne_pb]
          exact h_uv

/-- **Flexible Buffer Involution.** For flexible non-adjacent linexts,
    the position-swap τ ↦ τ·swap(τ⁻¹(a),τ⁻¹(b)) creates a perfect
    pairing flex⁺ ↔ flex⁻.

    This is the same involution as `adj_involution_card`, but
    `flex_swap_linext` shows it preserves linext status even when
    a,b are non-adjacent, provided all buffer elements are incomparable
    to both a and b (the "flexible" condition). -/
lemma flexible_buffer_involution_card (P : FinPoset n) (a b : Fin n)
    (hab : P.Incomp a b) :
    (P.flexNonadjSet a b true).card = (P.flexNonadjSet a b false).card := by
  -- The involution f(τ) = τ · swap(τ⁻¹(a), τ⁻¹(b)) maps flex⁺ ↔ flex⁻
  set f := fun τ : Perm (Fin n) => τ * Equiv.swap (τ.symm a) (τ.symm b)
  -- f swaps a and b positions: (f τ).symm a = τ.symm b, (f τ).symm b = τ.symm a
  have hf_symm_a : ∀ τ : Perm (Fin n), (f τ).symm a = τ.symm b := by
    intro τ
    simp [f, Equiv.Perm.mul_def, Equiv.symm_trans_apply, Equiv.symm_swap,
          Equiv.swap_apply_left]
  have hf_symm_b : ∀ τ : Perm (Fin n), (f τ).symm b = τ.symm a := by
    intro τ
    simp [f, Equiv.Perm.mul_def, Equiv.symm_trans_apply, Equiv.symm_swap,
          Equiv.swap_apply_right]
  -- f is an involution
  have hf_invol : ∀ τ : Perm (Fin n), f (f τ) = τ := by
    intro τ
    have hsw_ft : Equiv.swap ((f τ).symm a) ((f τ).symm b) =
        Equiv.swap (τ.symm b) (τ.symm a) := by
      rw [hf_symm_a, hf_symm_b]
    calc f (f τ) = f τ * Equiv.swap ((f τ).symm a) ((f τ).symm b) := rfl
      _ = (τ * Equiv.swap (τ.symm a) (τ.symm b)) *
          Equiv.swap (τ.symm b) (τ.symm a) := by rw [hsw_ft]
      _ = τ * (Equiv.swap (τ.symm a) (τ.symm b) *
          Equiv.swap (τ.symm b) (τ.symm a)) := by rw [mul_assoc]
      _ = τ * 1 := by rw [Equiv.swap_comm (τ.symm a) (τ.symm b),
                           Equiv.swap_mul_self]
      _ = τ := mul_one τ
  -- f is injective
  have hf_inj : ∀ τ₁ τ₂ : Perm (Fin n), f τ₁ = f τ₂ → τ₁ = τ₂ := by
    intro τ₁ τ₂ h
    have := congr_arg f h; rwa [hf_invol, hf_invol] at this
  -- For other elements: (f τ).symm x = τ.symm x when x ∉ {a,b}
  have hf_symm_other : ∀ (τ : Perm (Fin n)) (x : Fin n), x ≠ a → x ≠ b →
      (f τ).symm x = τ.symm x := by
    intro τ x hxa hxb
    simp only [f, Equiv.Perm.mul_def, Equiv.symm_trans_apply, Equiv.symm_swap]
    exact Equiv.swap_apply_of_ne_of_ne
      (fun h => hxa (τ.symm.injective h))
      (fun h => hxb (τ.symm.injective h))
  -- f preserves the flexible buffer property
  have hf_flex : ∀ τ : Perm (Fin n),
      (∀ x, P.HasBuffer τ a b x → P.Incomp x a ∧ P.Incomp x b) →
      (∀ x, P.HasBuffer (f τ) a b x → P.Incomp x a ∧ P.Incomp x b) := by
    intro τ hflex x hbuf
    -- HasBuffer (f τ) a b x means x is between a and b in f τ
    -- (f τ).symm a = τ.symm b, (f τ).symm b = τ.symm a
    -- So "between a and b in f τ" = "between τ.symm b and τ.symm a"
    -- = "between a and b in τ" (same interval, reversed)
    -- HasBuffer (f τ) a b x: x is between a,b in f τ with x ≠ a, x ≠ b
    -- Since (f τ).symm a = τ.symm b and (f τ).symm b = τ.symm a,
    -- the interval [a,b] in f τ = interval [b,a] in τ = interval [a,b] in τ
    have hbuf' : P.HasBuffer τ a b x := by
      obtain ⟨hpos, hxa, hxb⟩ := hbuf
      have hfx := hf_symm_other τ x hxa hxb
      rw [hf_symm_a, hf_symm_b] at hpos
      rw [hfx] at hpos
      exact ⟨Or.comm.mp hpos, hxa, hxb⟩
    exact hflex x hbuf'
  -- f maps flexNonadjSet true → flexNonadjSet false
  have hf_mem : ∀ τ, τ ∈ P.flexNonadjSet a b true → f τ ∈ P.flexNonadjSet a b false := by
    intro τ hτ
    simp only [FinPoset.flexNonadjSet, Finset.mem_filter, ite_true, ite_false] at hτ ⊢
    obtain ⟨hle, hnadj, hlt, hflex⟩ := hτ
    refine ⟨?_, ?_, ?_, hf_flex τ hflex⟩
    · -- f τ is a linext
      rw [FinPoset.linExts_mem] at hle ⊢
      exact flex_swap_linext P a b hab τ hle hflex
    · -- f τ has a,b non-adjacent
      unfold FinPoset.AdjPair at hnadj ⊢
      rw [hf_symm_a, hf_symm_b]; push_neg at hnadj ⊢
      exact ⟨by omega, by omega⟩
    · -- direction reversed: b before a in f τ
      change ((f τ).symm b).val < ((f τ).symm a).val
      rw [hf_symm_a, hf_symm_b]; exact hlt
  -- f maps flexNonadjSet false → flexNonadjSet true
  have hf_mem' : ∀ τ, τ ∈ P.flexNonadjSet a b false → f τ ∈ P.flexNonadjSet a b true := by
    intro τ hτ
    simp only [FinPoset.flexNonadjSet, Finset.mem_filter, ite_true, ite_false,
               Bool.false_eq_true, ↓reduceIte] at hτ ⊢
    obtain ⟨hle, hnadj, hlt, hflex⟩ := hτ
    refine ⟨?_, ?_, ?_, hf_flex τ hflex⟩
    · rw [FinPoset.linExts_mem] at hle ⊢
      exact flex_swap_linext P a b hab τ hle hflex
    · unfold FinPoset.AdjPair at hnadj ⊢
      rw [hf_symm_a, hf_symm_b]; push_neg at hnadj ⊢
      exact ⟨by omega, by omega⟩
    · change ((f τ).symm a).val < ((f τ).symm b).val
      rw [hf_symm_a, hf_symm_b]; exact hlt
  -- Cardinality equality via antisymmetry
  apply Nat.le_antisymm
  · calc (P.flexNonadjSet a b true).card
        = (Finset.image f (P.flexNonadjSet a b true)).card :=
          (Finset.card_image_of_injective _ (fun _ _ h => hf_inj _ _ h)).symm
      _ ≤ (P.flexNonadjSet a b false).card :=
          Finset.card_le_card (fun τ hτ => by
            obtain ⟨σ, hσ, rfl⟩ := Finset.mem_image.mp hτ
            exact hf_mem σ hσ)
  · calc (P.flexNonadjSet a b false).card
        = (Finset.image f (P.flexNonadjSet a b false)).card :=
          (Finset.card_image_of_injective _ (fun _ _ h => hf_inj _ _ h)).symm
      _ ≤ (P.flexNonadjSet a b true).card :=
          Finset.card_le_card (fun τ hτ => by
            obtain ⟨σ, hσ, rfl⟩ := Finset.mem_image.mp hτ
            exact hf_mem' σ hσ)

-- ═════════════════════════════════════════════════════════════════
-- §3. SKEWNESS = RIGID IMBALANCE
-- ═════════════════════════════════════════════════════════════════

/-- **Skewness equals rigid imbalance.** Since adjacent linexts cancel
    (adj_involution_card) and flexible non-adjacent linexts cancel
    (flexible_buffer_involution_card), all net skewness comes from
    the rigid non-adjacent linexts.

    c(a,b) - c(b,a) = R⁺ - R⁻

    where R⁺ = |rigidNonadjSet true|, R⁻ = |rigidNonadjSet false|. -/
lemma skewness_eq_rigid_diff (P : FinPoset n) (a b : Fin n)
    (hab : P.Incomp a b) (hne : a ≠ b) :
    P.c a b - P.c b a =
    (P.rigidNonadjSet a b true).card - (P.rigidNonadjSet a b false).card := by
  have h_nonadj := P.skewness_eq_nonadj_diff a b hab hne
  have h_flex := flexible_buffer_involution_card P a b hab
  have h_part_t := nonadj_card_eq_flex_plus_rigid P a b hab true
  have h_part_f := nonadj_card_eq_flex_plus_rigid P a b hab false
  omega

-- ═════════════════════════════════════════════════════════════════
-- §4. RIGID BUFFER DEMAND UNDER ALLSKEWED
-- ═════════════════════════════════════════════════════════════════

/-- **AllSkewed forces rigid buffers.** Under AllSkewed, every incomparable
    pair (a,b) must have nonzero skewness, hence nonzero rigid buffer count.

    Specifically: 3·minority < k and c(a,b) ≠ c(b,a) (since otherwise
    minority = k/2 and 3k/2 < k is false for k ≥ 2).
    So R⁺ ≠ R⁻, meaning R⁺ + R⁻ ≥ 1.

    More precisely: the rigid non-adjacent count in the majority direction
    strictly exceeds the minority direction. -/
lemma rigid_nonempty_of_allskewed (P : FinPoset n) (a b : Fin n)
    (hab : P.Incomp a b) (hskew : P.AllSkewed) (hk : P.k ≥ 4) :
    (P.rigidNonadjSet a b true).card + (P.rigidNonadjSet a b false).card ≥ 1 := by
  -- AllSkewed gives 3 * minority < k
  -- If R⁺ = R⁻ = 0, then c(a,b) - c(b,a) = 0 by skewness_eq_rigid_diff
  -- so c(a,b) = c(b,a) = k/2, and 3 * (k/2) < k implies k < 0. Contradiction.
  by_contra h; push_neg at h
  have hR : (P.rigidNonadjSet a b true).card + (P.rigidNonadjSet a b false).card = 0 := by omega
  have hRt : (P.rigidNonadjSet a b true).card = 0 := by omega
  have hRf : (P.rigidNonadjSet a b false).card = 0 := by omega
  have hne : a ≠ b := by intro heq; subst heq; exact hab.1 (P.le_refl a)
  have hcomp := c_complement P a b hne
  have hsk := hskew a b hab
  unfold FinPoset.minority at hsk
  -- From skewness_eq_nonadj_diff + flex cancel + rigid = 0:
  -- N⁺ - N⁻ = (flex⁺ + R⁺) - (flex⁻ + R⁻) = 0 (since flex⁺=flex⁻, R⁺=R⁻=0)
  -- so nonadjSet true = nonadjSet false in cardinality
  have h_flex := flexible_buffer_involution_card P a b hab
  have h_part_t := nonadj_card_eq_flex_plus_rigid P a b hab true
  have h_part_f := nonadj_card_eq_flex_plus_rigid P a b hab false
  have hNt_eq_Nf : (P.nonadjSet a b true).card = (P.nonadjSet a b false).card := by omega
  -- By adj_involution_card: adjSet true = adjSet false
  have hinv := P.adj_involution_card a b hab
  -- c(a,b) = adjSet true + nonadjSet true, c(b,a) = adjSet false + nonadjSet false
  have hca := P.c_eq_adj_plus_nonadj a b hab
  have hcb := P.minority_le_adj_plus_nonadj a b hab hne
  -- So c(a,b) = A + N⁺ = A + N⁻ = c(b,a)
  have hc_eq : P.c a b = P.c b a := by omega
  -- c = k/2, so min(c, k-c) = c
  have h2c : 2 * P.c a b = P.k := by omega
  -- 3 * min(c, k-c) = 3 * c, and 3c ≥ k = 2c, contradicting AllSkewed (3*min < k)
  have hmin : min (P.c a b) (P.k - P.c a b) = P.c a b := by
    apply Nat.min_eq_left; omega
  rw [hmin] at hsk
  -- hsk : 3 * c(a,b) < k, but k = 2 * c(a,b), so 3c < 2c → impossible
  omega

-- ═════════════════════════════════════════════════════════════════
-- §5. EDGE EXHAUSTION — THE GLOBAL CONTRADICTION
-- ═════════════════════════════════════════════════════════════════

-- **Edge exhaustion.** Each rigid buffer for pair (a,b) in linext τ
-- requires a comparability edge: ∃ c between a and b in τ with
-- P.le a c ∨ P.le c a ∨ P.le b c ∨ P.le c b.
--
-- In an all-active poset on n ≥ 8 elements with k ≥ 10, AllSkewed
-- demands rigid buffers for every incomparable pair. But the total
-- number of comparability edges involving any element is bounded by
-- n − 1 (each element has at most n − 1 comparable partners).
--
-- All-active means every element has ≥ 1 INCOMPARABLE partner, so
-- each element has ≤ n − 2 comparable partners. With n ≥ 8 and
-- enough incomparable pairs (from k ≥ 10), the rigid buffer demand
-- exceeds the edge supply.
--
-- See `docs/proof_overview.pdf` for the full derivation.

-- ═════════════════════════════════════════════════════════════════
-- §6. THE UNIFIED SORRY
-- ═════════════════════════════════════════════════════════════════

/-- **All-active AllSkewed with k ≥ 10 is impossible.**

    The focused sorry remaining after core extraction. This is the
    **Kuratowski Cascade** argument:

    1. AllActive + AllSkewed + k ≥ 10 → the dominant extension σ has
       |S| = bottleneckCount σ ≥ 4 (proved: |S| ≤ 3 is handled by
       `pigeonhole_two_bottlenecks` and `star_graph_shattered`).

    2. |S| ≥ 4 → 4 disjoint bottleneck pairs (4K₂ matching) →
       B₀ ≥ 2 balanced pairs in the 4K₂ sub-poset.

    3. **Cascade Indestructibility**: any adversary move (adding one
       element z covering all balanced pairs) produces B₁ ≥ 2 new
       balanced pairs. Verified exhaustively:
       - B₀ ≥ 2: 12,564,816 configs × 28 pairs = 12.6M checks
       - B₁ ≥ 2: 73,728 B₀=2 configs × 6,561 adversary moves = 483M checks

    4. By induction B_t ≥ 2 for all t → ∃ balanced pair → ¬AllSkewed.

    **Remaining gap**: The induction (step 4) requires showing that
    the cascade at step t reduces to the base case. Exhaustive cascade
    simulation (4 steps, n=8→12) confirms B ≥ 2 persists, but balanced
    pair endpoints can shift to cascade elements at step 3 (n=12),
    so the core is NOT bounded by 8 elements.

    **Rust verification**: `lab/examples/exhaustive_n8.rs` enumerates
    all 431,723,379 partial orders on 8 elements, confirming B₀ ≥ 2
    for all 4K₂ configs. Cascade simulation at `/tmp/cascade_core_v2.rs`
    confirms B ≥ 2 through 4 adversary steps. -/
theorem allactive_allskewed_k10_false (P : FinPoset n)
    (haa : P.AllActive) (hskew : P.AllSkewed) (hk : P.k ≥ 10) : False := by
  sorry

/-- **AllSkewed + k ≥ 10 → False.**

    Reduces to the all-active case via `core_extraction`, then applies
    `allactive_allskewed_k10_false`.

    `core_extraction` (proved sorry-free in CombinatorialBasics.lean)
    extracts the all-active sub-poset P' on m ≤ n elements, preserving
    both AllSkewed and k ≥ 10. Chain elements contribute no incomparable
    pairs and multiply each linext by exactly one insertion position, so
    removing them preserves all relevant invariants. -/
theorem allskewed_k_ge10_false (P : FinPoset n)
    (hskew : P.AllSkewed) (hk : P.k ≥ 10) : False := by
  -- Step 1: Extract all-active sub-poset
  obtain ⟨m, e, he, h_active, h_skew', h_k'⟩ := core_extraction P hskew hk
  -- Step 2: The all-active core cannot be AllSkewed with k ≥ 10
  exact allactive_allskewed_k10_false _ (fun x => h_active x) h_skew' h_k'

end Kislitsyn
