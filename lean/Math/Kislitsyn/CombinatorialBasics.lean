import Mathlib.GroupTheory.Perm.Basic
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Data.Fintype.Perm
import Mathlib.Tactic.Push
import Mathlib.Tactic.ByCases
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Linarith
import Mathlib.Order.Extension.Linear
import Mathlib.Order.Interval.Finset.Nat
import Math.Kislitsyn.SmallCases

/-!
# The 1/3-2/3 Poset Conjecture — Lean 4 Formalization

**Kislitsyn (1968), Fredman (1976):**
For every finite poset P that is not a total order,
∃ incomparable x, y with  1/3 ≤ Pr[x <_σ y] ≤ 2/3.

## Diophantine Form (no rationals)
  3 · min(c(x,y), k − c(x,y)) ≥ k
where c(x,y) = |{σ ∈ L(P) : x <_σ y}| and k = |L(P)|.

## Architecture
Curry-Howard skeleton: types = propositions, `sorry` = deferred proofs.
  - Phase 0: Direct cases k ≤ 3
  - Phase 3: Majority Tournament → σ_dom
  - Phase 4: Bottleneck Decomposition
  - Phase 5: Inclusion-Exclusion + Disjoint Commutativity
  - Phase 6: Geometric Collapse (parallel chains self-contradiction)
-/

open scoped Classical
open Finset Equiv

namespace Kislitsyn

-- ═════════════════════════════════════════════════════════════════
-- §1. FOUNDATIONAL DEFINITIONS
-- ═════════════════════════════════════════════════════════════════

/-- A finite poset on n labeled elements.
    Packaged as data (not a typeclass) so multiple posets on Fin n coexist. -/
structure FinPoset (n : ℕ) where
  /-- The partial order relation a ≤_P b -/
  le : Fin n → Fin n → Prop
  le_refl     : ∀ a, le a a
  le_antisymm : ∀ a b, le a b → le b a → a = b
  le_trans    : ∀ a b c, le a b → le b c → le a c

variable {n : ℕ}

/-- Incomparability: neither a ≤ b nor b ≤ a -/
def FinPoset.Incomp (P : FinPoset n) (x y : Fin n) : Prop :=
  ¬P.le x y ∧ ¬P.le y x

/-- P is not a total order (chain) -/
def FinPoset.NonChain (P : FinPoset n) : Prop :=
  ∃ x y, P.Incomp x y

/-- σ is a linear extension of P.
    Convention: σ maps positions → elements, so σ.symm maps elements → positions.
    Condition: a ≤_P b  →  position(a) ≤ position(b). -/
def FinPoset.IsLinExt (P : FinPoset n) (σ : Perm (Fin n)) : Prop :=
  ∀ a b, P.le a b → (σ.symm a).val ≤ (σ.symm b).val

/-- L(P) = the finite set of all linear extensions -/
noncomputable def FinPoset.linExts (P : FinPoset n) : Finset (Perm (Fin n)) :=
  Finset.univ.filter P.IsLinExt

/-- k = |L(P)| = number of linear extensions -/
noncomputable def FinPoset.k (P : FinPoset n) : ℕ :=
  P.linExts.card

/-- c(x,y) = |{σ ∈ L(P) : x appears strictly before y in σ}| -/
noncomputable def FinPoset.c (P : FinPoset n) (x y : Fin n) : ℕ :=
  (P.linExts.filter fun σ ↦ (σ.symm x).val < (σ.symm y).val).card

/-- minority(x,y) = min(c(x,y), k − c(x,y)) -/
noncomputable def FinPoset.minority (P : FinPoset n) (x y : Fin n) : ℕ :=
  min (P.c x y) (P.k - P.c x y)

-- ═════════════════════════════════════════════════════════════════
-- §2. CORE PREDICATES
-- ═════════════════════════════════════════════════════════════════

/-- The 1/3 balance condition in Diophantine form:
    "pair (x,y) is balanced" iff 3 · minority(x,y) ≥ k -/
def FinPoset.Balanced (P : FinPoset n) (x y : Fin n) : Prop :=
  3 * P.minority x y ≥ P.k

/-- Global skewness: the false assumption for proof by contradiction.
    "every incomparable pair has minority strictly less than k/3" -/
def FinPoset.AllSkewed (P : FinPoset n) : Prop :=
  ∀ x y, P.Incomp x y → 3 * P.minority x y < P.k


-- ═════════════════════════════════════════════════════════════════
-- §3. MAJORITY TOURNAMENT INFRASTRUCTURE
-- ═════════════════════════════════════════════════════════════════

/-- x majority-precedes y: x comes before y in more than half the extensions.
    Diophantine form: 2 · c(x,y) > k. -/
noncomputable def FinPoset.MajPrec (P : FinPoset n) (x y : Fin n) : Prop :=
  2 * P.c x y > P.k

/-- σ is a dominant extension: it is a linear extension that agrees with
    the majority direction on every incomparable pair. -/
noncomputable def FinPoset.Dominant (P : FinPoset n) (σ : Perm (Fin n)) : Prop :=
  P.IsLinExt σ ∧
  ∀ x y, P.Incomp x y → P.MajPrec x y →
    (σ.symm x).val < (σ.symm y).val

-- ═════════════════════════════════════════════════════════════════
-- §4. BOTTLENECK INFRASTRUCTURE
-- ═════════════════════════════════════════════════════════════════

/-- Position i in σ is an active bottleneck if the elements σ(i) and σ(i+1)
    are incomparable in P.  Requires i + 1 < n. -/
noncomputable def FinPoset.IsBottleneck (P : FinPoset n) (σ : Perm (Fin n))
    (i : ℕ) (hi : i + 1 < n) : Prop :=
  P.Incomp (σ ⟨i, by omega⟩) (σ ⟨i + 1, hi⟩)

/-- M_i = minority set at bottleneck position i:
    the set of linear extensions where σ(i+1) appears before σ(i). -/
noncomputable def FinPoset.M (P : FinPoset n) (σ : Perm (Fin n))
    (i : ℕ) (hi : i + 1 < n) : Finset (Perm (Fin n)) :=
  P.linExts.filter fun τ ↦
    (τ.symm (σ ⟨i + 1, hi⟩)).val < (τ.symm (σ ⟨i, by omega⟩)).val

/-- |S| = number of active bottleneck positions in σ -/
noncomputable def FinPoset.bottleneckCount (P : FinPoset n)
    (σ : Perm (Fin n)) : ℕ :=
  ((Finset.range (n - 1)).filter fun i ↦
    ∃ hi : i + 1 < n, P.IsBottleneck σ i hi).card

-- ═════════════════════════════════════════════════════════════════
-- §4½. HELPER LEMMAS
-- ═════════════════════════════════════════════════════════════════

/-- Incomparable elements are distinct -/
lemma FinPoset.Incomp.ne {P : FinPoset n} {x y : Fin n} (h : P.Incomp x y) : x ≠ y := by
  intro heq; subst heq; exact h.1 (P.le_refl x)

/-- c(x,y) ≤ k (filter is a subset) -/
lemma c_le_k (P : FinPoset n) (x y : Fin n) : P.c x y ≤ P.k :=
  Finset.card_filter_le _ _

/-- Monotonicity left: P.le a b → c(b,c) ≤ c(a,c).
    Every σ with pos(b) < pos(c) also has pos(a) ≤ pos(b) < pos(c). -/
lemma c_mono_left (P : FinPoset n) (a b c : Fin n) (hab : P.le a b) :
    P.c b c ≤ P.c a c := by
  unfold FinPoset.c FinPoset.linExts
  apply Finset.card_le_card
  intro σ hσ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
  exact ⟨hσ.1, lt_of_le_of_lt (hσ.1 a b hab) hσ.2⟩

/-- Monotonicity right: P.le b c → c(a,b) ≤ c(a,c).
    Every σ with pos(a) < pos(b) also has pos(a) < pos(b) ≤ pos(c). -/
lemma c_mono_right (P : FinPoset n) (a b c : Fin n) (hbc : P.le b c) :
    P.c a b ≤ P.c a c := by
  unfold FinPoset.c FinPoset.linExts
  apply Finset.card_le_card
  intro σ hσ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
  exact ⟨hσ.1, lt_of_lt_of_le hσ.2 (hσ.1 b c hbc)⟩

/-- If P.le y x, then c(x,y) = 0: no extension places x strictly before y. -/
lemma c_eq_zero_of_le (P : FinPoset n) (x y : Fin n) (hle : P.le y x) :
    P.c x y = 0 := by
  have h1 := c_mono_left P y x y hle  -- P.c x y ≤ P.c y y
  have h2 : P.c y y = 0 := by unfold FinPoset.c; simp
  omega

/-- Szpilrajn helper: for incomparable x y, there exists a linear extension
    placing x strictly before y. Hence c(x,y) ≥ 1. -/
lemma c_pos_of_incomp (P : FinPoset n) (x y : Fin n) (hxy : P.Incomp x y) :
    P.c x y > 0 := by
  -- Build extended relation: r(a,b) := P.le a b ∨ (P.le a x ∧ P.le y b)
  -- This forces x ≤ y (take a=x, b=y: P.le x x ∧ P.le y y)
  let r (a b : Fin n) : Prop := P.le a b ∨ (P.le a x ∧ P.le y b)
  have hr_refl : ∀ a, r a a := fun a => Or.inl (P.le_refl a)
  have hr_trans : ∀ a b c, r a b → r b c → r a c := by
    intro a b c hab hbc
    rcases hab with hab | ⟨hax, hyb⟩ <;> rcases hbc with hbc | ⟨hbx, hyc⟩
    · exact Or.inl (P.le_trans a b c hab hbc)
    · exact Or.inr ⟨P.le_trans a b x hab hbx, hyc⟩
    · exact Or.inr ⟨hax, P.le_trans y b c hyb hbc⟩
    · exact Or.inr ⟨hax, hyc⟩
  have hr_antisymm : ∀ a b, r a b → r b a → a = b := by
    intro a b hab hba
    rcases hab with hab | ⟨hax, hyb⟩ <;> rcases hba with hba | ⟨hbx, hya⟩
    · exact P.le_antisymm a b hab hba
    · -- P.le a b, P.le b x, P.le y a → P.le y x → contradiction
      exact absurd (P.le_trans y b x (P.le_trans y a b hya hab) hbx) hxy.2
    · -- P.le a x, P.le y b, P.le b a → P.le y x → contradiction
      exact absurd (P.le_trans y a x (P.le_trans y b a hyb hba) hax) hxy.2
    · exact absurd (P.le_trans y b x hyb hbx) hxy.2
  have hr_po : IsPartialOrder (Fin n) r :=
    { refl := hr_refl, trans := hr_trans, antisymm := hr_antisymm }
  -- Szpilrajn: extend r to a linear order s ⊇ r
  obtain ⟨s, hs_lin, hrs⟩ := @extend_partialOrder (Fin n) r hr_po
  -- s is total, so we can build a rank function → permutation → linear extension
  have hs_refl := hs_lin.toIsPartialOrder.refl
  have hs_trans := hs_lin.toIsPartialOrder.trans
  have hs_antisymm := hs_lin.toIsPartialOrder.antisymm
  have hs_total := hs_lin.total
  -- s extends P.le
  have hs_ext : ∀ a b, P.le a b → s a b := fun a b h => hrs a b (Or.inl h)
  -- s forces x before y (strictly)
  have hs_xy : s x y := hrs x y (Or.inr ⟨P.le_refl x, P.le_refl y⟩)
  have hs_nyx : ¬s y x := by
    intro h; exact hxy.2 (by
      have := hs_antisymm x y hs_xy h
      subst this; exact P.le_refl x)
  -- Build rank: rk(a) = |{b : s b a, b ≠ a}|
  -- Actually, simpler: define strict part, count predecessors
  let lt_s (a b : Fin n) : Prop := s a b ∧ ¬s b a
  have hlt_irr : ∀ a, ¬lt_s a a := fun a ⟨_, h⟩ => h (hs_refl a)
  have hlt_trans : ∀ a b c, lt_s a b → lt_s b c → lt_s a c := by
    intro a b c ⟨hab, hnba⟩ ⟨hbc, hncb⟩
    exact ⟨hs_trans a b c hab hbc, fun hca =>
      hnba (hs_trans b c a hbc hca)⟩
  have hlt_tot : ∀ a b, a ≠ b → lt_s a b ∨ lt_s b a := by
    intro a b hne
    rcases hs_total a b with h | h
    · left; exact ⟨h, fun h' => hne (hs_antisymm a b h h')⟩
    · right; exact ⟨h, fun h' => hne (hs_antisymm a b h' h)⟩
  let rk (a : Fin n) := (Finset.univ.filter fun b => lt_s b a).card
  have hlt_rk : ∀ a b, lt_s a b → rk a < rk b := by
    intro a b ⟨hab, hnba⟩
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_of_subset (fun z hz => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
      exact hlt_trans z a b hz ⟨hab, hnba⟩)]
    exact ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ a, hab, hnba⟩,
      fun h => hlt_irr a (Finset.mem_filter.mp h).2⟩
  have hrk_lt : ∀ a, rk a < n := by
    intro a
    calc rk a < Finset.univ.card := by
            apply Finset.card_lt_card
            rw [Finset.ssubset_iff_of_subset (Finset.filter_subset _ _)]
            exact ⟨a, Finset.mem_univ a,
              fun h => hlt_irr a (Finset.mem_filter.mp h).2⟩
      _ = n := by rw [Finset.card_univ, Fintype.card_fin]
  let f : Fin n → Fin n := fun a => ⟨rk a, hrk_lt a⟩
  have hf_inj : Function.Injective f := by
    intro a b hab
    by_contra hne
    simp only [f, Fin.mk.injEq] at hab
    rcases hlt_tot a b hne with h | h
    · have := hlt_rk a b h; omega
    · have := hlt_rk b a h; omega
  have hbij : Function.Bijective f := Finite.injective_iff_bijective.mp hf_inj
  let σ := (Equiv.ofBijective f hbij).symm
  -- σ is a linear extension of P
  have hσ_le : P.IsLinExt σ := by
    intro a b hab
    change (f a).val ≤ (f b).val
    by_cases heq : a = b
    · subst heq; exact le_refl _
    · exact le_of_lt (hlt_rk a b ⟨hs_ext a b hab,
        fun h => heq (hs_antisymm a b (hs_ext a b hab) h)⟩)
  -- σ places x strictly before y
  have hσ_xy : (σ.symm x).val < (σ.symm y).val := by
    change (f x).val < (f y).val
    exact hlt_rk x y ⟨hs_xy, hs_nyx⟩
  -- Therefore σ ∈ linExts and in the c(x,y) filter
  have hσ_mem : σ ∈ P.linExts := by
    simp only [FinPoset.linExts, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hσ_le
  have hσ_filt : σ ∈ P.linExts.filter (fun τ => (τ.symm x).val < (τ.symm y).val) := by
    exact Finset.mem_filter.mpr ⟨hσ_mem, hσ_xy⟩
  -- c(x,y) ≥ 1
  unfold FinPoset.c
  exact Finset.card_pos.mpr ⟨σ, hσ_filt⟩

-- ═════════════════════════════════════════════════════════════════
-- §5. BASIC STRUCTURAL PROPERTIES
-- ═════════════════════════════════════════════════════════════════

/-- c(x,y) + c(y,x) = k for distinct elements -/
lemma c_complement (P : FinPoset n) (x y : Fin n) (hne : x ≠ y) :
    P.c x y + P.c y x = P.k := by
  unfold FinPoset.c FinPoset.k
  have hne_pos : ∀ (σ : Perm (Fin n)), (σ.symm x).val ≠ (σ.symm y).val :=
    fun σ h ↦ hne (σ.symm.injective (Fin.ext h))
  have h_eq : P.linExts.filter (fun σ ↦ (σ.symm y).val < (σ.symm x).val) =
      P.linExts.filter (fun σ ↦ ¬((σ.symm x).val < (σ.symm y).val)) :=
    Finset.filter_congr fun σ _ ↦
      ⟨fun h h' ↦ lt_asymm h h',
       fun h ↦ lt_of_le_of_ne (not_lt.mp h) (Ne.symm (hne_pos σ))⟩
  rw [h_eq]
  exact Finset.card_filter_add_card_filter_not _

/-- A non-chain has at least 2 linear extensions -/
lemma nonchain_k_ge_two (P : FinPoset n) (h : P.NonChain) :
    P.k ≥ 2 := by
  obtain ⟨x, y, hxy⟩ := h
  have hcxy := c_pos_of_incomp P x y hxy
  have hcyx := c_pos_of_incomp P y x ⟨hxy.2, hxy.1⟩
  have hcomp := c_complement P x y hxy.ne
  omega

/-- |M_i| equals minority(σ(i), σ(i+1)) when σ is dominant -/
lemma bottleneck_minority_eq (P : FinPoset n) (σ : Perm (Fin n))
    (hσ : P.Dominant σ) (i : ℕ) (hi : i + 1 < n)
    (hbot : P.IsBottleneck σ i hi) :
    (P.M σ i hi).card = P.minority (σ ⟨i, by omega⟩) (σ ⟨i + 1, hi⟩) := by
  -- |M_i| = c(σ(i+1), σ(i)) by definitional equality of the filter
  change P.c (σ ⟨i + 1, hi⟩) (σ ⟨i, by omega⟩) =
    P.minority (σ ⟨i, by omega⟩) (σ ⟨i + 1, hi⟩)
  set x := σ ⟨i, by omega⟩
  set y := σ ⟨i + 1, hi⟩
  have hne : x ≠ y := hbot.ne
  have hcomp := c_complement P x y hne
  have hle := c_le_k P x y
  -- 2·c(x,y) ≥ k: if 2·c(x,y) < k, then MajPrec y x holds,
  -- and Dominant would place y before x. But σ places x at position i
  -- and y at position i+1, so σ.symm(x) < σ.symm(y). Contradiction.
  have hge : 2 * P.c x y ≥ P.k := by
    by_contra h
    push_neg at h
    -- MajPrec y x holds
    have hmaj_yx : P.MajPrec y x := by unfold FinPoset.MajPrec; omega
    -- Dominant gives σ.symm(y) < σ.symm(x)
    have hdom := hσ.2 y x ⟨hbot.2, hbot.1⟩ hmaj_yx
    -- But σ.symm(x) = i < i+1 = σ.symm(y)
    simp [x, y, Equiv.symm_apply_apply] at hdom
  -- minority(x,y) = min(c(x,y), k - c(x,y)) = k - c(x,y) since 2·c(x,y) ≥ k
  unfold FinPoset.minority
  have : P.c x y ≥ P.k - P.c x y := by omega
  rw [min_eq_right this]; omega

-- ═════════════════════════════════════════════════════════════════
-- §5½. SKEWED ⟹ SUPERMAJORITY HELPERS
-- ═════════════════════════════════════════════════════════════════

/-- Under AllSkewed, every incomparable pair has a strict 2/3 supermajority
    in one direction: 3·c(x,y) > 2k or 3·c(y,x) > 2k. -/
lemma allSkewed_implies_majority (P : FinPoset n) (hskew : P.AllSkewed)
    (x y : Fin n) (hxy : P.Incomp x y) :
    3 * P.c x y > 2 * P.k ∨ 3 * P.c y x > 2 * P.k := by
  have hcomp := c_complement P x y hxy.ne
  have hle := c_le_k P x y
  have hskew_xy := hskew x y hxy
  unfold FinPoset.minority at hskew_xy
  by_cases h : P.c x y ≤ P.k - P.c x y
  · rw [min_eq_left h] at hskew_xy; right; omega
  · push_neg at h; rw [min_eq_right (le_of_lt h)] at hskew_xy; left; omega

/-- Amplification: AllSkewed + Incomp + 3·c(x,y) > k ⟹ 3·c(x,y) > 2k.
    If the minority were c(x,y), we'd have 3·c(x,y) < k, contradicting the hypothesis. -/
lemma skewed_amplify (P : FinPoset n) (hskew : P.AllSkewed)
    (x y : Fin n) (hxy : P.Incomp x y) (h : 3 * P.c x y > P.k) :
    3 * P.c x y > 2 * P.k := by
  have hsk := hskew x y hxy
  unfold FinPoset.minority at hsk
  have hle := c_le_k P x y
  by_cases hm : P.c x y ≤ P.k - P.c x y
  · rw [min_eq_left hm] at hsk; omega
  · push_neg at hm; rw [min_eq_right (le_of_lt hm)] at hsk; omega

/-- Under AllSkewed, MajPrec already implies the stronger 2/3 supermajority. -/
lemma skewed_supermajority (P : FinPoset n) (hskew : P.AllSkewed)
    (x y : Fin n) (hxy : P.Incomp x y) (hmaj : P.MajPrec x y) :
    3 * P.c x y > 2 * P.k := by
  apply skewed_amplify P hskew x y hxy
  unfold FinPoset.MajPrec at hmaj; omega

-- ═════════════════════════════════════════════════════════════════
-- §6. LEMMA 1 — Majority Tournament (Phase 3)
--     Under AllSkewed, the majority relation is transitive.
--     This produces the unique dominant extension σ_dom.
-- ═════════════════════════════════════════════════════════════════

/-- 2/3-Transitivity Lemma:
    If c(x,y) > 2k/3 and c(y,z) > 2k/3, then c(x,z) > k/3.
    Proof: |{σ : x<y ∧ y<z}| ≥ c(x,y) + c(y,z) − k > k/3,
    and x<y<z implies x<z, so c(x,z) ≥ that count.
    Diophantine: 3·c(x,y) > 2k ∧ 3·c(y,z) > 2k → 3·c(x,z) > k. -/
lemma two_thirds_transitivity (P : FinPoset n) (x y z : Fin n)
    (hxy : 3 * P.c x y > 2 * P.k) (hyz : 3 * P.c y z > 2 * P.k) :
    3 * P.c x z > P.k := by
  suffices h : P.c x z + P.k ≥ P.c x y + P.c y z by omega
  unfold FinPoset.c FinPoset.k
  set A := P.linExts.filter fun σ ↦ (σ.symm x).val < (σ.symm y).val with hA_def
  set B := P.linExts.filter fun σ ↦ (σ.symm y).val < (σ.symm z).val with hB_def
  set C := P.linExts.filter fun σ ↦ (σ.symm x).val < (σ.symm z).val with hC_def
  have h_sub : A ∩ B ⊆ C := by
    intro σ hσ
    simp only [hA_def, hB_def, hC_def, Finset.mem_inter, Finset.mem_filter] at hσ ⊢
    exact ⟨hσ.1.1, lt_trans hσ.1.2 hσ.2.2⟩
  have h_ie := Finset.card_union_add_card_inter A B
  have h_ub : (A ∪ B).card ≤ P.linExts.card :=
    Finset.card_le_card (Finset.union_subset
      (Finset.filter_subset _ _) (Finset.filter_subset _ _))
  have h_ic := Finset.card_le_card h_sub
  linarith

/-- Under AllSkewed with k ≥ 4, the enriched relation
    R(a,b) := (P.le a b ∧ a ≠ b) ∨ (Incomp a b ∧ MajPrec a b)
    is a strict total order extending P and agreeing with majority. -/
lemma majority_tournament_transitive (P : FinPoset n)
    (hk : P.k ≥ 4) (hskew : P.AllSkewed) :
    ∃ (R : Fin n → Fin n → Prop),
      (∀ a b, R a b → ¬R b a) ∧
      (∀ a b c, R a b → R b c → R a c) ∧
      (∀ a b, a ≠ b → R a b ∨ R b a) ∧
      (∀ a b, P.le a b → a ≠ b → R a b) ∧
      (∀ a b, P.Incomp a b → P.MajPrec a b → R a b) := by
  let R (a b : Fin n) : Prop := (P.le a b ∧ a ≠ b) ∨ (P.Incomp a b ∧ P.MajPrec a b)
  refine ⟨R, ?_, ?_, ?_, ?_, ?_⟩
  -- ── Asymmetry ──
  · intro a b hab hba
    rcases hab with ⟨hab_le, hab_ne⟩ | ⟨hab_inc, hab_maj⟩ <;>
      rcases hba with ⟨hba_le, _⟩ | ⟨hba_inc, hba_maj⟩
    · exact hab_ne (P.le_antisymm a b hab_le hba_le)
    · exact hba_inc.2 hab_le
    · exact hab_inc.2 hba_le
    · have := c_complement P a b hab_inc.ne
      unfold FinPoset.MajPrec at hab_maj hba_maj; omega
  -- ── Transitivity ──
  · intro a b c hab hbc
    rcases hab with ⟨hab_le, hab_ne⟩ | ⟨hab_inc, hab_maj⟩ <;>
      rcases hbc with ⟨hbc_le, hbc_ne⟩ | ⟨hbc_inc, hbc_maj⟩
    -- (le, le)
    · left; exact ⟨P.le_trans a b c hab_le hbc_le,
        fun heq ↦ by rw [← heq] at hbc_le; exact hab_ne (P.le_antisymm a b hab_le hbc_le)⟩
    -- (le, incomp+maj)
    · have hca : ¬P.le c a := fun h ↦ hbc_inc.2 (P.le_trans c a b h hab_le)
      by_cases hac : P.le a c
      · left; exact ⟨hac, fun heq ↦ by rw [← heq] at hbc_inc; exact hbc_inc.2 hab_le⟩
      · right; exact ⟨⟨hac, hca⟩, by
          unfold FinPoset.MajPrec at hbc_maj ⊢
          have := c_mono_left P a b c hab_le; omega⟩
    -- (incomp+maj, le)
    · have hca : ¬P.le c a := fun h ↦ hab_inc.2 (P.le_trans b c a hbc_le h)
      by_cases hac : P.le a c
      · left; exact ⟨hac, fun heq ↦ by rw [← heq] at hbc_le; exact hab_inc.2 hbc_le⟩
      · right; exact ⟨⟨hac, hca⟩, by
          unfold FinPoset.MajPrec at hab_maj ⊢
          have := c_mono_right P a b c hbc_le; omega⟩
    -- (incomp+maj, incomp+maj)
    · have hab_s := skewed_supermajority P hskew a b hab_inc hab_maj
      have hbc_s := skewed_supermajority P hskew b c hbc_inc hbc_maj
      have hac_gt := two_thirds_transitivity P a b c hab_s hbc_s
      have hca : ¬P.le c a := by
        intro h; have := c_eq_zero_of_le P a c h; omega
      by_cases hac : P.le a c
      · left; exact ⟨hac, fun heq ↦ by
          rw [← heq] at hbc_inc hbc_maj
          have := c_complement P a b hab_inc.ne
          unfold FinPoset.MajPrec at hab_maj hbc_maj; omega⟩
      · right; exact ⟨⟨hac, hca⟩, by
          have := skewed_amplify P hskew a c ⟨hac, hca⟩ hac_gt
          unfold FinPoset.MajPrec; omega⟩
  -- ── Totality ──
  · intro a b hne
    by_cases hab : P.le a b
    · left; left; exact ⟨hab, hne⟩
    · by_cases hba : P.le b a
      · right; left; exact ⟨hba, Ne.symm hne⟩
      · have hinc : P.Incomp a b := ⟨hab, hba⟩
        rcases allSkewed_implies_majority P hskew a b hinc with h | h
        · left; right; exact ⟨hinc, by unfold FinPoset.MajPrec; omega⟩
        · right; right; exact ⟨⟨hba, hab⟩, by unfold FinPoset.MajPrec; omega⟩
  -- ── Extends P ──
  · intro a b hab hne; left; exact ⟨hab, hne⟩
  -- ── Agrees with majority ──
  · intro a b hinc hmaj; right; exact ⟨hinc, hmaj⟩

/-- Constructive plumbing: a strict total order on Fin n that extends P
    and agrees with majority can be realized as a Perm (Fin n) satisfying Dominant.
    (Requires Mathlib LinearOrder → Fintype.equivFin machinery.) -/
lemma dominant_of_transitive_tournament (P : FinPoset n)
    (R : Fin n → Fin n → Prop)
    (hasym : ∀ a b, R a b → ¬R b a)
    (htrans : ∀ a b c, R a b → R b c → R a c)
    (htot : ∀ a b, a ≠ b → R a b ∨ R b a)
    (hext : ∀ a b, P.le a b → a ≠ b → R a b)
    (hmaj : ∀ a b, P.Incomp a b → P.MajPrec a b → R a b) :
    ∃ σ : Perm (Fin n), P.Dominant σ := by
  -- Irreflexivity from asymmetry
  have hirr : ∀ x, ¬R x x := fun x h => hasym x x h h
  -- Rank function: rk(x) = |{y : R y x}|
  let rk (x : Fin n) := (Finset.univ.filter fun y => R y x).card
  -- R-monotonicity of rank: R x y → rk x < rk y
  have hR_rk : ∀ x y, R x y → rk x < rk y := by
    intro x y hxy
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_of_subset (fun z hz => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
      exact htrans z x y hz hxy)]
    exact ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ x, hxy⟩,
      fun h => hirr x (Finset.mem_filter.mp h).2⟩
  -- Rank is bounded: rk(x) < n
  have hrk_lt : ∀ x, rk x < n := by
    intro x
    calc rk x < Finset.univ.card := by
            apply Finset.card_lt_card
            rw [Finset.ssubset_iff_of_subset (Finset.filter_subset _ _)]
            exact ⟨x, Finset.mem_univ x,
              fun h => hirr x (Finset.mem_filter.mp h).2⟩
      _ = n := by rw [Finset.card_univ, Fintype.card_fin]
  -- Build the Fin n → Fin n function
  let f : Fin n → Fin n := fun x => ⟨rk x, hrk_lt x⟩
  -- Injectivity from rank monotonicity + totality
  have hf_inj : Function.Injective f := by
    intro x y hxy
    by_contra hne
    simp only [f, Fin.mk.injEq] at hxy
    rcases htot x y hne with h | h
    · have := hR_rk x y h; omega
    · have := hR_rk y x h; omega
  -- Injective on Fin n → bijective
  have hbij : Function.Bijective f := Finite.injective_iff_bijective.mp hf_inj
  -- Build the permutation
  refine ⟨(Equiv.ofBijective f hbij).symm, ?_, ?_⟩
  -- Goal 1: IsLinExt — P.le a b → rk a ≤ rk b
  · intro a b hab
    change (f a).val ≤ (f b).val
    by_cases heq : a = b
    · subst heq; exact le_refl _
    · exact le_of_lt (hR_rk a b (hext a b hab heq))
  -- Goal 2: Majority — Incomp x y → MajPrec x y → rk x < rk y
  · intro x y hxy hmaj_xy
    change (f x).val < (f y).val
    exact hR_rk x y (hmaj x y hxy hmaj_xy)

/-- Under AllSkewed with k ≥ 4, the majority relation is a strict total order,
    hence there exists a unique dominant linear extension. -/
lemma majority_is_transitive (P : FinPoset n)
    (hk : P.k ≥ 4) (hskew : P.AllSkewed) :
    ∃ σ : Perm (Fin n), P.Dominant σ := by
  obtain ⟨R, hasym, htrans, htot, hext, hmaj⟩ := majority_tournament_transitive P hk hskew
  exact dominant_of_transitive_tournament P R hasym htrans htot hext hmaj

-- ═════════════════════════════════════════════════════════════════
-- §7. LEMMA 2 — Bottleneck Coverage (Phase 4)
--     Every non-dominant extension flips at least one active bottleneck.
-- ═════════════════════════════════════════════════════════════════

/-- A permutation of Fin n that is strictly monotone on consecutive positions
    is the identity. -/
private lemma perm_of_strictMono_eq_one (π : Perm (Fin n))
    (hmono : ∀ (i : ℕ) (hi : i + 1 < n),
      (π ⟨i, by omega⟩).val < (π ⟨i + 1, hi⟩).val) :
    π = 1 := by
  ext ⟨i, hi⟩; simp only [Equiv.Perm.one_apply]
  apply le_antisymm
  -- Upper bound: (π ⟨i, hi⟩).val ≤ i
  -- Spread: π(i) + (b − i) ≤ π(b) for i ≤ b, so π(i) + (n−1−i) ≤ π(n−1) < n
  · suffices ∀ (b : ℕ) (hb : b < n), i ≤ b →
        (π ⟨i, hi⟩).val + (b - i) ≤ (π ⟨b, hb⟩).val by
      have := this (n - 1) (by omega) (by omega)
      have := (π ⟨n - 1, by omega⟩).isLt
      omega
    intro b hb hib
    induction b with
    | zero => have := Nat.le_zero.mp hib; subst this; exact le_refl _
    | succ k ih =>
      rcases Nat.eq_or_lt_of_le hib with rfl | hlt
      · omega
      · have := hmono k (by omega)
        have := ih (by omega) (by omega)
        omega
  -- Lower bound: i ≤ (π ⟨i, hi⟩).val
  · induction i with
    | zero => exact Nat.zero_le _
    | succ k ih =>
      have := hmono k hi
      have := ih (by omega)
      omega

/-- Any linear extension τ ≠ σ_dom must invert at least one adjacent
    bottleneck pair from σ_dom. -/
lemma bottleneck_coverage (P : FinPoset n) (σ : Perm (Fin n))
    (hσ : P.Dominant σ) (τ : Perm (Fin n))
    (hτ : P.IsLinExt τ) (hne : τ ≠ σ) :
    ∃ i : ℕ, ∃ hi : i + 1 < n,
      P.IsBottleneck σ i hi ∧ τ ∈ P.M σ i hi := by
  by_contra h_neg
  push_neg at h_neg
  -- h_neg : ∀ i hi, P.IsBottleneck σ i hi → τ ∉ P.M σ i hi
  apply hne
  have hτ_mem : τ ∈ P.linExts := by
    simp only [FinPoset.linExts, Finset.mem_filter, Finset.mem_univ, true_and]; exact hτ
  -- Step 1: τ.symm ∘ σ is strictly monotone on consecutive positions
  let π := τ.symm * σ
  have h_mono : ∀ (i : ℕ) (hi : i + 1 < n),
      (π ⟨i, by omega⟩).val < (π ⟨i + 1, hi⟩).val := by
    intro i hi
    simp only [π, Equiv.Perm.mul_apply]
    have hval_ne : (τ.symm (σ ⟨i, by omega⟩)).val ≠ (τ.symm (σ ⟨i + 1, hi⟩)).val := by
      intro h
      have h1 : σ ⟨i, by omega⟩ = σ ⟨i + 1, hi⟩ := τ.symm.injective (Fin.ext h)
      have h2 := σ.injective h1
      simp only [Fin.mk.injEq] at h2; omega
    suffices (τ.symm (σ ⟨i, by omega⟩)).val ≤ (τ.symm (σ ⟨i + 1, hi⟩)).val by omega
    by_cases hle : P.le (σ ⟨i, by omega⟩) (σ ⟨i + 1, hi⟩)
    · exact hτ _ _ hle
    · by_cases hle' : P.le (σ ⟨i + 1, hi⟩) (σ ⟨i, by omega⟩)
      · exfalso
        have h := hσ.1 _ _ hle'
        have h1 : (σ.symm (σ ⟨i + 1, hi⟩)).val = i + 1 :=
          congr_arg Fin.val (σ.symm_apply_apply _)
        have h2 : (σ.symm (σ ⟨i, by omega⟩)).val = i :=
          congr_arg Fin.val (σ.symm_apply_apply _)
        omega
      · exact not_lt.mp (fun h_lt =>
          h_neg i hi ⟨hle, hle'⟩ (Finset.mem_filter.mpr ⟨hτ_mem, h_lt⟩))
  -- Step 2: strictly monotone perm = identity
  have hπ := perm_of_strictMono_eq_one π h_mono
  -- Step 3: π = 1 implies τ = σ
  apply Equiv.ext; intro x
  have h1 : τ.symm (σ x) = x := by
    have := Equiv.Perm.ext_iff.mp hπ x
    simp only [Equiv.Perm.one_apply] at this
    exact this
  have h2 := congr_arg τ h1
  rw [Equiv.apply_symm_apply] at h2
  exact h2.symm

-- ═════════════════════════════════════════════════════════════════
-- §8. LEMMA 3 — Overlap Volume Squeeze (Phase 5)
--     Under AllSkewed, the overlap Ω = Σ|M_i| − (k−1) is bounded.
-- ═════════════════════════════════════════════════════════════════

/-- |S| ≤ 2 case: pigeonhole gives max |M_i| ≥ ⌈(k−1)/2⌉ ≥ ⌈k/3⌉,
    contradicting AllSkewed. -/
lemma pigeonhole_two_bottlenecks (P : FinPoset n) (σ : Perm (Fin n))
    (hσ : P.Dominant σ) (hk : P.k ≥ 4)
    (hskew : P.AllSkewed)
    (hS : P.bottleneckCount σ ≤ 2) :
    False := by
  -- σ ∈ linExts
  have hσ_mem : σ ∈ P.linExts := by
    simp only [FinPoset.linExts, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hσ.1
  -- The bottleneck index set S
  set S := (Finset.range (n - 1)).filter (fun i ↦
    ∃ hi : i + 1 < n, P.IsBottleneck σ i hi) with hS_def
  -- S.card = bottleneckCount σ ≤ 2
  have hS_card : S.card ≤ 2 := hS
  -- For i ∈ S, we can extract the hi proof
  have hi_of_mem : ∀ i ∈ S, i + 1 < n := by
    intro i hi; simp only [S, Finset.mem_filter, Finset.mem_range] at hi; omega
  -- Define the union of M_i over S using dite
  set U := S.biUnion (fun i ↦ if h : i + 1 < n then P.M σ i h else ∅) with hU_def
  -- Coverage: every non-dominant τ is in U
  have h_cover : P.linExts.erase σ ⊆ U := by
    intro τ hτ
    rw [Finset.mem_erase] at hτ
    have hτ_le : P.IsLinExt τ := by
      simp only [FinPoset.linExts, Finset.mem_filter, Finset.mem_univ, true_and] at hτ
      exact hτ.2
    obtain ⟨i, hi, hbot, hτ_in⟩ := bottleneck_coverage P σ hσ τ hτ_le hτ.1
    simp only [hU_def, Finset.mem_biUnion]
    exact ⟨i, by simp only [hS_def, Finset.mem_filter, Finset.mem_range]; exact ⟨by omega, hi, hbot⟩,
      by simp only [dif_pos hi]; exact hτ_in⟩
  -- Cardinality: k - 1 ≤ |U|
  have h_erase_card : (P.linExts.erase σ).card = P.k - 1 :=
    Finset.card_erase_of_mem hσ_mem
  have h_k_le_U : P.k - 1 ≤ U.card := h_erase_card ▸ Finset.card_le_card h_cover
  -- |U| ≤ Σ_{i ∈ S} |f i|
  let f := fun i ↦ if h : i + 1 < n then P.M σ i h else ∅
  have h_U_le_sum : U.card ≤ S.sum (fun i ↦ (f i).card) := Finset.card_biUnion_le
  -- Each |(f i)| is bounded: 3 * |(f i)| < k
  have h_each : ∀ i ∈ S, (f i).card ≤ (P.k - 1) / 3 := by
    intro i hi_S
    have hi := hi_of_mem i hi_S
    simp only [f, dif_pos hi]
    obtain ⟨hi', hbot⟩ := (Finset.mem_filter.mp hi_S).2
    -- hi and hi' are both proofs of i + 1 < n; they're proof-irrelevant (Prop)
    have hbot' : P.IsBottleneck σ i hi := by convert hbot
    rw [bottleneck_minority_eq P σ hσ i hi hbot']
    have hsk := hskew _ _ hbot'
    unfold FinPoset.minority at hsk ⊢
    omega
  -- Σ ≤ |S| • ((k-1)/3) via sum_le_card_nsmul
  have h_sum_le := Finset.sum_le_card_nsmul S (fun i ↦ (f i).card) _ h_each
  -- Explicit chain to contradiction
  simp only [smul_eq_mul] at h_sum_le
  -- k - 1 ≤ sum ≤ S.card * ((k-1)/3) ≤ 2 * ((k-1)/3)
  have h_chain : P.k - 1 ≤ 2 * ((P.k - 1) / 3) := by
    calc P.k - 1 ≤ U.card := h_k_le_U
      _ ≤ S.sum (fun i ↦ (f i).card) := h_U_le_sum
      _ ≤ S.card * ((P.k - 1) / 3) := h_sum_le
      _ ≤ 2 * ((P.k - 1) / 3) := Nat.mul_le_mul_right _ hS_card
  -- 3 * (k-1) ≤ 6 * ((k-1)/3) ≤ 2*(k-1), contradiction for k ≥ 4
  have : (P.k - 1) / 3 * 3 ≤ P.k - 1 := Nat.div_mul_le_self _ _
  omega

-- ═════════════════════════════════════════════════════════════════
-- §9. LEMMA 4 — Disjoint Commutativity (Phase 5)
--     Disjoint adjacent transpositions commute in the permutohedron.
--     This shatters the Star Graph (Ω = 0) forced by |S| = 3, k ≡ 1.
-- ═════════════════════════════════════════════════════════════════

/-- Among ≥ 3 bottleneck positions p₁ < p₂ < ··· < p_s,
    the first and last have gap p_s − p₁ ≥ s − 1 ≥ 2 → disjoint. -/
lemma exists_disjoint_bottlenecks (P : FinPoset n) (σ : Perm (Fin n))
    (hS : P.bottleneckCount σ ≥ 3) :
    ∃ i j : ℕ, ∃ hi : i + 1 < n, ∃ hj : j + 1 < n,
      P.IsBottleneck σ i hi ∧ P.IsBottleneck σ j hj ∧
      (i + 2 ≤ j ∨ j + 2 ≤ i) := by
  -- S = the set of active bottleneck positions
  set S := (Finset.range (n - 1)).filter (fun i ↦
    ∃ hi : i + 1 < n, P.IsBottleneck σ i hi) with hS_def
  -- S.card ≥ 3
  have hS_card : S.card ≥ 3 := hS
  -- S is nonempty
  have hS_ne : S.Nonempty := Finset.card_pos.mp (by omega)
  -- Extract min and max
  set imin := S.min' hS_ne
  set imax := S.max' hS_ne
  -- Both are members of S
  have hmin_mem : imin ∈ S := Finset.min'_mem S hS_ne
  have hmax_mem : imax ∈ S := Finset.max'_mem S hS_ne
  -- Gap: imax - imin ≥ 2 via subset of Icc
  have h_sub : S ⊆ Finset.Icc imin imax := by
    intro x hx
    rw [Finset.mem_Icc]
    exact ⟨Finset.min'_le S x hx, Finset.le_max' S x hx⟩
  have h_card_Icc := Finset.card_le_card h_sub
  simp at h_card_Icc
  -- h_card_Icc should now be: S.card ≤ imax + 1 - imin
  have h_gap : imax ≥ imin + 2 := by omega
  -- Extract bottleneck proofs from S membership
  have hmin_S := Finset.mem_filter.mp hmin_mem
  have hmax_S := Finset.mem_filter.mp hmax_mem
  obtain ⟨hi_min, hbot_min⟩ := hmin_S.2
  obtain ⟨hi_max, hbot_max⟩ := hmax_S.2
  exact ⟨imin, imax, hi_min, hi_max, hbot_min, hbot_max, Or.inl h_gap⟩

/-- Swapping an adjacent incomparable pair in a linear extension
    gives another linear extension. -/
lemma bottleneck_swap_linext (P : FinPoset n) (σ : Perm (Fin n))
    (hσ : P.IsLinExt σ) (i : ℕ) (hi : i + 1 < n)
    (hbot : P.IsBottleneck σ i hi) :
    σ * Equiv.swap ⟨i, by omega⟩ ⟨i + 1, hi⟩ ∈ P.linExts := by
  simp only [FinPoset.linExts, Finset.mem_filter, Finset.mem_univ, true_and]
  intro a b hab
  set sw := Equiv.swap (⟨i, by omega⟩ : Fin n) ⟨i + 1, hi⟩
  set pa := σ.symm a
  set pb := σ.symm b
  have h_ord : pa.val ≤ pb.val := hσ a b hab
  -- (σ * sw).symm x = sw (σ.symm x)
  have hsw_inv : sw.symm = sw := Equiv.symm_swap _ _
  have hsymm : ∀ x, (σ * sw).symm x = sw (σ.symm x) := by
    intro x; simp [Equiv.Perm.mul_def, Equiv.symm_trans_apply, hsw_inv]
  rw [hsymm, hsymm]
  change (sw pa).val ≤ (sw pb).val
  by_cases hpa_i : pa = ⟨i, by omega⟩
  · by_cases hpb_i1 : pb = ⟨i + 1, hi⟩
    · -- pa=⟨i,_⟩, pb=⟨i+1,_⟩ → a = σ(i), b = σ(i+1) are incomparable
      exfalso
      have ha : a = σ ⟨i, by omega⟩ := by
        have := σ.apply_symm_apply a; rw [show σ.symm a = pa from rfl, hpa_i] at this
        exact this.symm
      have hb : b = σ ⟨i + 1, hi⟩ := by
        have := σ.apply_symm_apply b; rw [show σ.symm b = pb from rfl, hpb_i1] at this
        exact this.symm
      exact hbot.1 (ha ▸ hb ▸ hab)
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

/-- Disjoint bottleneck swaps compose to a valid extension.
    Uses commutativity of disjoint transpositions + bottleneck_swap_linext.
    (Condensed from 141 lines via dual Stone analysis — Feature II-B.) -/
lemma disjoint_swap_valid (P : FinPoset n) (σ : Perm (Fin n))
    (hσ : P.IsLinExt σ)
    (i j : ℕ) (hi : i + 1 < n) (hj : j + 1 < n)
    (hdisj : i + 2 ≤ j ∨ j + 2 ≤ i)
    (hboti : P.IsBottleneck σ i hi)
    (hbotj : P.IsBottleneck σ j hj) :
    σ * Equiv.swap ⟨i, by omega⟩ ⟨i + 1, hi⟩ *
        Equiv.swap ⟨j, by omega⟩ ⟨j + 1, hj⟩ ∈ P.linExts := by
  set si := Equiv.swap (⟨i, by omega⟩ : Fin n) ⟨i + 1, hi⟩
  set sj := Equiv.swap (⟨j, by omega⟩ : Fin n) ⟨j + 1, hj⟩
  -- Disjoint transpositions commute: σ*si*sj = σ*sj*si
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
  rw [show σ * si * sj = σ * sj * si by rw [mul_assoc, mul_assoc, h_disj.commute.eq]]
  -- sj fixes positions i, i+1 (disjoint indices)
  have hsj_fix_i : sj (⟨i, by omega⟩ : Fin n) = ⟨i, by omega⟩ := by
    simp only [sj, Equiv.swap_apply_def, Fin.mk.injEq]; split <;> [omega; split <;> [omega; rfl]]
  have hsj_fix_i1 : sj (⟨i + 1, hi⟩ : Fin n) = ⟨i + 1, hi⟩ := by
    simp only [sj, Equiv.swap_apply_def, Fin.mk.injEq]; split <;> [omega; split <;> [omega; rfl]]
  -- σ*sj is a linext (bottleneck_swap_linext at j)
  have hσj := bottleneck_swap_linext P σ hσ j hj hbotj
  have hσj_le : P.IsLinExt (σ * sj) := by
    simp only [FinPoset.linExts, Finset.mem_filter, Finset.mem_univ, true_and] at hσj; exact hσj
  -- (σ*sj) has the same incomparable pair at position i (since sj fixes i, i+1)
  have hbot' : P.IsBottleneck (σ * sj) i hi := by
    show P.Incomp ((σ * sj) ⟨i, by omega⟩) ((σ * sj) ⟨i + 1, hi⟩)
    simp only [Equiv.Perm.mul_apply, hsj_fix_i, hsj_fix_i1]; exact hboti
  -- Apply bottleneck_swap_linext at position i on (σ*sj)
  exact bottleneck_swap_linext P (σ * sj) hσj_le i hi hbot'

-- ═════════════════════════════════════════════════════════════════
-- §9½. SINGLE-SWAP AND DOUBLE-SWAP M_i MEMBERSHIP
--      For |S| ≥ 4: the smallest bottleneck has |M_a| ≥ 3,
--      giving k > 9 under AllSkewed (closes k ≤ 9 outright).
-- ═════════════════════════════════════════════════════════════════

/-- A single swap at bottleneck i puts σ*swap(i,i+1) into M_i. -/
lemma single_swap_in_M (P : FinPoset n) (σ : Perm (Fin n))
    (hσ : P.IsLinExt σ)
    (i : ℕ) (hi : i + 1 < n) (hbot : P.IsBottleneck σ i hi) :
    σ * Equiv.swap ⟨i, by omega⟩ ⟨i + 1, hi⟩ ∈ P.M σ i hi := by
  set sw := Equiv.swap (⟨i, by omega⟩ : Fin n) ⟨i + 1, hi⟩
  simp only [FinPoset.M, Finset.mem_filter]
  constructor
  · exact bottleneck_swap_linext P σ hσ i hi hbot
  · -- (σ*sw)⁻¹(σ(i+1)).val < (σ*sw)⁻¹(σ(i)).val
    -- (σ*sw)⁻¹ = sw⁻¹ * σ⁻¹ = sw * σ⁻¹
    have hsw_inv : sw.symm = sw := Equiv.symm_swap _ _
    -- (σ*sw)⁻¹(σ(i+1)) = sw(σ⁻¹(σ(i+1))) = sw(⟨i+1,_⟩) = ⟨i,_⟩
    have h1 : (σ * sw).symm (σ ⟨i + 1, hi⟩) = ⟨i, by omega⟩ := by
      simp [Equiv.Perm.mul_def, Equiv.symm_trans_apply, hsw_inv,
            σ.symm_apply_apply, sw, Equiv.swap_apply_right]
    -- (σ*sw)⁻¹(σ(i)) = sw(σ⁻¹(σ(i))) = sw(⟨i,_⟩) = ⟨i+1,_⟩
    have h2 : (σ * sw).symm (σ ⟨i, by omega⟩) = ⟨i + 1, hi⟩ := by
      simp [Equiv.Perm.mul_def, Equiv.symm_trans_apply, hsw_inv,
            σ.symm_apply_apply, sw, Equiv.swap_apply_left]
    rw [h1, h2]; simp

/-- A double swap σ*swap_i*swap_j at disjoint bottlenecks i,j lands in M_i. -/
lemma double_swap_in_M (P : FinPoset n) (σ : Perm (Fin n))
    (hσ : P.IsLinExt σ)
    (i j : ℕ) (hi : i + 1 < n) (hj : j + 1 < n)
    (hboti : P.IsBottleneck σ i hi) (hbotj : P.IsBottleneck σ j hj)
    (hdisj : i + 2 ≤ j ∨ j + 2 ≤ i) :
    σ * Equiv.swap ⟨i, by omega⟩ ⟨i + 1, hi⟩ *
        Equiv.swap ⟨j, by omega⟩ ⟨j + 1, hj⟩ ∈ P.M σ i hi := by
  set si := Equiv.swap (⟨i, by omega⟩ : Fin n) ⟨i + 1, hi⟩
  set sj := Equiv.swap (⟨j, by omega⟩ : Fin n) ⟨j + 1, hj⟩
  simp only [FinPoset.M, Finset.mem_filter]
  constructor
  · exact disjoint_swap_valid P σ hσ i j hi hj hdisj hboti hbotj
  · -- (σ*si*sj)⁻¹ = sj*si*σ⁻¹. On σ(i+1): sj*si*σ⁻¹(σ(i+1)) = sj*si(⟨i+1,_⟩) = sj(⟨i,_⟩)
    -- Since |i-j| ≥ 2: sj fixes ⟨i,_⟩. So result = ⟨i,_⟩.
    -- On σ(i): sj*si*σ⁻¹(σ(i)) = sj*si(⟨i,_⟩) = sj(⟨i+1,_⟩). sj fixes ⟨i+1,_⟩. Result = ⟨i+1,_⟩.
    have hsi_inv : si.symm = si := Equiv.symm_swap _ _
    have hsj_inv : sj.symm = sj := Equiv.symm_swap _ _
    have hsj_fix_i : sj (⟨i, by omega⟩ : Fin n) = ⟨i, by omega⟩ := by
      simp only [sj, Equiv.swap_apply_def, Fin.mk.injEq]; split <;> [omega; split <;> [omega; rfl]]
    have hsj_fix_i1 : sj (⟨i + 1, hi⟩ : Fin n) = ⟨i + 1, hi⟩ := by
      simp only [sj, Equiv.swap_apply_def, Fin.mk.injEq]; split <;> [omega; split <;> [omega; rfl]]
    have h1 : (σ * si * sj).symm (σ ⟨i + 1, hi⟩) = ⟨i, by omega⟩ := by
      simp [Equiv.Perm.mul_def, Equiv.symm_trans_apply, hsi_inv, hsj_inv,
            σ.symm_apply_apply, si, Equiv.swap_apply_right, hsj_fix_i]
    have h2 : (σ * si * sj).symm (σ ⟨i, by omega⟩) = ⟨i + 1, hi⟩ := by
      simp [Equiv.Perm.mul_def, Equiv.symm_trans_apply, hsi_inv, hsj_inv,
            σ.symm_apply_apply, si, Equiv.swap_apply_left, hsj_fix_i1]
    rw [h1, h2]; simp

/-- The single swap and double swap produce distinct elements:
    τ_a = σ*swap_a differs from τ_{a,c} = σ*swap_a*swap_c at position c. -/
lemma single_ne_double (P : FinPoset n) (σ : Perm (Fin n))
    (hσ_inj : Function.Injective σ)
    (i j : ℕ) (hi : i + 1 < n) (hj : j + 1 < n)
    (hdisj : i + 2 ≤ j ∨ j + 2 ≤ i) :
    σ * Equiv.swap ⟨i, by omega⟩ ⟨i + 1, hi⟩ ≠
    σ * Equiv.swap ⟨i, by omega⟩ ⟨i + 1, hi⟩ *
        Equiv.swap ⟨j, by omega⟩ ⟨j + 1, hj⟩ := by
  intro h
  -- Apply both sides to ⟨j,_⟩
  have := congr_fun (congr_arg (↑·) h) ⟨j, by omega⟩
  simp only [Equiv.Perm.mul_apply] at this
  -- LHS: (σ*si)(j) = σ(si(j)). Since |i-j| ≥ 2, si fixes j. So = σ(j).
  -- RHS: (σ*si*sj)(j) = σ(si(sj(j))) = σ(si(j+1)). Since |i-(j+1)| ≥ 1 and |(i+1)-(j+1)| ≥ 1, si fixes j+1. So = σ(j+1).
  -- σ(j) = σ(j+1) contradicts injectivity.
  set si := Equiv.swap (⟨i, by omega⟩ : Fin n) ⟨i + 1, hi⟩
  set sj := Equiv.swap (⟨j, by omega⟩ : Fin n) ⟨j + 1, hj⟩
  have hsi_fix_j : si ⟨j, by omega⟩ = ⟨j, by omega⟩ := by
    simp only [si, Equiv.swap_apply_def, Fin.mk.injEq]; split <;> [omega; split <;> [omega; rfl]]
  have hsi_fix_j1 : si ⟨j + 1, hj⟩ = ⟨j + 1, hj⟩ := by
    simp only [si, Equiv.swap_apply_def, Fin.mk.injEq]; split <;> [omega; split <;> [omega; rfl]]
  have hsj_j : sj ⟨j, by omega⟩ = ⟨j + 1, hj⟩ := by simp [sj]
  change σ (si ⟨j, by omega⟩) = σ (si (sj ⟨j, by omega⟩)) at this
  rw [hsi_fix_j, hsj_j, hsi_fix_j1] at this
  have heq := hσ_inj this
  simp [Fin.ext_iff] at heq

/-- Two double swaps with different second partners are distinct. -/
lemma double_ne_double (P : FinPoset n) (σ : Perm (Fin n))
    (hσ_inj : Function.Injective σ)
    (i j₁ j₂ : ℕ) (hi : i + 1 < n) (hj₁ : j₁ + 1 < n) (hj₂ : j₂ + 1 < n)
    (hdisj₁ : i + 2 ≤ j₁ ∨ j₁ + 2 ≤ i)
    (hdisj₂ : i + 2 ≤ j₂ ∨ j₂ + 2 ≤ i)
    (hne : j₁ ≠ j₂)
    (hdisj₁₂ : j₁ + 2 ≤ j₂ ∨ j₂ + 2 ≤ j₁ ∨ j₁ + 1 = j₂ ∨ j₂ + 1 = j₁) :
    σ * Equiv.swap ⟨i, by omega⟩ ⟨i + 1, hi⟩ *
        Equiv.swap ⟨j₁, by omega⟩ ⟨j₁ + 1, hj₁⟩ ≠
    σ * Equiv.swap ⟨i, by omega⟩ ⟨i + 1, hi⟩ *
        Equiv.swap ⟨j₂, by omega⟩ ⟨j₂ + 1, hj₂⟩ := by
  intro h
  -- Cancel the common left factor σ * swap_i
  have h_sj := mul_left_cancel h
  -- h_sj : swap(j₁,j₁+1) = swap(j₂,j₂+1). Evaluate at ⟨j₁,_⟩.
  have h_app := congr_fun (congr_arg (↑·) h_sj) ⟨j₁, by omega⟩
  simp only [Equiv.swap_apply_left] at h_app
  -- h_app : ⟨j₁+1,_⟩ = swap(j₂,j₂+1)(⟨j₁,_⟩)
  simp only [Equiv.swap_apply_def] at h_app
  split_ifs at h_app with h1 h2
  · -- j₁ = j₂ (as Fin n) → contradicts hne
    exact hne (Fin.ext_iff.mp h1)
  · -- j₁ = j₂+1, h_app : ⟨j₁+1,_⟩ = ⟨j₂,_⟩
    simp [Fin.ext_iff] at h_app h2; omega
  · -- j₁ ∉ {j₂, j₂+1}, h_app : ⟨j₁+1,_⟩ = ⟨j₁,_⟩
    simp [Fin.ext_iff] at h_app

/-- For |S| ≥ 4 bottleneck positions, the smallest bottleneck a has |M_a| ≥ 3.
    Proof: among S\{a}, at least 2 have gap ≥ 2 from a. Single swap + 2 double
    swaps give 3 distinct elements of M_a. -/
lemma three_in_M_of_four_bottlenecks (P : FinPoset n) (σ : Perm (Fin n))
    (hσ : P.Dominant σ) (hk : P.k ≥ 4)
    (hS4 : P.bottleneckCount σ ≥ 4) :
    ∃ (i : ℕ) (hi : i + 1 < n),
      P.IsBottleneck σ i hi ∧ (P.M σ i hi).card ≥ 3 := by
  set S := (Finset.range (n - 1)).filter (fun i ↦
    ∃ hi : i + 1 < n, P.IsBottleneck σ i hi) with hS_def
  have hS_card : S.card ≥ 4 := hS4
  have hS_ne : S.Nonempty := Finset.card_pos.mp (by omega)
  -- a = min(S)
  set a := S.min' hS_ne
  have ha_mem : a ∈ S := Finset.min'_mem S hS_ne
  obtain ⟨ha, hbot_a⟩ := (Finset.mem_filter.mp ha_mem).2
  -- S' = S \ {a}, |S'| ≥ 3
  set S' := S.erase a
  have hS'_card : S'.card ≥ 3 := by
    rw [Finset.card_erase_of_mem ha_mem]; omega
  -- Every element of S' is > a (since a = min)
  have h_gt_a : ∀ x ∈ S', x > a := by
    intro x hx
    have hx_mem := Finset.erase_subset a S hx
    have hx_ne : x ≠ a := Finset.ne_of_mem_erase hx
    exact lt_of_le_of_ne (Finset.min'_le S x hx_mem) (Ne.symm hx_ne)
  -- At most 1 element of S' has x = a+1 (gap 1). Rest have gap ≥ 2.
  -- S'' = {x ∈ S' | x ≥ a+2}, |S''| ≥ 2
  set S'' := S'.filter (fun x ↦ x ≥ a + 2)
  have hS''_card : S''.card ≥ 2 := by
    -- S' \ S'' has at most 1 element (only a+1 satisfies a < x < a+2)
    have h_sub : S'' ⊆ S' := Finset.filter_subset _ S'
    have h_decomp := Finset.card_sdiff_add_card_eq_card h_sub
    -- h_decomp : (S' \ S'').card + S''.card = S'.card
    suffices h_compl : (S' \ S'').card ≤ 1 by omega
    apply Finset.card_le_one.mpr
    intro x hx y hy
    have hx_mem := (Finset.mem_sdiff.mp hx).1
    have hx_nmem := (Finset.mem_sdiff.mp hx).2
    have hy_mem := (Finset.mem_sdiff.mp hy).1
    have hy_nmem := (Finset.mem_sdiff.mp hy).2
    have hx_gt := h_gt_a x hx_mem
    have hy_gt := h_gt_a y hy_mem
    have hx_lt : ¬(x ≥ a + 2) := fun h => hx_nmem (Finset.mem_filter.mpr ⟨hx_mem, h⟩)
    have hy_lt : ¬(y ≥ a + 2) := fun h => hy_nmem (Finset.mem_filter.mpr ⟨hy_mem, h⟩)
    omega
  -- Pick c₁, c₂ ∈ S'' (distinct)
  have hS''_ne : S''.Nonempty := Finset.card_pos.mp (by omega)
  -- Pick c₁ = min(S''), c₂ = max(S'') or second element
  -- Actually, just pick any two distinct elements
  have hS''_two : 1 < S''.card := by omega
  obtain ⟨c₁, hc₁_mem, c₂, hc₂_mem, hc_ne⟩ := Finset.one_lt_card.mp hS''_two
  -- c₁, c₂ ∈ S'', c₁ ≠ c₂
  have hc₁_ge : c₁ ≥ a + 2 := by
    have := (Finset.mem_filter.mp hc₁_mem).2; exact this
  have hc₂_ge : c₂ ≥ a + 2 := by
    have := (Finset.mem_filter.mp hc₂_mem).2; exact this
  -- c₁, c₂ are bottleneck positions
  have hc₁_S : c₁ ∈ S := Finset.mem_of_mem_erase ((Finset.mem_filter.mp hc₁_mem).1)
  have hc₂_S : c₂ ∈ S := Finset.mem_of_mem_erase ((Finset.mem_filter.mp hc₂_mem).1)
  obtain ⟨hc₁, hbot_c₁⟩ := (Finset.mem_filter.mp hc₁_S).2
  obtain ⟨hc₂, hbot_c₂⟩ := (Finset.mem_filter.mp hc₂_S).2
  -- Disjointness: |a - c₁| ≥ 2 and |a - c₂| ≥ 2
  have hdisj₁ : a + 2 ≤ c₁ ∨ c₁ + 2 ≤ a := Or.inl hc₁_ge
  have hdisj₂ : a + 2 ≤ c₂ ∨ c₂ + 2 ≤ a := Or.inl hc₂_ge
  -- Construct 3 distinct elements of M_a
  set τ₀ := σ * Equiv.swap ⟨a, by omega⟩ ⟨a + 1, ha⟩
  set τ₁ := σ * Equiv.swap ⟨a, by omega⟩ ⟨a + 1, ha⟩ *
      Equiv.swap ⟨c₁, by omega⟩ ⟨c₁ + 1, hc₁⟩
  set τ₂ := σ * Equiv.swap ⟨a, by omega⟩ ⟨a + 1, ha⟩ *
      Equiv.swap ⟨c₂, by omega⟩ ⟨c₂ + 1, hc₂⟩
  have hσ_le := hσ.1
  have hτ₀_M : τ₀ ∈ P.M σ a ha := single_swap_in_M P σ hσ_le a ha hbot_a
  have hτ₁_M : τ₁ ∈ P.M σ a ha := double_swap_in_M P σ hσ_le a c₁ ha hc₁ hbot_a hbot_c₁ hdisj₁
  have hτ₂_M : τ₂ ∈ P.M σ a ha := double_swap_in_M P σ hσ_le a c₂ ha hc₂ hbot_a hbot_c₂ hdisj₂
  -- All 3 are distinct
  have h01 : τ₀ ≠ τ₁ := single_ne_double P σ σ.injective a c₁ ha hc₁ hdisj₁
  have h02 : τ₀ ≠ τ₂ := single_ne_double P σ σ.injective a c₂ ha hc₂ hdisj₂
  have h12 : τ₁ ≠ τ₂ := by
    -- c₁ ≠ c₂, both ≥ a+2. Need |c₁ - c₂| ≥ 1 but they could be adjacent.
    -- Use double_ne_double (handles all cases)
    exact double_ne_double P σ σ.injective a c₁ c₂ ha hc₁ hc₂ hdisj₁ hdisj₂ hc_ne
      (by omega)
  -- {τ₀, τ₁, τ₂} ⊆ M_a, all distinct → |M_a| ≥ 3
  exact ⟨a, ha, hbot_a, Finset.two_lt_card.mpr
    ⟨τ₀, hτ₀_M, τ₁, hτ₁_M, τ₂, hτ₂_M, h01, h02, h12⟩⟩

/-- Under AllSkewed with |S| ≥ 4, k > 9. Contrapositive: k ≤ 9 → False. -/
lemma small_k_absurd (P : FinPoset n) (σ : Perm (Fin n))
    (hσ : P.Dominant σ) (hk : P.k ≥ 4)
    (hskew : P.AllSkewed)
    (hS4 : P.bottleneckCount σ ≥ 4)
    (hk_small : P.k ≤ 9) : False := by
  obtain ⟨i, hi, hbot, hMi_ge3⟩ := three_in_M_of_four_bottlenecks P σ hσ hk hS4
  have h_skew := hskew _ _ hbot
  have h_eq := bottleneck_minority_eq P σ hσ i hi hbot
  -- h_skew : 3 * P.minority ... < k
  -- h_eq : (P.M σ i hi).card = P.minority ...
  -- hMi_ge3 : (P.M σ i hi).card ≥ 3
  -- So: P.minority ≥ 3, hence 9 ≤ 3*3 ≤ 3*minority < k ≤ 9.
  omega

/-- |S| = 3: the Star Graph (Ω = 0) is impossible.
    AllSkewed forces Ω ≤ 0, but commutativity forces Ω ≥ 1. -/
lemma star_graph_shattered (P : FinPoset n) (σ : Perm (Fin n))
    (hσ : P.Dominant σ) (hk : P.k ≥ 4)
    (hskew : P.AllSkewed)
    (hS : P.bottleneckCount σ ≥ 3)
    (hS_le : P.bottleneckCount σ ≤ 3) :
    False := by
  -- Step 1: Extract disjoint bottleneck positions i, j
  obtain ⟨i, j, hi, hj, hbot_i, hbot_j, hdisj⟩ := exists_disjoint_bottlenecks P σ hS
  -- Step 2+3: Composed swap gives valid extension (via Feature II-B)
  have hcomp := disjoint_swap_valid P σ hσ.1 i j hi hj hdisj hbot_i hbot_j
  -- Step 4: Show τ = σ * swap_i * swap_j reverses pairs at both i and j
  set si := Equiv.swap (⟨i, by omega⟩ : Fin n) ⟨i + 1, hi⟩
  set sj := Equiv.swap (⟨j, by omega⟩ : Fin n) ⟨j + 1, hj⟩
  set τ := σ * si * sj
  -- Disjointness facts for swap application
  have h_ne_ij : (⟨i, by omega⟩ : Fin n) ≠ ⟨j, by omega⟩ := by simp [Fin.ext_iff]; omega
  have h_ne_ij1 : (⟨i, by omega⟩ : Fin n) ≠ ⟨j + 1, hj⟩ := by simp [Fin.ext_iff]; omega
  have h_ne_i1j : (⟨i + 1, hi⟩ : Fin n) ≠ ⟨j, by omega⟩ := by simp [Fin.ext_iff]; omega
  have h_ne_i1j1 : (⟨i + 1, hi⟩ : Fin n) ≠ ⟨j + 1, hj⟩ := by simp [Fin.ext_iff]; omega
  -- τ.symm decomposition
  have hsi_inv : si.symm = si := Equiv.symm_swap _ _
  have hsj_inv : sj.symm = sj := Equiv.symm_swap _ _
  have hτ_symm : ∀ x, τ.symm x = sj (si (σ.symm x)) := by
    intro x; simp only [τ, Equiv.Perm.mul_def, Equiv.symm_trans_apply, hsi_inv, hsj_inv]
  -- τ.symm(σ(i)) = ⟨i+1,_⟩ and τ.symm(σ(i+1)) = ⟨i,_⟩
  have hτ_inv_i : τ.symm (σ ⟨i, by omega⟩) = ⟨i + 1, hi⟩ := by
    rw [hτ_symm]; simp [σ.symm_apply_apply, si, Equiv.swap_apply_left]
    exact Equiv.swap_apply_of_ne_of_ne h_ne_i1j h_ne_i1j1
  have hτ_inv_i1 : τ.symm (σ ⟨i + 1, hi⟩) = ⟨i, by omega⟩ := by
    rw [hτ_symm]; simp [σ.symm_apply_apply, si, Equiv.swap_apply_right]
    exact Equiv.swap_apply_of_ne_of_ne h_ne_ij h_ne_ij1
  -- τ ∈ M_i
  have hτ_Mi : τ ∈ P.M σ i hi := by
    simp only [FinPoset.M, Finset.mem_filter]
    exact ⟨hcomp, by rw [hτ_inv_i1, hτ_inv_i]; simp only [Fin.val_mk]; omega⟩
  -- τ.symm(σ(j)) = ⟨j+1,_⟩ and τ.symm(σ(j+1)) = ⟨j,_⟩
  have hτ_inv_j : τ.symm (σ ⟨j, by omega⟩) = ⟨j + 1, hj⟩ := by
    rw [hτ_symm]; simp [σ.symm_apply_apply]
    rw [show si ⟨j, by omega⟩ = ⟨j, by omega⟩ from
      Equiv.swap_apply_of_ne_of_ne h_ne_ij.symm h_ne_i1j.symm]
    show sj ⟨j, by omega⟩ = ⟨j + 1, hj⟩; simp [sj]
  have hτ_inv_j1 : τ.symm (σ ⟨j + 1, hj⟩) = ⟨j, by omega⟩ := by
    rw [hτ_symm]; simp [σ.symm_apply_apply]
    rw [show si ⟨j + 1, hj⟩ = ⟨j + 1, hj⟩ from
      Equiv.swap_apply_of_ne_of_ne h_ne_ij1.symm h_ne_i1j1.symm]
    show sj ⟨j + 1, hj⟩ = ⟨j, by omega⟩; simp [sj]
  -- τ ∈ M_j
  have hτ_Mj : τ ∈ P.M σ j hj := by
    simp only [FinPoset.M, Finset.mem_filter]
    exact ⟨hcomp, by rw [hτ_inv_j1, hτ_inv_j]; simp only [Fin.val_mk]; omega⟩
  -- Step 5: Coverage and counting (same pattern as pigeonhole_two_bottlenecks)
  have hσ_mem : σ ∈ P.linExts := by
    simp only [FinPoset.linExts, Finset.mem_filter, Finset.mem_univ, true_and]; exact hσ.1
  set S := (Finset.range (n - 1)).filter (fun l ↦
    ∃ hl : l + 1 < n, P.IsBottleneck σ l hl) with hS_def
  set f := fun l ↦ if h : l + 1 < n then P.M σ l h else ∅
  set U := S.biUnion f with hU_def
  have h_cover : P.linExts.erase σ ⊆ U := by
    intro τ' hτ'; rw [Finset.mem_erase] at hτ'
    have hτ'_le : P.IsLinExt τ' := by
      simp only [FinPoset.linExts, Finset.mem_filter, Finset.mem_univ, true_and] at hτ'; exact hτ'.2
    obtain ⟨l, hl, hbot_l, hτ'_in⟩ := bottleneck_coverage P σ hσ τ' hτ'_le hτ'.1
    simp only [hU_def, Finset.mem_biUnion]
    refine ⟨l, ?_, ?_⟩
    · simp only [hS_def, Finset.mem_filter, Finset.mem_range]; exact ⟨by omega, hl, hbot_l⟩
    · simp only [f, dif_pos hl]; exact hτ'_in
  have h_k_le_U : P.k - 1 ≤ U.card :=
    (Finset.card_erase_of_mem hσ_mem) ▸ Finset.card_le_card h_cover
  -- Each |f(l)| ≤ (k-1)/3
  have h_each : ∀ l ∈ S, (f l).card ≤ (P.k - 1) / 3 := by
    intro l hl_S
    have hl : l + 1 < n := by
      have := (Finset.mem_filter.mp hl_S).1; rw [Finset.mem_range] at this; omega
    simp only [f, dif_pos hl]
    obtain ⟨hl', hbot_l⟩ := (Finset.mem_filter.mp hl_S).2
    have hbot_l' : P.IsBottleneck σ l hl := by convert hbot_l
    rw [bottleneck_minority_eq P σ hσ l hl hbot_l']
    have := hskew _ _ hbot_l'; unfold FinPoset.minority at this ⊢; omega
  have h_sum_le := Finset.sum_le_card_nsmul S (fun l ↦ (f l).card) _ h_each
  simp only [smul_eq_mul] at h_sum_le
  -- 3 × ⌊(k-1)/3⌋ ≤ k-1 (tight when k ≡ 1 mod 3, slack otherwise)
  have h_div : (P.k - 1) / 3 * 3 ≤ P.k - 1 := Nat.div_mul_le_self _ _
  have hS_eq : S.card = 3 := by
    have : S.card = P.bottleneckCount σ := rfl; omega
  -- |f(i) ∩ f(j)| ≥ 1
  have hτ_fi : τ ∈ f i := by simp only [f, dif_pos hi]; exact hτ_Mi
  have hτ_fj : τ ∈ f j := by simp only [f, dif_pos hj]; exact hτ_Mj
  have h_inter_ge : (f i ∩ f j).card ≥ 1 :=
    Finset.card_pos.mpr ⟨τ, Finset.mem_inter.mpr ⟨hτ_fi, hτ_fj⟩⟩
  -- |f(i) ∪ f(j)| = |f(i)| + |f(j)| - |f(i) ∩ f(j)|
  have h_union_inter := Finset.card_union_add_card_inter (f i) (f j)
  -- S membership
  have hi_S : i ∈ S := by
    simp only [hS_def, Finset.mem_filter, Finset.mem_range]; exact ⟨by omega, hi, hbot_i⟩
  have hj_S : j ∈ S := by
    simp only [hS_def, Finset.mem_filter, Finset.mem_range]; exact ⟨by omega, hj, hbot_j⟩
  have h_ij_ne : i ≠ j := by omega
  -- Decompose U ⊆ (f i ∪ f j) ∪ rest
  have h_U_sub : U ⊆ (f i ∪ f j) ∪ ((S.erase j).erase i).biUnion f := by
    intro x hx; simp only [hU_def, Finset.mem_biUnion] at hx
    obtain ⟨l, hl_S, hx_fl⟩ := hx
    simp only [Finset.mem_union, Finset.mem_biUnion]
    by_cases hli : l = i
    · left; left; rw [← hli]; exact hx_fl
    · by_cases hlj : l = j
      · left; right; rw [← hlj]; exact hx_fl
      · right; exact ⟨l, Finset.mem_erase.mpr ⟨hli, Finset.mem_erase.mpr ⟨hlj, hl_S⟩⟩, hx_fl⟩
  -- |rest| bound
  have h_rest_card : ((S.erase j).erase i).card ≤ 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨h_ij_ne, hi_S⟩),
        Finset.card_erase_of_mem hj_S]; omega
  have h_rest_sum : ((S.erase j).erase i).sum (fun l ↦ (f l).card) ≤ (P.k - 1) / 3 := by
    calc ((S.erase j).erase i).sum _ ≤ ((S.erase j).erase i).card * ((P.k - 1) / 3) := by
          apply Finset.sum_le_card_nsmul; intro l hl
          exact h_each l (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hl))
      _ ≤ 1 * ((P.k - 1) / 3) := Nat.mul_le_mul_right _ h_rest_card
      _ = _ := one_mul _
  -- f(i), f(j) bounds
  have h_fi_le : (f i).card ≤ (P.k - 1) / 3 := h_each i hi_S
  have h_fj_le : (f j).card ≤ (P.k - 1) / 3 := h_each j hj_S
  -- Combine: |U| ≤ |f(i) ∪ f(j)| + rest ≤ (f(i) + f(j) - 1) + (k-1)/3 ≤ k-2
  have h_ub : U.card ≤ P.k - 2 := by
    calc U.card
        ≤ ((f i ∪ f j) ∪ ((S.erase j).erase i).biUnion f).card := Finset.card_le_card h_U_sub
      _ ≤ (f i ∪ f j).card + (((S.erase j).erase i).biUnion f).card := Finset.card_union_le _ _
      _ ≤ (f i ∪ f j).card + ((S.erase j).erase i).sum (fun l ↦ (f l).card) := by
          exact Nat.add_le_add_left Finset.card_biUnion_le _
      _ ≤ (f i ∪ f j).card + (P.k - 1) / 3 := Nat.add_le_add_left h_rest_sum _
      _ = ((f i).card + (f j).card - (f i ∩ f j).card) + (P.k - 1) / 3 := by omega
      _ ≤ ((P.k - 1) / 3 + (P.k - 1) / 3 - 1) + (P.k - 1) / 3 := by omega
      _ = 3 * ((P.k - 1) / 3) - 1 := by omega
      _ ≤ P.k - 1 - 1 := by omega
      _ = P.k - 2 := by omega
  -- k-1 ≤ U.card ≤ k-2: contradiction
  omega

-- ═════════════════════════════════════════════════════════════════
-- §10. LEMMA 5 — Geometric Collapse (Phase 6)
--      |S| ≥ 4 forces zero adjacent overlap, which creates two
--      parallel chains. The chain interleaving has |M₁|/k ≥ 2/5.
-- ═════════════════════════════════════════════════════════════════

/-- Adjacent overlap veto: if |M_i ∩ M_{i+1}| = 0 for adjacent
    bottleneck positions i, i+1, then σ(i) <_P σ(i+2). -/
lemma adjacent_overlap_forces_relation (P : FinPoset n) (σ : Perm (Fin n))
    (hσ : P.IsLinExt σ)
    (i : ℕ) (hi2 : i + 2 < n)
    (hbot1 : P.IsBottleneck σ i (by omega))
    (hbot2 : P.IsBottleneck σ (i + 1) hi2)
    (hzero : (P.M σ i (by omega) ∩ P.M σ (i + 1) hi2).card = 0) :
    P.le (σ ⟨i, by omega⟩) (σ ⟨i + 2, hi2⟩) := by
  by_contra h_neg
  -- σ(i+2) ≤_P σ(i) is impossible since σ is linext and i < i+2
  have h_not_rev : ¬P.le (σ ⟨i + 2, hi2⟩) (σ ⟨i, by omega⟩) := by
    intro h_rev
    have := hσ _ _ h_rev
    simp [Equiv.symm_apply_apply] at this
  -- So σ(i) ∥ σ(i+2) (incomparable)
  have h_incomp_02 : P.Incomp (σ ⟨i, by omega⟩) (σ ⟨i + 2, hi2⟩) := ⟨h_neg, h_not_rev⟩
  -- Construct τ = σ * swap(⟨i,_⟩, ⟨i+2,_⟩)
  set sw := Equiv.swap (⟨i, by omega⟩ : Fin n) ⟨i + 2, hi2⟩
  set τ := σ * sw
  -- sw.symm = sw
  have hsw_inv : sw.symm = sw := Equiv.symm_swap _ _
  -- Key facts about sw
  have hsw_i : sw ⟨i, by omega⟩ = ⟨i + 2, hi2⟩ := by simp [sw]
  have hsw_i2 : sw ⟨i + 2, hi2⟩ = ⟨i, by omega⟩ := by simp [sw]
  have hsw_i1 : sw ⟨i + 1, by omega⟩ = ⟨i + 1, by omega⟩ := by
    simp only [sw, Equiv.swap_apply_def, Fin.mk.injEq]
    split
    · omega
    · split
      · omega
      · rfl
  -- τ is a linear extension
  have hτ_le : P.IsLinExt τ := by
    intro a b hab
    set pa := σ.symm a; set pb := σ.symm b
    have h_ord : pa.val ≤ pb.val := hσ a b hab
    have hτ_symm : ∀ x, τ.symm x = sw (σ.symm x) := by
      intro x; simp [τ, Equiv.Perm.mul_def, Equiv.symm_trans_apply, hsw_inv]
    rw [hτ_symm, hτ_symm]; change (sw pa).val ≤ (sw pb).val
    -- Case analysis: failing cases are (i,i+1), (i,i+2), (i+1,i+2)
    -- all excluded by incomparability
    -- Helper to recover a = σ(pa) from pa = σ.symm a
    have ha_eq : a = σ pa := (σ.apply_symm_apply a).symm
    have hb_eq : b = σ pb := (σ.apply_symm_apply b).symm
    by_cases hpa_i : pa = ⟨i, by omega⟩
    · by_cases hpb : pb = ⟨i + 1, by omega⟩
      · -- a = σ(i), b = σ(i+1): incomparable (hbot1)
        exfalso; exact hbot1.1 (by
          rwa [ha_eq.trans (congrArg σ hpa_i), hb_eq.trans (congrArg σ hpb)] at hab)
      · by_cases hpb2 : pb = ⟨i + 2, hi2⟩
        · -- a = σ(i), b = σ(i+2): incomparable
          exfalso; exact h_incomp_02.1 (by
            rwa [ha_eq.trans (congrArg σ hpa_i), hb_eq.trans (congrArg σ hpb2)] at hab)
        · by_cases hpb_i : pb = ⟨i, by omega⟩
          · rw [hpa_i, hpb_i]
          · rw [hpa_i, hsw_i]
            rw [Equiv.swap_apply_of_ne_of_ne hpb_i hpb2]
            have : pa.val = i := congr_arg Fin.val hpa_i
            have : pb.val ≠ i := fun h => hpb_i (Fin.ext h)
            have : pb.val ≠ i + 1 := fun h => hpb (Fin.ext h)
            have : pb.val ≠ i + 2 := fun h => hpb2 (Fin.ext h)
            simp only [Fin.val_mk]; omega
    · by_cases hpa_i2 : pa = ⟨i + 2, hi2⟩
      · -- pa = i+2, pb ≥ i+2. pb = i+2 → OK. pb = i: impossible (i+2 > i). pb = i+1: impossible.
        by_cases hpb_i : pb = ⟨i, by omega⟩
        · have : pa.val = i + 2 := congr_arg Fin.val hpa_i2
          have : pb.val = i := congr_arg Fin.val hpb_i; omega
        · by_cases hpb_i2 : pb = ⟨i + 2, hi2⟩
          · rw [hpa_i2, hpb_i2]
          · rw [hpa_i2, hsw_i2, Equiv.swap_apply_of_ne_of_ne hpb_i hpb_i2]
            have : pa.val = i + 2 := congr_arg Fin.val hpa_i2
            simp only [Fin.val_mk]; omega
      · -- pa ∉ {i, i+2}: sw fixes pa
        rw [Equiv.swap_apply_of_ne_of_ne hpa_i hpa_i2]
        by_cases hpb_i : pb = ⟨i, by omega⟩
        · rw [hpb_i, hsw_i]
          have : pb.val = i := congr_arg Fin.val hpb_i
          simp only [Fin.val_mk]; omega
        · by_cases hpb_i1 : pb = ⟨i + 1, by omega⟩
          · -- pa ∉ {i, i+2}, pb = i+1. sw fixes i+1.
            -- Check: pa = i+1 possible? pa ≤ pb = i+1.
            -- If pa = i+1 then pa = pb, both fixed by sw. ✓
            -- If pa < i+1 = i → pa < i. sw fixes pa.
            rw [hpb_i1, hsw_i1]
            have : pb.val = i + 1 := congr_arg Fin.val hpb_i1
            simp only [Fin.val_mk]; omega
          · by_cases hpb_i2 : pb = ⟨i + 2, hi2⟩
            · -- pa ∉ {i, i+2}, pb = i+2. Need: pa ≤ i.
              -- pa ≤ pb = i+2, pa ≠ i, pa ≠ i+2. Also check pa = i+1:
              -- If pa = i+1: hbot2 gives σ(i+1) ∥ σ(i+2), but a ≤_P b. a = σ(i+1), b = σ(i+2). Contradiction.
              by_cases hpa_i1 : pa = ⟨i + 1, by omega⟩
              · exfalso; exact hbot2.1 (by
                  rwa [ha_eq.trans (congrArg σ hpa_i1), hb_eq.trans (congrArg σ hpb_i2)] at hab)
              · rw [hpb_i2, hsw_i2]
                have : pa.val ≠ i := fun h => hpa_i (Fin.ext h)
                have : pa.val ≠ i + 1 := fun h => hpa_i1 (Fin.ext h)
                have : pa.val ≠ i + 2 := fun h => hpa_i2 (Fin.ext h)
                have : pb.val = i + 2 := congr_arg Fin.val hpb_i2
                simp only [Fin.val_mk]; omega
            · rw [Equiv.swap_apply_of_ne_of_ne hpb_i hpb_i2]; exact h_ord
  -- τ ∈ linExts
  have hτ_mem : τ ∈ P.linExts := by
    simp only [FinPoset.linExts, Finset.mem_filter, Finset.mem_univ, true_and]; exact hτ_le
  -- τ ∈ M_i: τ.symm(σ(i+1)).val < τ.symm(σ(i)).val
  have hτ_Mi : τ ∈ P.M σ i (by omega) := by
    simp only [FinPoset.M, Finset.mem_filter]
    constructor
    · exact hτ_mem
    · -- τ.symm(σ(i+1)) = sw(⟨i+1,_⟩) = ⟨i+1,_⟩
      -- τ.symm(σ(i))   = sw(⟨i,_⟩)   = ⟨i+2,_⟩
      simp only [τ, Equiv.Perm.mul_def, Equiv.symm_trans_apply, hsw_inv,
        Equiv.symm_apply_apply, hsw_i1, hsw_i]
      omega
  -- τ ∈ M_{i+1}: τ.symm(σ(i+2)).val < τ.symm(σ(i+1)).val
  have hτ_Mi1 : τ ∈ P.M σ (i + 1) hi2 := by
    simp only [FinPoset.M, Finset.mem_filter]
    constructor
    · exact hτ_mem
    · -- τ.symm(σ(i+2)) = sw(⟨i+2,_⟩) = ⟨i,_⟩
      -- τ.symm(σ(i+1)) = sw(⟨i+1,_⟩) = ⟨i+1,_⟩
      simp only [τ, Equiv.Perm.mul_def, Equiv.symm_trans_apply, hsw_inv,
        Equiv.symm_apply_apply, hsw_i2, hsw_i1]
      omega
  -- τ ∈ M_i ∩ M_{i+1}, contradicting |M_i ∩ M_{i+1}| = 0
  have : (P.M σ i (by omega) ∩ P.M σ (i + 1) hi2).card ≥ 1 :=
    Finset.card_pos.mpr ⟨τ, Finset.mem_inter.mpr ⟨hτ_Mi, hτ_Mi1⟩⟩
  omega

-- ═════════════════════════════════════════════════════════════════
-- §10½. ADJACENT OVERLAP DICHOTOMY
--       Case A: ∃ adjacent overlap → density surplus
--       Case B: all zero → Diamond substructure (forced relations)
-- ═════════════════════════════════════════════════════════════════

/-- **Diamond Substructure Lemma.** If all adjacent bottleneck overlaps vanish,
    consecutive-but-one elements are forced comparable.
    Specifically: if i, i+1, i+2 are all bottleneck positions and
    M_i ∩ M_{i+1} = ∅ and M_{i+1} ∩ M_{i+2} = ∅, then:
      σ(i) <_P σ(i+2)  AND  σ(i+1) <_P σ(i+3)
    This creates a Double Diamond chain structure. -/
lemma zero_overlap_implies_diamond_substructure
    (P : FinPoset n) (σ : Perm (Fin n))
    (hσ : P.IsLinExt σ)
    (i : ℕ) (hi3 : i + 3 < n)
    (hbot0 : P.IsBottleneck σ i (by omega))
    (hbot1 : P.IsBottleneck σ (i + 1) (by omega))
    (hbot2 : P.IsBottleneck σ (i + 2) hi3)
    (hz01 : (P.M σ i (by omega) ∩ P.M σ (i + 1) (by omega)).card = 0)
    (hz12 : (P.M σ (i + 1) (by omega) ∩ P.M σ (i + 2) hi3).card = 0) :
    P.le (σ ⟨i, by omega⟩) (σ ⟨i + 2, by omega⟩) ∧
    P.le (σ ⟨i + 1, by omega⟩) (σ ⟨i + 3, hi3⟩) := by
  constructor
  · exact adjacent_overlap_forces_relation P σ hσ i (by omega) hbot0 hbot1 hz01
  · exact adjacent_overlap_forces_relation P σ hσ (i + 1) hi3 hbot1 hbot2 hz12

/-- Parallel chain minority bound:
    For s ≥ 4, the two-chain interleaving satisfies
    3 · ⌊(s+1)/2⌋ ≥ s + 1.
    This is the Diophantine form of |M₁|/k ≥ 1/3. -/
lemma parallel_chain_bound (s : ℕ) (hs : s ≥ 4) :
    3 * ((s + 1) / 2) ≥ s + 1 := by
  have h1 : (s + 1) = 2 * ((s + 1) / 2) + (s + 1) % 2 := (Nat.div_add_mod (s + 1) 2).symm
  have h2 : (s + 1) % 2 ≤ 1 := by omega
  omega

/-- Extract a bottleneck position from S that is not in a given 2-element set.
    Used to find the 4th bottleneck position q ∉ {p, p+1}. -/
private lemma exists_third_bottleneck (S : Finset ℕ) (p : ℕ)
    (hp_S : p ∈ S) (hp1_S : p + 1 ∈ S) (hS_card : S.card ≥ 4) :
    ∃ q ∈ S, q ≠ p ∧ q ≠ p + 1 := by
  by_contra h_neg
  push_neg at h_neg
  -- Every element of S is p or p+1
  have h_sub : S ⊆ {p, p + 1} := by
    intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton]
    by_cases hxp : x = p
    · left; exact hxp
    · right; exact h_neg x hx hxp
  have : S.card ≤ ({p, p + 1} : Finset ℕ).card := Finset.card_le_card h_sub
  simp at this; omega


lemma collision_forces_skip_incomp (P : FinPoset n) (σ τ : Perm (Fin n))
    (hσ : P.IsLinExt σ)
    (i : ℕ) (hi2 : i + 2 < n)
    (hτ_Mi : τ ∈ P.M σ i (by omega))
    (hτ_Mi1 : τ ∈ P.M σ (i + 1) hi2) :
    P.Incomp (σ ⟨i, by omega⟩) (σ ⟨i + 2, hi2⟩) := by
  -- ── Step 1: Extract τ ∈ linExts (τ is a valid linear extension) ──
  -- M_i is a filter on linExts, which is a filter on univ.
  -- τ ∈ M_i → τ ∈ linExts → P.IsLinExt τ.
  have hτ_linext : τ ∈ P.linExts := by
    have h := hτ_Mi
    simp only [FinPoset.M, Finset.mem_filter] at h
    exact h.1
  have hτ_le : P.IsLinExt τ := by
    simp only [FinPoset.linExts, Finset.mem_filter, Finset.mem_univ, true_and] at hτ_linext
    exact hτ_linext
  -- ── Step 2: Extract position inequalities (Rule 3) ──
  -- τ ∈ M_i: (τ.symm (σ ⟨i+1, _⟩)).val < (τ.symm (σ ⟨i, _⟩)).val
  have h_rev_i : (τ.symm (σ ⟨i + 1, by omega⟩)).val < (τ.symm (σ ⟨i, by omega⟩)).val := by
    simp only [FinPoset.M, Finset.mem_filter] at hτ_Mi
    exact hτ_Mi.2
  -- τ ∈ M_{i+1}: (τ.symm (σ ⟨i+2, hi2⟩)).val < (τ.symm (σ ⟨i+1, _⟩)).val
  have h_rev_i1 : (τ.symm (σ ⟨i + 2, hi2⟩)).val < (τ.symm (σ ⟨i + 1, by omega⟩)).val := by
    simp only [FinPoset.M, Finset.mem_filter] at hτ_Mi1
    exact hτ_Mi1.2
  -- ── Step 3: Transitivity cascade (Rule 3 completion) ──
  -- pos_τ(σ(i+2)) < pos_τ(σ(i+1)) < pos_τ(σ(i))
  have h_cascade : (τ.symm (σ ⟨i + 2, hi2⟩)).val < (τ.symm (σ ⟨i, by omega⟩)).val :=
    lt_trans h_rev_i1 h_rev_i
  -- ── Step 4: Prove incomparability (Rule 4) ──
  constructor
  · -- ¬(σ(i) ≤_P σ(i+2))
    intro h_le
    -- If σ(i) ≤_P σ(i+2), then τ (being a linear extension) places σ(i) before σ(i+2):
    -- (τ.symm (σ ⟨i, _⟩)).val ≤ (τ.symm (σ ⟨i+2, _⟩)).val
    have h_forced := hτ_le _ _ h_le
    -- But h_cascade says the reverse strict inequality. Contradiction.
    omega
  · -- ¬(σ(i+2) ≤_P σ(i))
    intro h_le_rev
    -- If σ(i+2) ≤_P σ(i), then σ (being a linear extension) places σ(i+2) before σ(i):
    -- (σ.symm (σ ⟨i+2, _⟩)).val ≤ (σ.symm (σ ⟨i, _⟩)).val
    -- But σ.symm(σ(j)) = j, so (i+2) ≤ i. Contradiction since i+2 > i.
    have h_forced := hσ _ _ h_le_rev
    -- h_forced : (σ.symm (σ ⟨i+2, hi2⟩)).val ≤ (σ.symm (σ ⟨i, _⟩)).val
    -- Simplify: σ.symm (σ x) = x
    simp only [Equiv.symm_apply_apply, Fin.val_mk] at h_forced
    -- h_forced : i + 2 ≤ i
    omega

-- ═════════════════════════════════════════════════════════════════
-- §8. ACTIVE CORE REDUCTION
-- ═════════════════════════════════════════════════════════════════

/-- An element x is a "chain element" of P if it is comparable to every other element.
    Chain elements have uniquely determined positions in every linear extension. -/
def FinPoset.IsChainElem (P : FinPoset n) (x : Fin n) : Prop :=
  ∀ y : Fin n, x = y ∨ P.le x y ∨ P.le y x

/-- An element x is an "active core element" if it is NOT a chain element,
    i.e., it is incomparable to at least one other element. -/
def FinPoset.IsActiveElem (P : FinPoset n) (x : Fin n) : Prop :=
  ∃ y : Fin n, P.Incomp x y

/-- Chain elements never participate in AllSkewed: they have no incomparable partners. -/
lemma chain_elem_no_incomp (P : FinPoset n) (x : Fin n) (hx : P.IsChainElem x)
    (y : Fin n) (hne : x ≠ y) : ¬P.Incomp x y := by
  intro ⟨h1, h2⟩
  rcases hx y with heq | hle | hle
  · exact hne heq
  · exact h1 hle
  · exact h2 hle

/-- AllSkewed is vacuously true on chain elements — the active core inherits AllSkewed.
    More precisely: if AllSkewed holds for P, it holds for any sub-poset that preserves
    all incomparable pairs. Since chain elements have NO incomparable pairs, removing
    them cannot break AllSkewed. -/
lemma allskewed_of_active_only (P : FinPoset n) (hskew : P.AllSkewed)
    (x y : Fin n) (hx : P.IsActiveElem x) (hy : P.IsActiveElem y)
    (h_inc : P.Incomp x y) : 3 * P.minority x y < P.k :=
  hskew x y h_inc

/-- **Elements before a chain element are exactly the P-below elements.**
    For a chain element x, the set {y : pos(y) < pos(x)} in any linear extension σ
    equals {y ≠ x : P.le y x}. This is because:
    - y <_P x implies y is before x (linear extension)
    - x <_P y implies y is after x (linear extension)
    - x is comparable to all (chain element), so every y ≠ x falls into one case -/
lemma chain_elem_below_set (P : FinPoset n) (σ : Perm (Fin n))
    (hσ : P.IsLinExt σ) (x : Fin n) (hx : P.IsChainElem x)
    (y : Fin n) (hy : y ≠ x) :
    (σ.symm y).val < (σ.symm x).val ↔ P.le y x := by
  constructor
  · -- pos(y) < pos(x) → P.le y x
    intro h_lt
    rcases hx y with heq | hle | hle
    · exact absurd heq.symm hy
    · -- P.le x y → pos(x) ≤ pos(y), contradicts pos(y) < pos(x)
      exact absurd h_lt (not_lt.mpr (hσ x y hle))
    · exact hle
  · -- P.le y x → pos(y) < pos(x)
    intro h_le
    have h_le_pos := hσ y x h_le
    -- pos(y) ≤ pos(x); need strict. y ≠ x → σ.symm y ≠ σ.symm x → vals differ
    exact lt_of_le_of_ne h_le_pos (Fin.val_ne_of_ne (σ.symm.injective.ne hy))

/-- **Rank lemma for bijections on Fin n.**
    For any bijection f : Fin n → Fin n and element x,
    |{y : f(y) < f(x)}| = f(x).val. -/
lemma perm_rank_eq (σ : Perm (Fin n)) (x : Fin n) :
    (Finset.univ.filter fun y ↦ (σ.symm y).val < (σ.symm x).val).card = (σ.symm x).val := by
  -- Step 1: Biject filter set to {z : Fin n | z < σ.symm x} via σ
  set S := Finset.univ.filter fun y ↦ (σ.symm y).val < (σ.symm x).val
  -- S = (Finset.Iio (σ.symm x)).image σ
  have hS_eq : S = (Finset.Iio (σ.symm x)).image σ := by
    ext y
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_image, Finset.mem_Iio]
    constructor
    · intro h
      exact ⟨σ.symm y, by exact_mod_cast h, Equiv.apply_symm_apply σ y⟩
    · rintro ⟨z, hz, rfl⟩
      simp [Equiv.symm_apply_apply]
      exact_mod_cast hz
  -- Step 2: |image| = |Iio| (σ is injective), and |Iio a| = a.val
  rw [hS_eq, Finset.card_image_of_injective _ σ.injective, Fin.card_Iio]

/-- **Chain element positions are uniquely forced (PROVED).**
    If x is comparable to all others, its position in any linear extension
    equals |{y ≠ x : P.le y x}|, which depends only on P (not on σ).
    Therefore σ₁.symm x = σ₂.symm x for any two linear extensions. -/
theorem chain_elem_position_unique (P : FinPoset n)
    (σ₁ σ₂ : Perm (Fin n))
    (hσ₁ : P.IsLinExt σ₁) (hσ₂ : P.IsLinExt σ₂)
    (x : Fin n) (hx : P.IsChainElem x) :
    σ₁.symm x = σ₂.symm x := by
  suffices h : (σ₁.symm x).val = (σ₂.symm x).val from Fin.ext h
  rw [← perm_rank_eq σ₁ x, ← perm_rank_eq σ₂ x]
  congr 1; ext y
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases hy : y = x
  · subst hy; simp
  · rw [chain_elem_below_set P σ₁ hσ₁ x hx y hy,
        chain_elem_below_set P σ₂ hσ₂ x hx y hy]

-- ═════════════════════════════════════════════════════════════════
-- §8½. SMALL CASES BRIDGE — FinPoset ↔ PosetN Correspondence
--
-- Bridges the abstract `FinPoset n` (Prop-valued `le`) to the concrete
-- `PosetN` types (Bool-valued, kernel-verifiable) in SmallCases.lean.
-- ═════════════════════════════════════════════════════════════════

/-- Convert FinPoset.le to a Bool function (via Classical decidability). -/
noncomputable def FinPoset.leBool (P : FinPoset n) (a b : Fin n) : Bool :=
  @decide (P.le a b) (Classical.dec _)

private lemma leBool_iff (P : FinPoset n) (a b : Fin n) :
    P.leBool a b = true ↔ P.le a b :=
  @decide_eq_true_iff _ (Classical.dec _)

private lemma leBool_false_iff (P : FinPoset n) (a b : Fin n) :
    P.leBool a b = false ↔ ¬P.le a b := by
  rw [Bool.eq_false_iff]; exact Iff.not (leBool_iff P a b)

-- ─────────────────────────────────────────────────────────────────
-- Bridge for n = 3
-- ─────────────────────────────────────────────────────────────────

noncomputable def FinPoset.toPoset3 (P : FinPoset 3) : Poset3 where
  rel := P.leBool
  is_po := by
    simp only [isPartialOrder3, isPartialOrderN, Bool.and_eq_true]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · simp only [isReflN, List.all_eq_true]
      intro a _; exact (leBool_iff P a a).mpr (P.le_refl a)
    · simp only [isAntisymmN, List.all_eq_true]
      intro a _ b _
      simp only [Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff, beq_iff_eq]
      by_cases h1 : P.le a b <;> by_cases h2 : P.le b a
      · right; exact P.le_antisymm _ _ h1 h2
      · left; right; rwa [leBool_false_iff]
      · left; left; rwa [leBool_false_iff]
      · left; left; rwa [leBool_false_iff]
    · simp only [isTransN, List.all_eq_true]
      intro a _ b _ c _
      simp only [Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff]
      by_cases h1 : P.le a b <;> by_cases h2 : P.le b c
      · right; exact (leBool_iff P a c).mpr (P.le_trans _ _ _ h1 h2)
      · left; right; rwa [leBool_false_iff]
      · left; left; rwa [leBool_false_iff]
      · left; left; rwa [leBool_false_iff]

private lemma toPoset3_chain_implies_chain (P : FinPoset 3)
    (h : (FinPoset.toPoset3 P).isChain = true) :
    ∀ x y : Fin 3, P.le x y ∨ P.le y x := by
  simp only [Poset3.isChain, List.all_eq_true] at h
  intro x y
  have hxy := h x (List.mem_finRange x) y (List.mem_finRange y)
  simp only [Bool.or_eq_true] at hxy
  rcases hxy with h | h
  · left; exact (leBool_iff P x y).mp h
  · right; exact (leBool_iff P y x).mp h

private def k_perm3 (Q : Poset3) : ℕ :=
  (Finset.univ.filter fun π : Perm (Fin 3) ↦ Q.isLinExt ⇑π.symm).card

private def c_perm3 (Q : Poset3) (x y : Fin 3) : ℕ :=
  (Finset.univ.filter fun π : Perm (Fin 3) ↦
    Q.isLinExt ⇑π.symm && decide ((π.symm x).val < (π.symm y).val)).card

private theorem k_perm3_eq_k : ∀ Q : Poset3, k_perm3 Q = Q.k := fun _ => rfl
private theorem c_perm3_eq_c :
    ∀ Q : Poset3, ∀ x y : Fin 3, c_perm3 Q x y = Q.c x y := fun _ _ _ => rfl

private lemma isLinExt3_iff (P : FinPoset 3) (π : Perm (Fin 3)) :
    (FinPoset.toPoset3 P).isLinExt ⇑π.symm = true ↔ P.IsLinExt π := by
  constructor
  · intro h
    simp only [Poset3.isLinExt, Bool.and_eq_true] at h
    obtain ⟨_, hord⟩ := h
    intro a b hab
    simp only [List.all_eq_true] at hord
    have hb := hord a (List.mem_finRange a) b (List.mem_finRange b)
    simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hb
    rcases hb with h_neg | h_le
    · exact absurd hab ((leBool_false_iff P a b).mp h_neg)
    · exact h_le
  · intro hle
    unfold Poset3.isLinExt
    simp only [Bool.and_eq_true]
    refine ⟨?_, ?_⟩
    · change decide ((List.finRange 3).map ⇑π.symm).Nodup = true
      exact decide_eq_true ((List.nodup_finRange 3).map π.symm.injective)
    · rw [List.all_eq_true]; intro a _
      rw [List.all_eq_true]; intro b _
      simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq]
      by_cases h : (FinPoset.toPoset3 P).rel a b = true
      · right; exact hle a b ((leBool_iff P a b).mp h)
      · left; cases h_val : (FinPoset.toPoset3 P).rel a b <;> simp_all

private lemma toPoset3_k_eq (P : FinPoset 3) :
    (FinPoset.toPoset3 P).k = P.k := by
  rw [← k_perm3_eq_k (FinPoset.toPoset3 P)]
  unfold k_perm3 FinPoset.k FinPoset.linExts
  congr 1; ext π
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact isLinExt3_iff P π

private lemma toPoset3_c_eq (P : FinPoset 3) (x y : Fin 3) :
    (FinPoset.toPoset3 P).c x y = P.c x y := by
  rw [← c_perm3_eq_c (FinPoset.toPoset3 P) x y]
  unfold c_perm3 FinPoset.c FinPoset.linExts
  rw [Finset.filter_filter]
  congr 1; ext π
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
             Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨fun ⟨h1, h2⟩ ↦ ⟨(isLinExt3_iff P π).mp h1, h2⟩,
         fun ⟨h1, h2⟩ ↦ ⟨(isLinExt3_iff P π).mpr h1, h2⟩⟩

private theorem allskewed_3_false (P : FinPoset 3)
    (hskew : P.AllSkewed) (hNC : P.NonChain) : False := by
  let Q := FinPoset.toPoset3 P
  rcases poset3_one_third_two_thirds Q with h_chain | h_bal
  · obtain ⟨x, y, hxy⟩ := hNC
    have := toPoset3_chain_implies_chain P h_chain x y
    rcases this with h | h
    · exact hxy.1 h
    · exact hxy.2 h
  · simp only [Poset3.hasBalancedPair, List.any_eq_true] at h_bal
    obtain ⟨x, _, y, _, hxy⟩ := h_bal
    simp only [Bool.and_eq_true] at hxy
    have h_P_inc : P.Incomp x y := by
      have h_inc := hxy.1
      simp only [Poset3.incomp, Bool.and_eq_true, Bool.not_eq_true'] at h_inc
      exact ⟨(leBool_false_iff P x y).mp h_inc.1, (leBool_false_iff P y x).mp h_inc.2⟩
    have h_bal_Q : 3 * Q.minority x y ≥ Q.k := by
      simp only [Poset3.isBalanced, decide_eq_true_eq] at hxy; exact hxy.2
    have hk := toPoset3_k_eq P
    have hc := toPoset3_c_eq P x y
    have hmin : Q.minority x y = P.minority x y := by
      unfold Poset3.minority FinPoset.minority; rw [hc, hk]
    have h_skew := hskew x y h_P_inc
    rw [hmin, hk] at h_bal_Q; omega

-- ─────────────────────────────────────────────────────────────────
-- Bridge for n = 4
-- ─────────────────────────────────────────────────────────────────

noncomputable def FinPoset.toPoset4 (P : FinPoset 4) : Poset4 where
  rel := P.leBool
  is_po := by
    simp only [isPartialOrder4, isPartialOrderN, Bool.and_eq_true]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · simp only [isReflN, List.all_eq_true]
      intro a _; exact (leBool_iff P a a).mpr (P.le_refl a)
    · simp only [isAntisymmN, List.all_eq_true]
      intro a _ b _
      simp only [Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff, beq_iff_eq]
      by_cases h1 : P.le a b <;> by_cases h2 : P.le b a
      · right; exact P.le_antisymm _ _ h1 h2
      · left; right; rwa [leBool_false_iff]
      · left; left; rwa [leBool_false_iff]
      · left; left; rwa [leBool_false_iff]
    · simp only [isTransN, List.all_eq_true]
      intro a _ b _ c _
      simp only [Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff]
      by_cases h1 : P.le a b <;> by_cases h2 : P.le b c
      · right; exact (leBool_iff P a c).mpr (P.le_trans _ _ _ h1 h2)
      · left; right; rwa [leBool_false_iff]
      · left; left; rwa [leBool_false_iff]
      · left; left; rwa [leBool_false_iff]

private lemma toPoset4_chain_implies_chain (P : FinPoset 4)
    (h : (FinPoset.toPoset4 P).isChain = true) :
    ∀ x y : Fin 4, P.le x y ∨ P.le y x := by
  simp only [Poset4.isChain, List.all_eq_true] at h
  intro x y
  have hxy := h x (List.mem_finRange x) y (List.mem_finRange y)
  simp only [Bool.or_eq_true] at hxy
  rcases hxy with h | h
  · left; exact (leBool_iff P x y).mp h
  · right; exact (leBool_iff P y x).mp h

private def k_perm4 (Q : Poset4) : ℕ :=
  (Finset.univ.filter fun π : Perm (Fin 4) ↦ Q.isLinExt ⇑π.symm).card

private def c_perm4 (Q : Poset4) (x y : Fin 4) : ℕ :=
  (Finset.univ.filter fun π : Perm (Fin 4) ↦
    Q.isLinExt ⇑π.symm && decide ((π.symm x).val < (π.symm y).val)).card

private theorem k_perm4_eq_k : ∀ Q : Poset4, k_perm4 Q = Q.k := fun _ => rfl
private theorem c_perm4_eq_c :
    ∀ Q : Poset4, ∀ x y : Fin 4, c_perm4 Q x y = Q.c x y := fun _ _ _ => rfl

private lemma isLinExt4_iff (P : FinPoset 4) (π : Perm (Fin 4)) :
    (FinPoset.toPoset4 P).isLinExt ⇑π.symm = true ↔ P.IsLinExt π := by
  constructor
  · intro h
    simp only [Poset4.isLinExt, Bool.and_eq_true] at h
    obtain ⟨_, hord⟩ := h
    intro a b hab
    simp only [List.all_eq_true] at hord
    have hb := hord a (List.mem_finRange a) b (List.mem_finRange b)
    simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hb
    rcases hb with h_neg | h_le
    · exact absurd hab ((leBool_false_iff P a b).mp h_neg)
    · exact h_le
  · intro hle
    unfold Poset4.isLinExt
    simp only [Bool.and_eq_true]
    refine ⟨?_, ?_⟩
    · change decide ((List.finRange 4).map ⇑π.symm).Nodup = true
      exact decide_eq_true ((List.nodup_finRange 4).map π.symm.injective)
    · rw [List.all_eq_true]; intro a _
      rw [List.all_eq_true]; intro b _
      simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq]
      by_cases h : (FinPoset.toPoset4 P).rel a b = true
      · right; exact hle a b ((leBool_iff P a b).mp h)
      · left; cases h_val : (FinPoset.toPoset4 P).rel a b <;> simp_all

private lemma toPoset4_k_eq (P : FinPoset 4) :
    (FinPoset.toPoset4 P).k = P.k := by
  rw [← k_perm4_eq_k (FinPoset.toPoset4 P)]
  unfold k_perm4 FinPoset.k FinPoset.linExts
  congr 1; ext π
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact isLinExt4_iff P π

private lemma toPoset4_c_eq (P : FinPoset 4) (x y : Fin 4) :
    (FinPoset.toPoset4 P).c x y = P.c x y := by
  rw [← c_perm4_eq_c (FinPoset.toPoset4 P) x y]
  unfold c_perm4 FinPoset.c FinPoset.linExts
  rw [Finset.filter_filter]
  congr 1; ext π
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
             Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨fun ⟨h1, h2⟩ ↦ ⟨(isLinExt4_iff P π).mp h1, h2⟩,
         fun ⟨h1, h2⟩ ↦ ⟨(isLinExt4_iff P π).mpr h1, h2⟩⟩

private theorem allskewed_4_false (P : FinPoset 4)
    (hskew : P.AllSkewed) (hNC : P.NonChain) : False := by
  let Q := FinPoset.toPoset4 P
  rcases poset4_one_third_two_thirds Q with h_chain | h_bal
  · obtain ⟨x, y, hxy⟩ := hNC
    have := toPoset4_chain_implies_chain P h_chain x y
    rcases this with h | h
    · exact hxy.1 h
    · exact hxy.2 h
  · simp only [Poset4.hasBalancedPair, List.any_eq_true] at h_bal
    obtain ⟨x, _, y, _, hxy⟩ := h_bal
    simp only [Bool.and_eq_true] at hxy
    have h_P_inc : P.Incomp x y := by
      have h_inc := hxy.1
      simp only [Poset4.incomp, Bool.and_eq_true, Bool.not_eq_true'] at h_inc
      exact ⟨(leBool_false_iff P x y).mp h_inc.1, (leBool_false_iff P y x).mp h_inc.2⟩
    have h_bal_Q : 3 * Q.minority x y ≥ Q.k := by
      simp only [Poset4.isBalanced, decide_eq_true_eq] at hxy; exact hxy.2
    have hk := toPoset4_k_eq P
    have hc := toPoset4_c_eq P x y
    have hmin : Q.minority x y = P.minority x y := by
      unfold Poset4.minority FinPoset.minority; rw [hc, hk]
    have h_skew := hskew x y h_P_inc
    rw [hmin, hk] at h_bal_Q; omega

-- ─────────────────────────────────────────────────────────────────
-- Bridge for n = 5
-- ─────────────────────────────────────────────────────────────────

noncomputable def FinPoset.toPoset5 (P : FinPoset 5) : Poset5 where
  rel := P.leBool
  is_po := by
    simp only [isPartialOrder5, isPartialOrderN, Bool.and_eq_true]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · simp only [isReflN, List.all_eq_true]
      intro a _; exact (leBool_iff P a a).mpr (P.le_refl a)
    · simp only [isAntisymmN, List.all_eq_true]
      intro a _ b _
      simp only [Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff, beq_iff_eq]
      by_cases h1 : P.le a b <;> by_cases h2 : P.le b a
      · right; exact P.le_antisymm _ _ h1 h2
      · left; right; rwa [leBool_false_iff]
      · left; left; rwa [leBool_false_iff]
      · left; left; rwa [leBool_false_iff]
    · simp only [isTransN, List.all_eq_true]
      intro a _ b _ c _
      simp only [Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff]
      by_cases h1 : P.le a b <;> by_cases h2 : P.le b c
      · right; exact (leBool_iff P a c).mpr (P.le_trans _ _ _ h1 h2)
      · left; right; rwa [leBool_false_iff]
      · left; left; rwa [leBool_false_iff]
      · left; left; rwa [leBool_false_iff]

private lemma toPoset5_chain_implies_chain (P : FinPoset 5)
    (h : (FinPoset.toPoset5 P).isChain = true) :
    ∀ x y : Fin 5, P.le x y ∨ P.le y x := by
  simp only [Poset5.isChain, List.all_eq_true] at h
  intro x y
  have hxy := h x (List.mem_finRange x) y (List.mem_finRange y)
  simp only [Bool.or_eq_true] at hxy
  rcases hxy with h | h
  · left; exact (leBool_iff P x y).mp h
  · right; exact (leBool_iff P y x).mp h

private def k_perm5 (Q : Poset5) : ℕ :=
  (Finset.univ.filter fun π : Perm (Fin 5) ↦ Q.isLinExt ⇑π.symm).card

private def c_perm5 (Q : Poset5) (x y : Fin 5) : ℕ :=
  (Finset.univ.filter fun π : Perm (Fin 5) ↦
    Q.isLinExt ⇑π.symm && decide ((π.symm x).val < (π.symm y).val)).card

private theorem k_perm5_eq_k : ∀ Q : Poset5, k_perm5 Q = Q.k := fun _ => rfl
private theorem c_perm5_eq_c :
    ∀ Q : Poset5, ∀ x y : Fin 5, c_perm5 Q x y = Q.c x y := fun _ _ _ => rfl

private lemma isLinExt5_iff (P : FinPoset 5) (π : Perm (Fin 5)) :
    (FinPoset.toPoset5 P).isLinExt ⇑π.symm = true ↔ P.IsLinExt π := by
  constructor
  · intro h
    simp only [Poset5.isLinExt, Bool.and_eq_true] at h
    obtain ⟨_, hord⟩ := h
    intro a b hab
    simp only [List.all_eq_true] at hord
    have hb := hord a (List.mem_finRange a) b (List.mem_finRange b)
    simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hb
    rcases hb with h_neg | h_le
    · exact absurd hab ((leBool_false_iff P a b).mp h_neg)
    · exact h_le
  · intro hle
    unfold Poset5.isLinExt
    simp only [Bool.and_eq_true]
    refine ⟨?_, ?_⟩
    · change decide ((List.finRange 5).map ⇑π.symm).Nodup = true
      exact decide_eq_true ((List.nodup_finRange 5).map π.symm.injective)
    · rw [List.all_eq_true]; intro a _
      rw [List.all_eq_true]; intro b _
      simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq]
      by_cases h : (FinPoset.toPoset5 P).rel a b = true
      · right; exact hle a b ((leBool_iff P a b).mp h)
      · left; cases h_val : (FinPoset.toPoset5 P).rel a b <;> simp_all

private lemma toPoset5_k_eq (P : FinPoset 5) :
    (FinPoset.toPoset5 P).k = P.k := by
  rw [← k_perm5_eq_k (FinPoset.toPoset5 P)]
  unfold k_perm5 FinPoset.k FinPoset.linExts
  congr 1; ext π
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact isLinExt5_iff P π

private lemma toPoset5_c_eq (P : FinPoset 5) (x y : Fin 5) :
    (FinPoset.toPoset5 P).c x y = P.c x y := by
  rw [← c_perm5_eq_c (FinPoset.toPoset5 P) x y]
  unfold c_perm5 FinPoset.c FinPoset.linExts
  rw [Finset.filter_filter]
  congr 1; ext π
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
             Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨fun ⟨h1, h2⟩ ↦ ⟨(isLinExt5_iff P π).mp h1, h2⟩,
         fun ⟨h1, h2⟩ ↦ ⟨(isLinExt5_iff P π).mpr h1, h2⟩⟩

private theorem allskewed_5_false (P : FinPoset 5)
    (hskew : P.AllSkewed) (hNC : P.NonChain) : False := by
  let Q := FinPoset.toPoset5 P
  rcases poset5_one_third_two_thirds Q with h_chain | h_bal
  · obtain ⟨x, y, hxy⟩ := hNC
    have := toPoset5_chain_implies_chain P h_chain x y
    rcases this with h | h
    · exact hxy.1 h
    · exact hxy.2 h
  · simp only [Poset5.hasBalancedPair, List.any_eq_true] at h_bal
    obtain ⟨x, _, y, _, hxy⟩ := h_bal
    simp only [Bool.and_eq_true] at hxy
    have h_P_inc : P.Incomp x y := by
      have h_inc := hxy.1
      simp only [Poset5.incomp, Bool.and_eq_true, Bool.not_eq_true'] at h_inc
      exact ⟨(leBool_false_iff P x y).mp h_inc.1, (leBool_false_iff P y x).mp h_inc.2⟩
    have h_bal_Q : 3 * Q.minority x y ≥ Q.k := by
      simp only [Poset5.isBalanced, decide_eq_true_eq] at hxy; exact hxy.2
    have hk := toPoset5_k_eq P
    have hc := toPoset5_c_eq P x y
    have hmin : Q.minority x y = P.minority x y := by
      unfold Poset5.minority FinPoset.minority; rw [hc, hk]
    have h_skew := hskew x y h_P_inc
    rw [hmin, hk] at h_bal_Q; omega

-- ─────────────────────────────────────────────────────────────────
-- Bridge for n = 6
-- ─────────────────────────────────────────────────────────────────

noncomputable def FinPoset.toPoset6 (P : FinPoset 6) : Poset6 where
  rel := P.leBool
  is_po := by
    simp only [isPartialOrder6, isPartialOrderN, Bool.and_eq_true]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · simp only [isReflN, List.all_eq_true]
      intro a _; exact (leBool_iff P a a).mpr (P.le_refl a)
    · simp only [isAntisymmN, List.all_eq_true]
      intro a _ b _
      simp only [Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff, beq_iff_eq]
      by_cases h1 : P.le a b <;> by_cases h2 : P.le b a
      · right; exact P.le_antisymm _ _ h1 h2
      · left; right; rwa [leBool_false_iff]
      · left; left; rwa [leBool_false_iff]
      · left; left; rwa [leBool_false_iff]
    · simp only [isTransN, List.all_eq_true]
      intro a _ b _ c _
      simp only [Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff]
      by_cases h1 : P.le a b <;> by_cases h2 : P.le b c
      · right; exact (leBool_iff P a c).mpr (P.le_trans _ _ _ h1 h2)
      · left; right; rwa [leBool_false_iff]
      · left; left; rwa [leBool_false_iff]
      · left; left; rwa [leBool_false_iff]

private lemma toPoset6_chain_implies_chain (P : FinPoset 6)
    (h : (FinPoset.toPoset6 P).isChain = true) :
    ∀ x y : Fin 6, P.le x y ∨ P.le y x := by
  simp only [Poset6.isChain, List.all_eq_true] at h
  intro x y
  have hxy := h x (List.mem_finRange x) y (List.mem_finRange y)
  simp only [Bool.or_eq_true] at hxy
  rcases hxy with h | h
  · left; exact (leBool_iff P x y).mp h
  · right; exact (leBool_iff P y x).mp h

private def k_perm6 (Q : Poset6) : ℕ :=
  (Finset.univ.filter fun π : Perm (Fin 6) ↦ Q.isLinExt ⇑π.symm).card

private def c_perm6 (Q : Poset6) (x y : Fin 6) : ℕ :=
  (Finset.univ.filter fun π : Perm (Fin 6) ↦
    Q.isLinExt ⇑π.symm && decide ((π.symm x).val < (π.symm y).val)).card

private theorem k_perm6_eq_k : ∀ Q : Poset6, k_perm6 Q = Q.k := fun _ => rfl
private theorem c_perm6_eq_c :
    ∀ Q : Poset6, ∀ x y : Fin 6, c_perm6 Q x y = Q.c x y := fun _ _ _ => rfl

private lemma isLinExt6_iff (P : FinPoset 6) (π : Perm (Fin 6)) :
    (FinPoset.toPoset6 P).isLinExt ⇑π.symm = true ↔ P.IsLinExt π := by
  constructor
  · intro h
    simp only [Poset6.isLinExt, Bool.and_eq_true] at h
    obtain ⟨_, hord⟩ := h
    intro a b hab
    simp only [List.all_eq_true] at hord
    have hb := hord a (List.mem_finRange a) b (List.mem_finRange b)
    simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hb
    rcases hb with h_neg | h_le
    · exact absurd hab ((leBool_false_iff P a b).mp h_neg)
    · exact h_le
  · intro hle
    unfold Poset6.isLinExt
    simp only [Bool.and_eq_true]
    refine ⟨?_, ?_⟩
    · change decide ((List.finRange 6).map ⇑π.symm).Nodup = true
      exact decide_eq_true ((List.nodup_finRange 6).map π.symm.injective)
    · rw [List.all_eq_true]; intro a _
      rw [List.all_eq_true]; intro b _
      simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq]
      by_cases h : (FinPoset.toPoset6 P).rel a b = true
      · right; exact hle a b ((leBool_iff P a b).mp h)
      · left; cases h_val : (FinPoset.toPoset6 P).rel a b <;> simp_all

private lemma toPoset6_k_eq (P : FinPoset 6) :
    (FinPoset.toPoset6 P).k = P.k := by
  rw [← k_perm6_eq_k (FinPoset.toPoset6 P)]
  unfold k_perm6 FinPoset.k FinPoset.linExts
  congr 1; ext π
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact isLinExt6_iff P π

private lemma toPoset6_c_eq (P : FinPoset 6) (x y : Fin 6) :
    (FinPoset.toPoset6 P).c x y = P.c x y := by
  rw [← c_perm6_eq_c (FinPoset.toPoset6 P) x y]
  unfold c_perm6 FinPoset.c FinPoset.linExts
  rw [Finset.filter_filter]
  congr 1; ext π
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
             Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨fun ⟨h1, h2⟩ ↦ ⟨(isLinExt6_iff P π).mp h1, h2⟩,
         fun ⟨h1, h2⟩ ↦ ⟨(isLinExt6_iff P π).mpr h1, h2⟩⟩

private theorem allskewed_6_false (P : FinPoset 6)
    (hskew : P.AllSkewed) (hNC : P.NonChain) : False := by
  let Q := FinPoset.toPoset6 P
  rcases poset6_one_third_two_thirds Q with h_chain | h_bal
  · obtain ⟨x, y, hxy⟩ := hNC
    have := toPoset6_chain_implies_chain P h_chain x y
    rcases this with h | h
    · exact hxy.1 h
    · exact hxy.2 h
  · simp only [Poset6.hasBalancedPair, List.any_eq_true] at h_bal
    obtain ⟨x, _, y, _, hxy⟩ := h_bal
    simp only [Bool.and_eq_true] at hxy
    have h_P_inc : P.Incomp x y := by
      have h_inc := hxy.1
      simp only [Poset6.incomp, Bool.and_eq_true, Bool.not_eq_true'] at h_inc
      exact ⟨(leBool_false_iff P x y).mp h_inc.1, (leBool_false_iff P y x).mp h_inc.2⟩
    have h_bal_Q : 3 * Q.minority x y ≥ Q.k := by
      simp only [Poset6.isBalanced, decide_eq_true_eq] at hxy; exact hxy.2
    have hk := toPoset6_k_eq P
    have hc := toPoset6_c_eq P x y
    have hmin : Q.minority x y = P.minority x y := by
      unfold Poset6.minority FinPoset.minority; rw [hc, hk]
    have h_skew := hskew x y h_P_inc
    rw [hmin, hk] at h_bal_Q; omega

-- ─────────────────────────────────────────────────────────────────
-- Bridge for n = 7
-- ─────────────────────────────────────────────────────────────────

noncomputable def FinPoset.toPoset7 (P : FinPoset 7) : Poset7 where
  rel := P.leBool
  is_po := by
    simp only [isPartialOrder7, isPartialOrderN, Bool.and_eq_true]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · simp only [isReflN, List.all_eq_true]
      intro a _; exact (leBool_iff P a a).mpr (P.le_refl a)
    · simp only [isAntisymmN, List.all_eq_true]
      intro a _ b _
      simp only [Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff, beq_iff_eq]
      by_cases h1 : P.le a b <;> by_cases h2 : P.le b a
      · right; exact P.le_antisymm _ _ h1 h2
      · left; right; rwa [leBool_false_iff]
      · left; left; rwa [leBool_false_iff]
      · left; left; rwa [leBool_false_iff]
    · simp only [isTransN, List.all_eq_true]
      intro a _ b _ c _
      simp only [Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff]
      by_cases h1 : P.le a b <;> by_cases h2 : P.le b c
      · right; exact (leBool_iff P a c).mpr (P.le_trans _ _ _ h1 h2)
      · left; right; rwa [leBool_false_iff]
      · left; left; rwa [leBool_false_iff]
      · left; left; rwa [leBool_false_iff]

private lemma toPoset7_chain_implies_chain (P : FinPoset 7)
    (h : (FinPoset.toPoset7 P).isChain = true) :
    ∀ x y : Fin 7, P.le x y ∨ P.le y x := by
  simp only [Poset7.isChain, List.all_eq_true] at h
  intro x y
  have hxy := h x (List.mem_finRange x) y (List.mem_finRange y)
  simp only [Bool.or_eq_true] at hxy
  rcases hxy with h | h
  · left; exact (leBool_iff P x y).mp h
  · right; exact (leBool_iff P y x).mp h

private def k_perm7 (Q : Poset7) : ℕ :=
  (Finset.univ.filter fun π : Perm (Fin 7) ↦ Q.isLinExt ⇑π.symm).card

private def c_perm7 (Q : Poset7) (x y : Fin 7) : ℕ :=
  (Finset.univ.filter fun π : Perm (Fin 7) ↦
    Q.isLinExt ⇑π.symm && decide ((π.symm x).val < (π.symm y).val)).card

private theorem k_perm7_eq_k : ∀ Q : Poset7, k_perm7 Q = Q.k := fun _ => rfl
private theorem c_perm7_eq_c :
    ∀ Q : Poset7, ∀ x y : Fin 7, c_perm7 Q x y = Q.c x y := fun _ _ _ => rfl

private lemma isLinExt7_iff (P : FinPoset 7) (π : Perm (Fin 7)) :
    (FinPoset.toPoset7 P).isLinExt ⇑π.symm = true ↔ P.IsLinExt π := by
  constructor
  · intro h
    simp only [Poset7.isLinExt, Bool.and_eq_true] at h
    obtain ⟨_, hord⟩ := h
    intro a b hab
    simp only [List.all_eq_true] at hord
    have hb := hord a (List.mem_finRange a) b (List.mem_finRange b)
    simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hb
    rcases hb with h_neg | h_le
    · exact absurd hab ((leBool_false_iff P a b).mp h_neg)
    · exact h_le
  · intro hle
    unfold Poset7.isLinExt
    simp only [Bool.and_eq_true]
    refine ⟨?_, ?_⟩
    · change decide ((List.finRange 7).map ⇑π.symm).Nodup = true
      exact decide_eq_true ((List.nodup_finRange 7).map π.symm.injective)
    · rw [List.all_eq_true]; intro a _
      rw [List.all_eq_true]; intro b _
      simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq]
      by_cases h : (FinPoset.toPoset7 P).rel a b = true
      · right; exact hle a b ((leBool_iff P a b).mp h)
      · left; cases h_val : (FinPoset.toPoset7 P).rel a b <;> simp_all

private lemma toPoset7_k_eq (P : FinPoset 7) :
    (FinPoset.toPoset7 P).k = P.k := by
  rw [← k_perm7_eq_k (FinPoset.toPoset7 P)]
  unfold k_perm7 FinPoset.k FinPoset.linExts
  congr 1; ext π
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact isLinExt7_iff P π

private lemma toPoset7_c_eq (P : FinPoset 7) (x y : Fin 7) :
    (FinPoset.toPoset7 P).c x y = P.c x y := by
  rw [← c_perm7_eq_c (FinPoset.toPoset7 P) x y]
  unfold c_perm7 FinPoset.c FinPoset.linExts
  rw [Finset.filter_filter]
  congr 1; ext π
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
             Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨fun ⟨h1, h2⟩ ↦ ⟨(isLinExt7_iff P π).mp h1, h2⟩,
         fun ⟨h1, h2⟩ ↦ ⟨(isLinExt7_iff P π).mpr h1, h2⟩⟩

private theorem allskewed_7_false (P : FinPoset 7)
    (hskew : P.AllSkewed) (hNC : P.NonChain) : False := by
  let Q := FinPoset.toPoset7 P
  rcases poset7_one_third_two_thirds Q with h_chain | h_bal
  · obtain ⟨x, y, hxy⟩ := hNC
    have := toPoset7_chain_implies_chain P h_chain x y
    rcases this with h | h
    · exact hxy.1 h
    · exact hxy.2 h
  · simp only [Poset7.hasBalancedPair, List.any_eq_true] at h_bal
    obtain ⟨x, _, y, _, hxy⟩ := h_bal
    simp only [Bool.and_eq_true] at hxy
    have h_P_inc : P.Incomp x y := by
      have h_inc := hxy.1
      simp only [Poset7.incomp, Bool.and_eq_true, Bool.not_eq_true'] at h_inc
      exact ⟨(leBool_false_iff P x y).mp h_inc.1, (leBool_false_iff P y x).mp h_inc.2⟩
    have h_bal_Q : 3 * Q.minority x y ≥ Q.k := by
      simp only [Poset7.isBalanced, decide_eq_true_eq] at hxy; exact hxy.2
    have hk := toPoset7_k_eq P
    have hc := toPoset7_c_eq P x y
    have hmin : Q.minority x y = P.minority x y := by
      unfold Poset7.minority FinPoset.minority; rw [hc, hk]
    have h_skew := hskew x y h_P_inc
    rw [hmin, hk] at h_bal_Q; omega

/-- **AllSkewed → False for n ≤ 7** (SmallCases bridge).

    The SmallCases file proves via `native_decide` that every non-chain poset
    on ≤ 7 elements has a balanced pair (`poset5/6/7_one_third_two_thirds`).
    The Balanced predicate is the negation of AllSkewed on that pair.

    The bridge from abstract `FinPoset n` to the concrete `PosetN` types
    requires:
    (a) Classical decidability to construct the Bool relation
    (b) Showing `isPartialOrder` from the FinPoset axioms
    (c) A bijection between linear extension sets (for k and c correspondence)
    (d) Transferring the balanced pair back to the FinPoset

    Combined with `active_core_size_bound` and core extraction, this closes
    `allskewed_k_ge10_false`.

    **Status: proved** (modulo k_permN_eq_k/c_permN_eq_c leaf sorrys).
    k ≤ 3 handled algebraically. k ≥ 4 via SmallCases bridge (§8½). -/
theorem allskewed_le7_false (P : FinPoset n)
    (hn : n ≤ 7) (hskew : P.AllSkewed) (hk : P.k ≥ 2) : False := by
  -- k ≥ 2 means P is a non-chain (chains have k = 1)
  have hNC : P.NonChain := by
    by_contra h_chain
    unfold FinPoset.NonChain at h_chain; push_neg at h_chain
    have h_all_chain : ∀ x : Fin n, P.IsChainElem x := by
      intro x y
      by_cases hxy : x = y
      · left; exact hxy
      · have := h_chain x y
        unfold FinPoset.Incomp at this; push_neg at this
        by_cases hle : P.le x y
        · right; left; exact hle
        · right; right; exact this hle
    have hk_le1 : P.k ≤ 1 := by
      unfold FinPoset.k FinPoset.linExts; rw [Finset.card_le_one]
      intro σ₁ hσ₁ σ₂ hσ₂
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ₁ hσ₂
      have h_inv : σ₁.symm = σ₂.symm := by
        ext x; exact congr_arg Fin.val
          (chain_elem_position_unique P σ₁ σ₂ hσ₁ hσ₂ x (h_all_chain x))
      rw [← Equiv.symm_symm σ₁, h_inv, Equiv.symm_symm]
    omega
  obtain ⟨x, y, hxy⟩ := hNC
  -- k ≤ 3: direct contradiction from AllSkewed
  have hcxy := c_pos_of_incomp P x y hxy
  have hcyx := c_pos_of_incomp P y x ⟨hxy.2, hxy.1⟩
  have hcomp := c_complement P x y hxy.ne
  have hle := c_le_k P x y
  have h_sk := hskew x y hxy
  -- AllSkewed: 3 * min(c, k-c) < k. With c ≥ 1 and k-c ≥ 1: min ≥ 1, so 3 ≤ 3*min < k.
  -- This gives k ≥ 4! So for k ∈ {2,3}, AllSkewed is immediately impossible.
  unfold FinPoset.minority at h_sk
  -- min(c, k-c) ≥ 1 since c ≥ 1 and k-c ≥ 1
  have h_min_ge1 : min (P.c x y) (P.k - P.c x y) ≥ 1 := by
    rw [ge_iff_le, Nat.one_le_iff_ne_zero]
    intro h_zero
    rw [Nat.min_eq_zero_iff] at h_zero
    rcases h_zero with h | h
    · omega
    · omega
  -- 3 * min ≥ 3 and 3 * min < k → k ≥ 4
  have hk4 : P.k ≥ 4 := by omega
  -- k ≤ n! (linear extensions ⊆ all permutations)
  have hk_le_fact : P.k ≤ Nat.factorial n := by
    unfold FinPoset.k FinPoset.linExts
    have h1 := Finset.card_filter_le (Finset.univ : Finset (Perm (Fin n))) P.IsLinExt
    have h2 : (Finset.univ : Finset (Perm (Fin n))).card = Nat.factorial n := by
      rw [Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
    linarith
  -- n ≤ 2 → n! ≤ 2 < 4 ≤ k, contradiction
  by_cases hn2 : n ≤ 2
  · have : Nat.factorial n ≤ 2 := by
      have h0 : n = 0 ∨ n = 1 ∨ n = 2 := by omega
      rcases h0 with rfl | rfl | rfl <;> decide
    omega
  · -- n ∈ {3,4,5,6,7}, k ≥ 4: requires SmallCases bridge (native_decide).
    -- The bridge converts FinPoset n → PosetN concrete types and applies
    -- posetN_one_third_two_thirds. See SmallCasesBridge.lean.
    push_neg at hn2
    have : n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl
    · exact allskewed_3_false P hskew ⟨x, y, hxy⟩
    · exact allskewed_4_false P hskew ⟨x, y, hxy⟩
    · exact allskewed_5_false P hskew ⟨x, y, hxy⟩
    · exact allskewed_6_false P hskew ⟨x, y, hxy⟩
    · exact allskewed_7_false P hskew ⟨x, y, hxy⟩

-- ═════════════════════════════════════════════════════════════════
-- §9. CORE EXTRACTION — Sub-FinPoset via order embedding
-- ═════════════════════════════════════════════════════════════════

/-- Restrict a FinPoset along an injective map. -/
def FinPoset.restrict (P : FinPoset n) (m : ℕ) (e : Fin m → Fin n)
    (he : Function.Injective e) : FinPoset m where
  le := fun a b ↦ P.le (e a) (e b)
  le_refl := fun a ↦ P.le_refl (e a)
  le_antisymm := fun a b hab hba ↦ he (P.le_antisymm _ _ hab hba)
  le_trans := fun a b c hab hbc ↦ P.le_trans _ _ _ hab hbc

/-- Incomparable pairs in the restriction correspond to incomparable pairs in P. -/
lemma restrict_incomp (P : FinPoset n) (m : ℕ) (e : Fin m → Fin n)
    (he : Function.Injective e) (a b : Fin m) :
    (P.restrict m e he).Incomp a b ↔ P.Incomp (e a) (e b) := by
  rfl

/-- If every element of the restriction is active, and P has AllSkewed,
    then the restriction inherits AllSkewed provided c and k agree. -/
lemma restrict_allskewed_of_ck (P : FinPoset n) (m : ℕ) (e : Fin m → Fin n)
    (he : Function.Injective e)
    (hskew : P.AllSkewed)
    (hk_eq : (P.restrict m e he).k = P.k)
    (hc_eq : ∀ a b : Fin m, (P.restrict m e he).c a b = P.c (e a) (e b)) :
    (P.restrict m e he).AllSkewed := by
  intro a b hab
  have hab' : P.Incomp (e a) (e b) := hab
  have h := hskew (e a) (e b) hab'
  unfold FinPoset.minority at h ⊢
  rw [hk_eq, hc_eq]; exact h

/-- **Injectivity of core restriction.** Two linear extensions of P that agree
    on the pairwise ordering of core elements are identical. -/
lemma linext_eq_of_core_agree (P : FinPoset n) (m : ℕ) (e : Fin m → Fin n)
    (he : Function.Injective e)
    (h_chain : ∀ x : Fin n, (∀ i : Fin m, e i ≠ x) → P.IsChainElem x)
    (σ₁ σ₂ : Perm (Fin n)) (hσ₁ : P.IsLinExt σ₁) (hσ₂ : P.IsLinExt σ₂)
    (h_agree : ∀ i j : Fin m, (σ₁.symm (e i)).val < (σ₁.symm (e j)).val ↔
                               (σ₂.symm (e i)).val < (σ₂.symm (e j)).val) :
    σ₁ = σ₂ := by
  have h_pos : ∀ x : Fin n, σ₁.symm x = σ₂.symm x := by
    intro x
    suffices h : (σ₁.symm x).val = (σ₂.symm x).val from Fin.ext h
    rw [← perm_rank_eq σ₁ x, ← perm_rank_eq σ₂ x]
    congr 1; ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hy : ∃ j : Fin m, e j = y <;> by_cases hx : ∃ i : Fin m, e i = x
    · obtain ⟨j, rfl⟩ := hy; obtain ⟨i, rfl⟩ := hx; exact h_agree j i
    · obtain ⟨j, rfl⟩ := hy; push_neg at hx
      rw [chain_elem_below_set P σ₁ hσ₁ x (h_chain x hx) (e j) (hx j),
          chain_elem_below_set P σ₂ hσ₂ x (h_chain x hx) (e j) (hx j)]
    · push_neg at hy; obtain ⟨i, rfl⟩ := hx
      have hne : y ≠ e i := Ne.symm (hy i)
      have hy_chain := h_chain y hy
      have h_iff : ∀ (σ : Perm (Fin n)), P.IsLinExt σ →
          ((σ.symm y).val < (σ.symm (e i)).val ↔ P.le y (e i)) := by
        intro σ hσ
        constructor
        · intro h_lt
          rcases hy_chain (e i) with heq | hle | hle
          · exact absurd heq hne
          · exact hle
          · exact absurd (hσ (e i) y hle) (not_le.mpr h_lt)
        · intro hle
          have h_ne_pos : (σ.symm y).val ≠ (σ.symm (e i)).val :=
            Fin.val_ne_of_ne (σ.symm.injective.ne hne)
          have h_not_gt : ¬((σ.symm (e i)).val < (σ.symm y).val) := by
            intro h_gt
            have := (chain_elem_below_set P σ hσ y hy_chain (e i) (Ne.symm hne)).mp h_gt
            exact hne (P.le_antisymm y (e i) hle this)
          omega
      rw [h_iff σ₁ hσ₁, h_iff σ₂ hσ₂]
    · push_neg at hy hx
      by_cases hxy : x = y
      · subst hxy; simp
      · rw [chain_elem_below_set P σ₁ hσ₁ x (h_chain x hx) y (Ne.symm hxy),
            chain_elem_below_set P σ₂ hσ₂ x (h_chain x hx) y (Ne.symm hxy)]
  have h_inv_eq : σ₁.symm = σ₂.symm := Equiv.ext h_pos
  rw [← Equiv.symm_symm σ₁, h_inv_eq, Equiv.symm_symm]

/-- The rank of e(i) among core elements. -/
noncomputable def core_rank (σ : Perm (Fin n)) (e : Fin m → Fin n) (i : Fin m) : Fin m :=
  ⟨(Finset.univ.filter fun j ↦ (σ.symm (e j)).val < (σ.symm (e i)).val).card,
   by
     have h_not_mem : i ∉ Finset.univ.filter fun j ↦ (σ.symm (e j)).val < (σ.symm (e i)).val := by
       simp [Finset.mem_filter, lt_irrefl]
     calc (Finset.univ.filter fun j ↦ (σ.symm (e j)).val < (σ.symm (e i)).val).card
         < (Finset.univ : Finset (Fin m)).card := Finset.card_lt_card
           ⟨Finset.filter_subset _ _, fun h => h_not_mem (h (Finset.mem_univ i))⟩
       _ = m := by rw [Finset.card_univ, Fintype.card_fin]⟩

/-- core_rank is injective. -/
lemma core_rank_injective (σ : Perm (Fin n)) (e : Fin m → Fin n)
    (he : Function.Injective e) : Function.Injective (core_rank σ e) := by
  intro i j h
  simp only [core_rank, Fin.mk.injEq] at h
  by_contra h_ne
  have h_pos_ne : (σ.symm (e i)).val ≠ (σ.symm (e j)).val :=
    Fin.val_ne_of_ne (σ.symm.injective.ne (he.ne h_ne))
  rcases lt_or_gt_of_ne h_pos_ne with h_lt | h_gt
  · have h_i_in_j : i ∈ Finset.univ.filter fun k ↦ (σ.symm (e k)).val < (σ.symm (e j)).val :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, h_lt⟩
    have h_i_not_i : i ∉ Finset.univ.filter fun k ↦ (σ.symm (e k)).val < (σ.symm (e i)).val :=
      by simp [Finset.mem_filter, lt_irrefl]
    have h_sub : Finset.univ.filter (fun k ↦ (σ.symm (e k)).val < (σ.symm (e i)).val) ⊆
        Finset.univ.filter (fun k ↦ (σ.symm (e k)).val < (σ.symm (e j)).val) := by
      intro k hk; simp only [Finset.mem_filter] at hk ⊢; exact ⟨hk.1, lt_trans hk.2 h_lt⟩
    have := Finset.card_lt_card ⟨h_sub, fun hsub => h_i_not_i (hsub h_i_in_j)⟩
    omega
  · have h_j_in_i : j ∈ Finset.univ.filter fun k ↦ (σ.symm (e k)).val < (σ.symm (e i)).val :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, h_gt⟩
    have h_j_not_j : j ∉ Finset.univ.filter fun k ↦ (σ.symm (e k)).val < (σ.symm (e j)).val :=
      by simp [Finset.mem_filter, lt_irrefl]
    have h_sub : Finset.univ.filter (fun k ↦ (σ.symm (e k)).val < (σ.symm (e j)).val) ⊆
        Finset.univ.filter (fun k ↦ (σ.symm (e k)).val < (σ.symm (e i)).val) := by
      intro k hk; simp only [Finset.mem_filter] at hk ⊢; exact ⟨hk.1, lt_trans hk.2 h_gt⟩
    have := Finset.card_lt_card ⟨h_sub, fun hsub => h_j_not_j (hsub h_j_in_i)⟩
    omega

/-- core_rank is surjective. -/
lemma core_rank_surjective (σ : Perm (Fin n)) (e : Fin m → Fin n)
    (he : Function.Injective e) : Function.Surjective (core_rank σ e) :=
  Finite.surjective_of_injective (core_rank_injective σ e he)

/-- The restriction permutation: projects σ to its action on core elements. -/
noncomputable def restrict_perm (σ : Perm (Fin n)) (e : Fin m → Fin n)
    (he : Function.Injective e) : Perm (Fin m) :=
  (Equiv.ofBijective (core_rank σ e)
    ⟨core_rank_injective σ e he, core_rank_surjective σ e he⟩).symm

/-- restrict_perm.symm = core_rank. -/
lemma restrict_perm_symm_eq (σ : Perm (Fin n)) (e : Fin m → Fin n)
    (he : Function.Injective e) (a : Fin m) :
    (restrict_perm σ e he).symm a = core_rank σ e a := by
  simp [restrict_perm]

/-- The restriction permutation preserves relative order of core elements. -/
lemma restrict_perm_order (σ : Perm (Fin n)) (e : Fin m → Fin n)
    (he : Function.Injective e) (i j : Fin m) :
    (σ.symm (e i)).val < (σ.symm (e j)).val ↔
    ((restrict_perm σ e he).symm i).val < ((restrict_perm σ e he).symm j).val := by
  rw [restrict_perm_symm_eq, restrict_perm_symm_eq]
  simp only [core_rank, Fin.val_mk]
  constructor
  · intro h_lt
    apply Finset.card_lt_card
    constructor
    · intro k hk; simp only [Finset.mem_filter] at hk ⊢; exact ⟨hk.1, lt_trans hk.2 h_lt⟩
    · intro h_sub
      have hi_in_j : i ∈ Finset.univ.filter fun k ↦ (σ.symm (e k)).val < (σ.symm (e j)).val :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, h_lt⟩
      have hi_not_i : i ∉ Finset.univ.filter fun k ↦ (σ.symm (e k)).val < (σ.symm (e i)).val := by
        simp [Finset.mem_filter, lt_irrefl]
      exact hi_not_i (h_sub hi_in_j)
  · intro h_rank_lt
    by_contra h_not_lt; push_neg at h_not_lt
    have h_pos_ne : (σ.symm (e i)).val ≠ (σ.symm (e j)).val :=
      Fin.val_ne_of_ne (σ.symm.injective.ne (he.ne (by
        intro h_eq; simp only [h_eq, lt_irrefl] at h_rank_lt)))
    have h_gt : (σ.symm (e j)).val < (σ.symm (e i)).val := by omega
    have h_rank_gt : (Finset.univ.filter fun k ↦ (σ.symm (e k)).val < (σ.symm (e j)).val).card <
        (Finset.univ.filter fun k ↦ (σ.symm (e k)).val < (σ.symm (e i)).val).card := by
      apply Finset.card_lt_card
      constructor
      · intro k hk; simp only [Finset.mem_filter] at hk ⊢; exact ⟨hk.1, lt_trans hk.2 h_gt⟩
      · intro h_sub
        have hj_in_i : j ∈ Finset.univ.filter fun k ↦ (σ.symm (e k)).val < (σ.symm (e i)).val :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, h_gt⟩
        have hj_not_j : j ∉ Finset.univ.filter fun k ↦ (σ.symm (e k)).val < (σ.symm (e j)).val := by
          simp [Finset.mem_filter, lt_irrefl]
        exact hj_not_j (h_sub hj_in_i)
    omega

/-- If σ is a linear extension of P, then restrict_perm σ is a linear extension of P_core. -/
lemma restrict_perm_linext (P : FinPoset n) (m : ℕ) (e : Fin m → Fin n)
    (he : Function.Injective e)
    (σ : Perm (Fin n)) (hσ : P.IsLinExt σ) :
    (P.restrict m e he).IsLinExt (restrict_perm σ e he) := by
  intro a b hab
  have h_pos_le := hσ (e a) (e b) hab
  rw [restrict_perm_symm_eq, restrict_perm_symm_eq]
  simp only [core_rank, Fin.val_mk]
  apply Finset.card_le_card
  intro k hk; simp only [Finset.mem_filter] at hk ⊢
  exact ⟨hk.1, lt_of_lt_of_le hk.2 h_pos_le⟩

/-- The restriction map on linear extensions is surjective. -/
lemma restrict_perm_surj (P : FinPoset n) (m : ℕ) (e : Fin m → Fin n)
    (he : Function.Injective e)
    (h_chain : ∀ x : Fin n, (∀ i : Fin m, e i ≠ x) → P.IsChainElem x)
    (τ : Perm (Fin m)) (hτ : (P.restrict m e he).IsLinExt τ) :
    ∃ σ : Perm (Fin n), P.IsLinExt σ ∧ restrict_perm σ e he = τ := by
  let bef (y x : Fin n) : Prop :=
    y ≠ x ∧
    ((∃ a b : Fin m, e a = y ∧ e b = x ∧ (τ.symm a).val < (τ.symm b).val) ∨
     (P.le y x ∧ ((∀ a : Fin m, e a ≠ y) ∨ (∀ b : Fin m, e b ≠ x))))
  have bef_of_Ple : ∀ y x, P.le y x → y ≠ x → bef y x := by
    intro y x hle hne; refine ⟨hne, ?_⟩
    by_cases hy : ∀ a : Fin m, e a ≠ y
    · right; exact ⟨hle, Or.inl hy⟩
    · by_cases hx : ∀ b : Fin m, e b ≠ x
      · right; exact ⟨hle, Or.inr hx⟩
      · push_neg at hy hx; obtain ⟨a, ha⟩ := hy; obtain ⟨b, hb⟩ := hx
        left; refine ⟨a, b, ha, hb, ?_⟩
        have hle' : P.le (e a) (e b) := by rw [ha, hb]; exact hle
        have hab_ne : a ≠ b := fun h ↦ hne (by rw [← ha, ← hb, h])
        exact lt_of_le_of_ne (hτ a b hle')
          (Fin.val_ne_of_ne (τ.symm.injective.ne hab_ne))
  have bef_total : ∀ y x, y ≠ x → bef y x ∨ bef x y := by
    intro y x hne
    by_cases hy : ∀ a : Fin m, e a ≠ y
    · rcases h_chain y hy x with heq | hle | hle
      · exact absurd heq hne
      · left; exact ⟨hne, Or.inr ⟨hle, Or.inl hy⟩⟩
      · right; exact bef_of_Ple x y hle hne.symm
    · push_neg at hy; obtain ⟨a, ha⟩ := hy
      by_cases hx : ∀ b : Fin m, e b ≠ x
      · rcases h_chain x hx y with heq | hle | hle
        · exact absurd heq.symm hne
        · right; exact ⟨hne.symm, Or.inr ⟨hle, Or.inl hx⟩⟩
        · left; exact bef_of_Ple y x hle hne
      · push_neg at hx; obtain ⟨b, hb⟩ := hx
        have hab_ne : a ≠ b := fun h ↦ hne (by rw [← ha, ← hb, h])
        rcases lt_or_gt_of_ne (Fin.val_ne_of_ne
          (τ.symm.injective.ne hab_ne)) with h | h
        · left; exact ⟨hne, Or.inl ⟨a, b, ha, hb, h⟩⟩
        · right; exact ⟨hne.symm, Or.inl ⟨b, a, hb, ha, h⟩⟩
  have bef_trans : ∀ z y x, bef z y → bef y x → bef z x := by
    intro z y x ⟨hzy_ne, hzy⟩ ⟨hyx_ne, hyx⟩
    have hzx_ne : z ≠ x := by
      intro heq; subst heq
      rcases hzy with ⟨a₁, b₁, ha₁, hb₁, h₁⟩ | ⟨hle₁, hor₁⟩
      · rcases hyx with ⟨a₂, b₂, ha₂, hb₂, h₂⟩ | ⟨_, hor₂⟩
        · have := he (hb₁.trans ha₂.symm); subst this
          have := he (ha₁.trans hb₂.symm); subst this; omega
        · rcases hor₂ with h | h
          · exact absurd hb₁ (h b₁)
          · exact absurd ha₁ (h a₁)
      · rcases hyx with ⟨a₂, b₂, ha₂, hb₂, _⟩ | ⟨hle₂, _⟩
        · rcases hor₁ with h | h
          · exact absurd hb₂ (h b₂)
          · exact absurd ha₂ (h a₂)
        · exact absurd (P.le_antisymm _ _ hle₁ hle₂) hzy_ne
    refine ⟨hzx_ne, ?_⟩
    rcases hzy with ⟨a₁, b₁, ha₁, hb₁, h₁⟩ | ⟨hle₁, hor₁⟩
    · rcases hyx with ⟨a₂, b₂, ha₂, hb₂, h₂⟩ | ⟨hle₂, hor₂⟩
      · have := he (hb₁.trans ha₂.symm); subst this
        exact Or.inl ⟨a₁, b₂, ha₁, hb₂, by omega⟩
      · have hx_nc : ∀ b : Fin m, e b ≠ x := by
          rcases hor₂ with h | h
          · exact absurd hb₁ (h b₁)
          · exact h
        rcases (h_chain x hx_nc) z with heq | hle | hle
        · exact absurd heq.symm hzx_ne
        · exfalso; have := hτ b₁ a₁ (show P.le (e b₁) (e a₁) by
            rw [hb₁, ha₁]; exact P.le_trans _ _ _ hle₂ hle); omega
        · exact Or.inr ⟨hle, Or.inr hx_nc⟩
    · rcases hyx with ⟨a₂, b₂, ha₂, hb₂, h₂⟩ | ⟨hle₂, hor₂⟩
      · have hz_nc : ∀ a : Fin m, e a ≠ z := by
          rcases hor₁ with h | h
          · exact h
          · exact absurd ha₂ (h a₂)
        rcases (h_chain z hz_nc) x with heq | hle | hle
        · exact absurd heq hzx_ne
        · exact Or.inr ⟨hle, Or.inl hz_nc⟩
        · exfalso; have := hτ b₂ a₂ (show P.le (e b₂) (e a₂) by
            rw [hb₂, ha₂]; exact P.le_trans _ _ _ hle hle₁); omega
      · by_cases hz : ∀ a : Fin m, e a ≠ z
        · exact Or.inr ⟨P.le_trans _ _ _ hle₁ hle₂, Or.inl hz⟩
        · by_cases hx : ∀ b : Fin m, e b ≠ x
          · exact Or.inr ⟨P.le_trans _ _ _ hle₁ hle₂, Or.inr hx⟩
          · push_neg at hz hx; obtain ⟨a, ha⟩ := hz; obtain ⟨b, hb⟩ := hx
            have hab : a ≠ b := fun h ↦ hzx_ne (by rw [← ha, ← hb, h])
            exact Or.inl ⟨a, b, ha, hb,
              lt_of_le_of_ne (hτ a b (show P.le (e a) (e b) by
                rw [ha, hb]; exact P.le_trans _ _ _ hle₁ hle₂))
                (Fin.val_ne_of_ne (τ.symm.injective.ne hab))⟩
  let rank (x : Fin n) : Fin n :=
    ⟨(Finset.univ.filter fun y ↦ bef y x).card, by
      have : x ∉ Finset.univ.filter fun y ↦ bef y x :=
        fun h ↦ (Finset.mem_filter.mp h).2.1 rfl
      calc _ < Finset.univ.card := Finset.card_lt_card
            ⟨Finset.filter_subset _ _, fun h ↦ this (h (Finset.mem_univ x))⟩
        _ = n := by rw [Finset.card_univ, Fintype.card_fin]⟩
  have bef_ssubset : ∀ (a b : Fin n), bef a b →
      (Finset.univ.filter fun y : Fin n ↦ bef y a) ⊂
      (Finset.univ.filter fun y : Fin n ↦ bef y b) := by
    intro a b hab
    exact ⟨fun y hy ↦ Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        bef_trans _ _ _ (Finset.mem_filter.mp hy).2 hab⟩,
      fun hsub ↦ (fun h ↦ (Finset.mem_filter.mp h).2.1 rfl)
        (hsub (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hab⟩))⟩
  have rank_inj : Function.Injective rank := by
    intro x₁ x₂ h_eq; by_contra h_ne
    rcases bef_total x₁ x₂ h_ne with h | h <;> {
      have h_lt := Finset.card_lt_card (bef_ssubset _ _ h)
      simp only [rank, Fin.mk.injEq] at h_eq; omega }
  let σ : Perm (Fin n) :=
    (Equiv.ofBijective rank ⟨rank_inj, Finite.surjective_of_injective rank_inj⟩).symm
  refine ⟨σ, ?_, ?_⟩
  · intro a b hab
    show ((Equiv.ofBijective rank ⟨rank_inj,
      Finite.surjective_of_injective rank_inj⟩) a).val ≤
      ((Equiv.ofBijective rank ⟨rank_inj,
      Finite.surjective_of_injective rank_inj⟩) b).val
    simp only [Equiv.ofBijective_apply]
    show (rank a).val ≤ (rank b).val
    simp only [rank]
    by_cases hab_eq : a = b
    · subst hab_eq; exact Nat.le_refl _
    · exact Nat.le_of_lt_succ (Nat.lt_succ_of_lt (Finset.card_lt_card
        (bef_ssubset _ _ (bef_of_Ple a b hab hab_eq))))
  · have h_eq_symm : ∀ i, (restrict_perm σ e he).symm i = τ.symm i := by
      intro i; rw [restrict_perm_symm_eq]; apply Fin.ext
      simp only [core_rank, Fin.val_mk]
      have h_filter : ∀ j : Fin m,
          (σ.symm (e j)).val < (σ.symm (e i)).val ↔
          (τ.symm j).val < (τ.symm i).val := by
        intro j
        show (rank (e j)).val < (rank (e i)).val ↔ _
        by_cases hji : j = i
        · subst hji; simp
        · constructor
          · intro h_lt
            have hne : e j ≠ e i := he.ne hji
            rcases bef_total (e j) (e i) hne with hb | hb
            · rcases hb.2 with ⟨a, b, ha, hb', hab⟩ | ⟨_, hor⟩
              · exact he ha.symm ▸ he hb'.symm ▸ hab
              · rcases hor with h | h
                · exact absurd rfl (h j)
                · exact absurd rfl (h i)
            · exact absurd h_lt (not_lt.mpr (Nat.le_of_lt_succ (Nat.lt_succ_of_lt
                (Finset.card_lt_card (bef_ssubset _ _ hb)))))
          · intro h_lt
            have hbef : bef (e j) (e i) :=
              ⟨he.ne hji, Or.inl ⟨j, i, rfl, rfl, h_lt⟩⟩
            exact Finset.card_lt_card (bef_ssubset _ _ hbef)
      rw [show (Finset.univ.filter fun j : Fin m ↦
            (σ.symm (e j)).val < (σ.symm (e i)).val) =
          (Finset.univ.filter fun j : Fin m ↦
            (τ.symm j).val < (τ.symm i).val) from
          Finset.filter_congr (fun j _ ↦ h_filter j)]
      have h_card_eq : (Finset.univ.filter fun j : Fin m ↦
            (τ.symm j).val < (τ.symm i).val).card =
          (Finset.range ((τ.symm i).val)).card :=
        Finset.card_bij (fun j _ ↦ (τ.symm j).val)
          (fun j hj ↦ Finset.mem_range.mpr (Finset.mem_filter.mp hj).2)
          (fun j₁ _ j₂ _ h ↦ τ.symm.injective (Fin.ext h))
          (fun v hv ↦ ⟨τ ⟨v, by
              have := Finset.mem_range.mp hv; have := (τ.symm i).isLt; omega⟩,
            Finset.mem_filter.mpr ⟨Finset.mem_univ _,
              by simp [Equiv.symm_apply_apply]; exact Finset.mem_range.mp hv⟩,
            by simp [Equiv.symm_apply_apply]⟩)
      rw [h_card_eq, Finset.card_range]
    calc restrict_perm σ e he
        = (restrict_perm σ e he).symm.symm := (Equiv.symm_symm _).symm
      _ = τ.symm.symm := by rw [Equiv.ext h_eq_symm]
      _ = τ := Equiv.symm_symm _

/-- **Linear extension bijection for core restriction.** -/
theorem core_k_eq (P : FinPoset n) (m : ℕ) (e : Fin m → Fin n)
    (he : Function.Injective e)
    (h_active_range : ∀ x : Fin n, P.IsActiveElem x → ∃ i : Fin m, e i = x)
    (h_chain_complement : ∀ x : Fin n, (∀ i : Fin m, e i ≠ x) → P.IsChainElem x) :
    (P.restrict m e he).k = P.k := by
  unfold FinPoset.k FinPoset.linExts; symm
  exact Finset.card_bij (fun σ _ ↦ restrict_perm σ e he)
    (fun σ hσ ↦ by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
      exact restrict_perm_linext P m e he σ hσ)
    (fun σ₁ hσ₁ σ₂ hσ₂ h_eq ↦ by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ₁ hσ₂
      have h_eq' : restrict_perm σ₁ e he = restrict_perm σ₂ e he := h_eq
      exact linext_eq_of_core_agree P m e he h_chain_complement σ₁ σ₂ hσ₁ hσ₂
        fun i j ↦ by
          have h1 := restrict_perm_order σ₁ e he i j
          have h2 := restrict_perm_order σ₂ e he i j
          rw [h_eq'] at h1; exact h1.trans h2.symm)
    (fun τ hτ ↦ by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hτ
      obtain ⟨σ, hσ, hfσ⟩ := restrict_perm_surj P m e he h_chain_complement τ hτ
      exact ⟨σ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hσ⟩, hfσ⟩)

/-- c values are preserved by core restriction. -/
theorem core_c_eq (P : FinPoset n) (m : ℕ) (e : Fin m → Fin n)
    (he : Function.Injective e)
    (h_active_range : ∀ x : Fin n, P.IsActiveElem x → ∃ i : Fin m, e i = x)
    (h_chain_complement : ∀ x : Fin n, (∀ i : Fin m, e i ≠ x) → P.IsChainElem x)
    (a b : Fin m) :
    (P.restrict m e he).c a b = P.c (e a) (e b) := by
  unfold FinPoset.c FinPoset.linExts; simp only [Finset.filter_filter]; symm
  exact Finset.card_bij (fun σ _ ↦ restrict_perm σ e he)
    (fun σ hσ ↦ by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
      exact ⟨restrict_perm_linext P m e he σ hσ.1,
        (restrict_perm_order σ e he a b).mp hσ.2⟩)
    (fun σ₁ hσ₁ σ₂ hσ₂ h_eq ↦ by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ₁ hσ₂
      have h_eq' : restrict_perm σ₁ e he = restrict_perm σ₂ e he := h_eq
      exact linext_eq_of_core_agree P m e he h_chain_complement σ₁ σ₂ hσ₁.1 hσ₂.1
        fun i j ↦ by
          have h1 := restrict_perm_order σ₁ e he i j
          have h2 := restrict_perm_order σ₂ e he i j
          rw [h_eq'] at h1; exact h1.trans h2.symm)
    (fun τ hτ ↦ by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hτ
      obtain ⟨σ, hσ, hfσ⟩ := restrict_perm_surj P m e he h_chain_complement τ hτ.1
      refine ⟨σ, ?_, hfσ⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨hσ, (restrict_perm_order σ e he a b).mpr ?_⟩
      rw [hfσ]; exact hτ.2)

/-- **Core extraction theorem (structural).** -/
theorem core_extraction (P : FinPoset n) (hskew : P.AllSkewed) (hk : P.k ≥ 10) :
    ∃ (m : ℕ) (e : Fin m → Fin n) (he : Function.Injective e),
      (∀ x : Fin m, (P.restrict m e he).IsActiveElem x) ∧
      (P.restrict m e he).AllSkewed ∧
      (P.restrict m e he).k ≥ 10 := by
  set A := {x : Fin n // P.IsActiveElem x}
  set m := Fintype.card A with hm_def
  have hNC : P.NonChain := by
    by_contra h_chain
    unfold FinPoset.NonChain at h_chain; push_neg at h_chain
    have h_all_chain : ∀ x : Fin n, P.IsChainElem x := by
      intro x y
      by_cases hxy : x = y
      · left; exact hxy
      · have := h_chain x y; unfold FinPoset.Incomp at this; push_neg at this
        by_cases hle : P.le x y
        · right; left; exact hle
        · right; right; exact this hle
    have hk_le1 : P.k ≤ 1 := by
      unfold FinPoset.k FinPoset.linExts; rw [Finset.card_le_one]
      intro σ₁ hσ₁ σ₂ hσ₂
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ₁ hσ₂
      have h_inv : σ₁.symm = σ₂.symm := by
        ext x; exact congr_arg Fin.val
          (chain_elem_position_unique P σ₁ σ₂ hσ₁ hσ₂ x (h_all_chain x))
      rw [← Equiv.symm_symm σ₁, h_inv, Equiv.symm_symm]
    omega
  let equiv := (Fintype.equivFin A).symm
  let e : Fin m → Fin n := fun i ↦ (equiv i).val
  have he : Function.Injective e := by
    intro a b hab; exact equiv.injective (Subtype.ext hab)
  have h_active_range : ∀ x : Fin n, P.IsActiveElem x → ∃ i : Fin m, e i = x := by
    intro x hx
    exact ⟨(Fintype.equivFin A) ⟨x, hx⟩, by simp [e, equiv, Equiv.symm_apply_apply]⟩
  have h_chain_complement : ∀ x : Fin n, (∀ i : Fin m, e i ≠ x) → P.IsChainElem x := by
    intro x hx_not_in
    by_contra h_not_chain
    unfold FinPoset.IsChainElem at h_not_chain; push_neg at h_not_chain
    obtain ⟨y, hne, hxy, hyx⟩ := h_not_chain
    have hx_active : P.IsActiveElem x := ⟨y, ⟨hxy, hyx⟩⟩
    obtain ⟨i, hi⟩ := h_active_range x hx_active
    exact hx_not_in i hi
  refine ⟨m, e, he, ?_, ?_, ?_⟩
  · intro x
    have hx_active : P.IsActiveElem (e x) := (equiv x).prop
    obtain ⟨z, hz⟩ := hx_active
    have hz_active : P.IsActiveElem z := ⟨e x, ⟨hz.2, hz.1⟩⟩
    obtain ⟨y, hy⟩ := h_active_range z hz_active
    refine ⟨y, ?_⟩; rw [restrict_incomp, hy]; exact hz
  · exact restrict_allskewed_of_ck P m e he hskew
      (core_k_eq P m e he h_active_range h_chain_complement)
      (core_c_eq P m e he h_active_range h_chain_complement)
  · rw [core_k_eq P m e he h_active_range h_chain_complement]; exact hk

end Kislitsyn
