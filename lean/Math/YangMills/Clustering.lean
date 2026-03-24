import Mathlib.GroupTheory.Perm.Basic
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Data.Fintype.Perm
import Mathlib.Tactic.Push
import Mathlib.Tactic.ByCases
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Linarith
import Mathlib.Order.Extension.Linear

/-!
# Zero Correlation of Isolated Pairs

## Main Result

**Theorem (zero_correlation_of_isolated):**
Let P be a finite poset on Fin n, and x ∥ y incomparable elements.
If every other element z is incomparable to both x and y, then
  2 * c(x,y) = k
i.e. c(x,y) = c(y,x) = k/2.

## Proof Strategy

1. Define posSwap σ x y = σ ∘ swap(σ⁻¹(x), σ⁻¹(y)). This swaps the
   positions of x and y in σ.
2. posSwap is an involution: posSwap(posSwap(σ)) = σ.
3. If x ∥ y and all other elements z are incomparable to both x and y,
   then posSwap preserves the linext property.
4. posSwap maps {σ : x <_σ y} bijectively to {σ : y <_σ x}.
5. c(x,y) + c(y,x) = k.
6. Therefore 2 * c(x,y) = k.

## Sorry Inventory

- 0 sorrys (fully proved)
-/

set_option linter.style.openClassical false
open scoped Classical
open Finset Equiv

namespace YangMillsClustering

-- ═══════════════════════════════════════════════════════════════
-- §1. STANDALONE FINPOSET DEFINITION
-- ═══════════════════════════════════════════════════════════════

/-- A finite poset on n labeled elements.
    Self-contained copy (no imports from Kislitsyn). -/
structure FinPoset (n : ℕ) where
  le : Fin n → Fin n → Prop
  le_refl     : ∀ a, le a a
  le_antisymm : ∀ a b, le a b → le b a → a = b
  le_trans    : ∀ a b c, le a b → le b c → le a c

variable {n : ℕ}

/-- Incomparability: neither a ≤ b nor b ≤ a -/
def FinPoset.Incomp (P : FinPoset n) (x y : Fin n) : Prop :=
  ¬P.le x y ∧ ¬P.le y x

/-- σ is a linear extension of P.
    σ maps positions → elements, so σ.symm maps elements → positions.
    Condition: a ≤_P b  →  pos(a) ≤ pos(b). -/
def FinPoset.IsLinExt (P : FinPoset n) (σ : Perm (Fin n)) : Prop :=
  ∀ a b, P.le a b → (σ.symm a).val ≤ (σ.symm b).val

/-- L(P) = the finite set of all linear extensions -/
noncomputable def FinPoset.linExts (P : FinPoset n) : Finset (Perm (Fin n)) :=
  Finset.univ.filter P.IsLinExt

/-- k = |L(P)| -/
noncomputable def FinPoset.k (P : FinPoset n) : ℕ :=
  P.linExts.card

/-- c(x,y) = |{σ ∈ L(P) : x appears strictly before y in σ}| -/
noncomputable def FinPoset.c (P : FinPoset n) (x y : Fin n) : ℕ :=
  (P.linExts.filter fun σ ↦ (σ.symm x).val < (σ.symm y).val).card

/-- Incomparable elements are distinct. -/
lemma FinPoset.Incomp.ne {P : FinPoset n} {x y : Fin n}
    (h : P.Incomp x y) : x ≠ y := by
  intro heq; subst heq; exact h.1 (P.le_refl x)

-- ═══════════════════════════════════════════════════════════════
-- §2. c_complement: c(x,y) + c(y,x) = k
-- ═══════════════════════════════════════════════════════════════

/-- c(x,y) + c(y,x) = k for distinct elements. -/
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

-- ═══════════════════════════════════════════════════════════════
-- §3. posSwap DEFINITION AND INVOLUTION
-- ═══════════════════════════════════════════════════════════════

/-- posSwap σ x y swaps the positions of x and y in σ.
    Formally: σ * swap(σ⁻¹(x), σ⁻¹(y)). -/
noncomputable def posSwap (σ : Perm (Fin n)) (x y : Fin n) : Perm (Fin n) :=
  σ * Equiv.swap (σ.symm x) (σ.symm y)

/-- posSwap is an involution. -/
lemma posSwap_involution (σ : Perm (Fin n)) (x y : Fin n) :
    posSwap (posSwap σ x y) x y = σ := by
  unfold posSwap
  set sw := Equiv.swap (σ.symm x) (σ.symm y) with hsw_def
  set σ' := σ * sw
  -- σ'⁻¹(x) = sw(σ⁻¹(x)) = σ⁻¹(y)
  have hsx : σ'.symm x = σ.symm y := by
    simp [σ', Equiv.Perm.mul_def, Equiv.symm_trans_apply, hsw_def,
      Equiv.symm_swap, Equiv.swap_apply_left]
  -- σ'⁻¹(y) = sw(σ⁻¹(y)) = σ⁻¹(x)
  have hsy : σ'.symm y = σ.symm x := by
    simp [σ', Equiv.Perm.mul_def, Equiv.symm_trans_apply, hsw_def,
      Equiv.symm_swap, Equiv.swap_apply_right]
  -- swap(σ'⁻¹(x), σ'⁻¹(y)) = swap(σ⁻¹(y), σ⁻¹(x)) = swap(σ⁻¹(x), σ⁻¹(y)) = sw
  rw [hsx, hsy]
  have hsw_comm : Equiv.swap (σ.symm y) (σ.symm x) = sw := Equiv.swap_comm _ _
  rw [hsw_comm]
  -- σ' * sw = (σ * sw) * sw = σ * (sw * sw) = σ * 1 = σ
  show σ * sw * sw = σ
  rw [mul_assoc]
  simp [hsw_def, Equiv.swap_mul_self]

/-- posSwap swaps the positions of x and y. -/
lemma posSwap_symm_x (σ : Perm (Fin n)) (x y : Fin n) :
    (posSwap σ x y).symm x = σ.symm y := by
  simp [posSwap, Equiv.Perm.mul_def, Equiv.symm_trans_apply,
    Equiv.symm_swap, Equiv.swap_apply_left]

lemma posSwap_symm_y (σ : Perm (Fin n)) (x y : Fin n) :
    (posSwap σ x y).symm y = σ.symm x := by
  simp [posSwap, Equiv.Perm.mul_def, Equiv.symm_trans_apply,
    Equiv.symm_swap, Equiv.swap_apply_right]

lemma posSwap_symm_other (σ : Perm (Fin n)) (x y z : Fin n)
    (hzx : z ≠ x) (hzy : z ≠ y) :
    (posSwap σ x y).symm z = σ.symm z := by
  simp [posSwap, Equiv.Perm.mul_def, Equiv.symm_trans_apply, Equiv.symm_swap]
  rw [Equiv.swap_apply_of_ne_of_ne]
  · intro h; exact hzx (σ.symm.injective h)
  · intro h; exact hzy (σ.symm.injective h)

-- ═══════════════════════════════════════════════════════════════
-- §4. ISOLATED PAIR: posSwap PRESERVES LINEXT
-- ═══════════════════════════════════════════════════════════════

/-- All other elements are incomparable to both x and y. -/
def Isolated (P : FinPoset n) (x y : Fin n) : Prop :=
  P.Incomp x y ∧
  ∀ z : Fin n, z ≠ x → z ≠ y → P.Incomp z x ∧ P.Incomp z y

/-- If (x,y) is an isolated pair, posSwap preserves the linext property. -/
lemma posSwap_linext_of_isolated (P : FinPoset n)
    (x y : Fin n) (hiso : Isolated P x y)
    (σ : Perm (Fin n)) (hσ : P.IsLinExt σ) :
    P.IsLinExt (posSwap σ x y) := by
  -- Key insight: for an isolated pair, P.le a b can only hold when
  -- a, b ∉ {x, y} (isolation kills all other constraints).
  -- In that case posSwap acts as identity on positions of a and b.
  intro a b hab
  -- If a or b ∈ {x,y}, we derive contradiction from isolation.
  by_cases hax : a = x
  · by_cases hbx : b = x
    · simp [hax, hbx]
    · by_cases hby : b = y
      · rw [hax, hby] at hab; exact absurd hab hiso.1.1
      · rw [hax] at hab; exact absurd hab ((hiso.2 b hbx hby).1).2
  · by_cases hay : a = y
    · by_cases hbx : b = x
      · rw [hay, hbx] at hab; exact absurd hab hiso.1.2
      · by_cases hby : b = y
        · simp [hay, hby]
        · rw [hay] at hab; exact absurd hab ((hiso.2 b hbx hby).2).2
    · by_cases hbx : b = x
      · rw [hbx] at hab; exact absurd hab ((hiso.2 a hax hay).1).1
      · by_cases hby : b = y
        · rw [hby] at hab; exact absurd hab ((hiso.2 a hax hay).2).1
        · -- a, b ∉ {x,y}: posSwap is identity on their positions
          rw [posSwap_symm_other σ x y a hax hay,
              posSwap_symm_other σ x y b hbx hby]
          exact hσ a b hab

-- ═══════════════════════════════════════════════════════════════
-- §5. posSwap MAPS c(x,y)-SET TO c(y,x)-SET BIJECTIVELY
-- ═══════════════════════════════════════════════════════════════

/-- posSwap flips the relative order of x and y. -/
lemma posSwap_flips_order (σ : Perm (Fin n)) (x y : Fin n) :
    (posSwap σ x y).symm x = σ.symm y ∧
    (posSwap σ x y).symm y = σ.symm x :=
  ⟨posSwap_symm_x σ x y, posSwap_symm_y σ x y⟩

/-- If x <_σ y, then y <_{posSwap σ} x. -/
lemma posSwap_reverses_xy (σ : Perm (Fin n)) (x y : Fin n)
    (hlt : (σ.symm x).val < (σ.symm y).val) :
    ((posSwap σ x y).symm y).val < ((posSwap σ x y).symm x).val := by
  rw [posSwap_symm_x, posSwap_symm_y]
  exact hlt

/-- posSwap sends linExts to linExts for isolated pairs. -/
lemma posSwap_mem_linExts_of_isolated (P : FinPoset n) (x y : Fin n)
    (hiso : Isolated P x y) (σ : Perm (Fin n)) (hσ : σ ∈ P.linExts) :
    posSwap σ x y ∈ P.linExts := by
  simp only [FinPoset.linExts, Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
  exact posSwap_linext_of_isolated P x y hiso σ hσ

-- ═══════════════════════════════════════════════════════════════
-- §6. c(x,y) = c(y,x) VIA BIJECTION
-- ═══════════════════════════════════════════════════════════════

/-- posSwap is an injection from {σ : x <_σ y} to {σ : y <_σ x}. -/
lemma c_eq_of_isolated (P : FinPoset n) (x y : Fin n) (hiso : Isolated P x y) :
    P.c x y = P.c y x := by
  unfold FinPoset.c
  -- Define the two filter sets
  set Sxy := P.linExts.filter fun σ ↦ (σ.symm x).val < (σ.symm y).val with hSxy_def
  set Syx := P.linExts.filter fun σ ↦ (σ.symm y).val < (σ.symm x).val with hSyx_def
  -- posSwap is a bijection from Sxy to Syx
  -- We use Finset.card_bij
  apply Finset.card_bij (fun σ _ ↦ posSwap σ x y)
  · -- posSwap maps Sxy into Syx
    intro σ hσ
    simp only [hSxy_def, Finset.mem_filter] at hσ
    simp only [hSyx_def, Finset.mem_filter]
    exact ⟨posSwap_mem_linExts_of_isolated P x y hiso σ hσ.1,
           posSwap_reverses_xy σ x y hσ.2⟩
  · -- posSwap is injective (follows from involution)
    intro σ₁ hσ₁ σ₂ hσ₂ heq
    have h1 := posSwap_involution σ₁ x y
    have h2 := posSwap_involution σ₂ x y
    rw [heq] at h1; rw [h2] at h1; exact h1.symm
  · -- posSwap is surjective (given τ ∈ Syx, posSwap τ x y ∈ Sxy maps to τ)
    intro τ hτ
    simp only [hSyx_def, Finset.mem_filter] at hτ
    refine ⟨posSwap τ x y, ?_, posSwap_involution τ x y⟩
    simp only [hSxy_def, Finset.mem_filter]
    constructor
    · exact posSwap_mem_linExts_of_isolated P x y hiso τ hτ.1
    · -- τ has y <_τ x, so posSwap τ has x <_{posSwap τ} y
      rw [posSwap_symm_x, posSwap_symm_y]
      exact hτ.2

-- ═══════════════════════════════════════════════════════════════
-- §7. MAIN THEOREM
-- ═══════════════════════════════════════════════════════════════

/-- **Zero Correlation of Isolated Pairs.**

If x ∥ y and every other element z is incomparable to both x and y,
then 2 * c(x,y) = k.

Proof: c(x,y) = c(y,x) by the posSwap bijection, and
c(x,y) + c(y,x) = k by complement counting.
Therefore 2 * c(x,y) = k. -/
theorem zero_correlation_of_isolated (P : FinPoset n) (x y : Fin n)
    (hiso : Isolated P x y) :
    2 * P.c x y = P.k := by
  have hcxy_eq : P.c x y = P.c y x := c_eq_of_isolated P x y hiso
  have hcomp : P.c x y + P.c y x = P.k :=
    c_complement P x y hiso.1.ne
  linarith

end YangMillsClustering
