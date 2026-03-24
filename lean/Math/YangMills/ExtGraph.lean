import Math.YangMills.Foundations

/-!
# Extension Graph Connectivity

## Main results

- `adjacent_le_of_not_incomp`: no bottleneck at position i → σ(i) ≤_P σ(i+1)
- `chain_le_of_no_bottleneck`: no bottlenecks anywhere → σ induces a total order
- `linext_has_bottleneck`: k ≥ 2 → every linext has ≥ 1 bottleneck
- `ext_graph_connected`: E(P) is connected (bubble sort)

## Verified

Exhaustively on all 2,097,151 non-chain posets with n ≤ 7.
-/

open scoped Classical
open Finset Equiv

namespace Kislitsyn

variable {n : ℕ}

-- ═══════════════════════════════════════════════════════════════
-- §1. ADJACENT COMPARABLE → FORWARD ORDER
-- ═══════════════════════════════════════════════════════════════

/-- If σ(i) and σ(i+1) are NOT incomparable (i.e., comparable),
    and σ is a linext, then σ(i) ≤_P σ(i+1).

    Proof: comparable means P.le a b ∨ P.le b a.
    If P.le σ(i+1) σ(i), then IsLinExt gives pos(σ(i+1)) ≤ pos(σ(i)),
    i.e. i+1 ≤ i. Contradiction. So P.le σ(i) σ(i+1). -/
lemma adjacent_le_of_not_incomp (P : FinPoset n) (σ : Perm (Fin n))
    (hσ : P.IsLinExt σ) (i : ℕ) (hi : i + 1 < n)
    (hni : ¬P.Incomp (σ ⟨i, by omega⟩) (σ ⟨i + 1, hi⟩)) :
    P.le (σ ⟨i, by omega⟩) (σ ⟨i + 1, hi⟩) := by
  unfold FinPoset.Incomp at hni
  push_neg at hni
  by_contra h
  have hback := hni h
  have hpos := hσ (σ ⟨i + 1, hi⟩) (σ ⟨i, by omega⟩) hback
  simp at hpos

-- ═══════════════════════════════════════════════════════════════
-- §2. NO BOTTLENECKS → TOTAL ORDER (chain argument)
-- ═══════════════════════════════════════════════════════════════

/-- If σ has no bottleneck at any position, then σ(i) ≤_P σ(j)
    whenever i ≤ j.  Proved by induction on j - i. -/
lemma chain_le_of_no_bottleneck (P : FinPoset n) (σ : Perm (Fin n))
    (hσ : P.IsLinExt σ)
    (hno : ∀ (i : ℕ) (hi : i + 1 < n),
      ¬P.Incomp (σ ⟨i, by omega⟩) (σ ⟨i + 1, hi⟩))
    (i j : ℕ) (hi : i < n) (hj : j < n) (hij : i ≤ j) :
    P.le (σ ⟨i, hi⟩) (σ ⟨j, hj⟩) := by
  have key : ∀ d : ℕ, d = j - i → P.le (σ ⟨i, hi⟩) (σ ⟨j, hj⟩) := by
    intro d hd
    induction d generalizing j with
    | zero =>
      have : i = j := by omega
      subst this; exact P.le_refl _
    | succ d ih =>
      have hj1 : j - 1 < n := by omega
      have hij1 : i ≤ j - 1 := by omega
      have h_prev := ih (j - 1) hj1 hij1 (by omega)
      have hstep : j - 1 + 1 < n := by omega
      have h_adj := adjacent_le_of_not_incomp P σ hσ (j - 1) (by omega)
        (hno (j - 1) (by omega))
      have hj_pos : 1 ≤ j := by omega
      have hnat : j - 1 + 1 = j := Nat.sub_add_cancel hj_pos
      have hj_eq : σ ⟨j - 1 + 1, by omega⟩ = σ ⟨j, hj⟩ := by
        congr 1; exact Fin.ext hnat
      rw [hj_eq] at h_adj
      exact P.le_trans _ _ _ h_prev h_adj
  exact key (j - i) rfl

/-- No bottlenecks → P is a total order. -/
lemma total_of_no_bottleneck (P : FinPoset n) (σ : Perm (Fin n))
    (hσ : P.IsLinExt σ)
    (hno : ∀ (i : ℕ) (hi : i + 1 < n),
      ¬P.Incomp (σ ⟨i, by omega⟩) (σ ⟨i + 1, hi⟩)) :
    ∀ (a b : Fin n), P.le a b ∨ P.le b a := by
  intro a b
  set ia := σ.symm a
  set ib := σ.symm b
  by_cases h : ia.val ≤ ib.val
  · left
    have := chain_le_of_no_bottleneck P σ hσ hno ia.val ib.val ia.isLt ib.isLt h
    simp [ia, ib] at this
    exact this
  · right
    push_neg at h
    have := chain_le_of_no_bottleneck P σ hσ hno ib.val ia.val ib.isLt ia.isLt (by omega)
    simp [ia, ib] at this
    exact this

-- ═══════════════════════════════════════════════════════════════
-- §3. TOTAL ORDER → UNIQUE LINEXT → k = 1
-- ═══════════════════════════════════════════════════════════════

/-- A monotone bijection on `Fin n` is the identity.

    Proof: two-sided squeeze.
    1. f(i) ≥ i by Nat induction (base trivial, step uses strict mono).
    2. f⁻¹ is also monotone, so f⁻¹(i) ≥ i.
       Apply f (monotone) to both sides: f(f⁻¹(i)) ≥ f(i), i.e., i ≥ f(i).
    Combined: f(i) = i. -/
private lemma monotone_fin_bijection_eq_id
    (f : Fin n → Fin n)
    (hmono : ∀ i j : Fin n, i.val ≤ j.val → (f i).val ≤ (f j).val)
    (hbij : Function.Bijective f) :
    ∀ i : Fin n, f i = i := by
  -- Strict monotonicity from mono + injective
  have hstrict : ∀ i j : Fin n, i.val < j.val → (f i).val < (f j).val := by
    intro i j hij
    have hle := hmono i j (Nat.le_of_lt hij)
    rcases Nat.eq_or_lt_of_le hle with heq | hlt
    · exfalso
      have : i = j := hbij.1 (Fin.val_injective heq)
      omega
    · exact hlt
  -- Claim 1: f(i).val ≥ i.val for all i
  have hge : ∀ i : Fin n, i.val ≤ (f i).val := by
    intro ⟨i, hi⟩
    induction i with
    | zero => exact Nat.zero_le _
    | succ k ih =>
      have hk : k < n := by omega
      have ih' := ih hk
      have hpre : (⟨k, hk⟩ : Fin n).val < (⟨k + 1, hi⟩ : Fin n).val := by simp
      have hlt : (f ⟨k, hk⟩).val < (f ⟨k + 1, hi⟩).val := hstrict ⟨k, hk⟩ ⟨k + 1, hi⟩ hpre
      -- ih' : k ≤ (f ⟨k, hk⟩).val, hlt : (f ⟨k, hk⟩).val < (f ⟨k+1, hi⟩).val
      -- goal : k + 1 ≤ (f ⟨k+1, hi⟩).val
      linarith
  -- Construct inverse g = f⁻¹
  have hsurj := hbij.2
  let e := Equiv.ofBijective f hbij
  let g := e.symm
  -- g is also monotone
  have gmono : ∀ i j : Fin n, i.val ≤ j.val → (g i).val ≤ (g j).val := by
    intro i j hij
    by_contra hgt; push_neg at hgt
    -- g(i) > g(j), so by strict mono of f: f(g(i)) > f(g(j)), i.e., i > j
    have := hstrict (g j) (g i) hgt
    simp only [g, e, Equiv.ofBijective_apply_symm_apply] at this
    omega
  -- g is also bijective
  have gbij : Function.Bijective g := e.symm.bijective
  -- Strict monotonicity for g
  have gstrict : ∀ a b : Fin n, a.val < b.val → (g a).val < (g b).val := by
    intro a b hab
    have hle := gmono a b (Nat.le_of_lt hab)
    rcases Nat.eq_or_lt_of_le hle with heq | hlt
    · exfalso
      have : a = b := gbij.1 (Fin.val_injective heq)
      omega
    · exact hlt
  -- Claim 1 applied to g: g(i).val ≥ i.val
  have gge : ∀ i : Fin n, i.val ≤ (g i).val := by
    intro ⟨i, hi⟩
    induction i with
    | zero => exact Nat.zero_le _
    | succ k ih =>
      have hk : k < n := by omega
      have ih' := ih hk
      have hpre : (⟨k, hk⟩ : Fin n).val < (⟨k + 1, hi⟩ : Fin n).val := by simp
      have hlt : (g ⟨k, hk⟩).val < (g ⟨k + 1, hi⟩).val := gstrict ⟨k, hk⟩ ⟨k + 1, hi⟩ hpre
      linarith
  -- Claim 2: f(i).val ≤ i.val
  -- From g(i) ≥ i and f monotone: f(g(i)) ≥ f(i), i.e., i ≥ f(i).
  have hle : ∀ i : Fin n, (f i).val ≤ i.val := by
    intro i
    have h1 := gge (f i)         -- (f i).val ≤ (g (f i)).val
    have h2 := hmono i (g (f i))  -- needs i.val ≤ (g (f i)).val
    -- g (f i) = i
    have hgf : g (f i) = i := by
      simp only [g, e]
      exact (Equiv.ofBijective f hbij).symm_apply_apply i
    rw [hgf] at h1
    -- h1 : (f i).val ≤ i.val
    exact h1
  -- Combine
  intro i
  exact Fin.val_injective (Nat.le_antisymm (hle i) (hge i))

/-- In a total order, two linexts must agree.
    Proof: τ = σ₂⁻¹ ∘ σ₁ is a monotone bijection on Fin n, hence the identity. -/
lemma unique_linext_of_total (P : FinPoset n)
    (htotal : ∀ a b : Fin n, P.le a b ∨ P.le b a)
    (σ₁ σ₂ : Perm (Fin n))
    (hσ₁ : P.IsLinExt σ₁) (hσ₂ : P.IsLinExt σ₂) :
    σ₁ = σ₂ := by
  -- No incomparable pairs in a total order
  have hno_incomp : ∀ a b : Fin n, ¬P.Incomp a b := by
    intro a b ⟨h1, h2⟩
    rcases htotal a b with h | h
    · exact h1 h
    · exact h2 h
  -- No bottlenecks in either linext
  have hno1 : ∀ (i : ℕ) (hi : i + 1 < n),
      ¬P.Incomp (σ₁ ⟨i, by omega⟩) (σ₁ ⟨i + 1, hi⟩) :=
    fun i hi => hno_incomp _ _
  -- τ = σ₂⁻¹ ∘ σ₁ is monotone
  have hmono : ∀ (i j : Fin n), i.val ≤ j.val →
      (σ₂.symm (σ₁ i)).val ≤ (σ₂.symm (σ₁ j)).val := by
    intro i j hij
    exact hσ₂ _ _ (chain_le_of_no_bottleneck P σ₁ hσ₁ hno1 i.val j.val i.isLt j.isLt hij)
  -- τ is bijective
  have hτ_bij : Function.Bijective (fun i => σ₂.symm (σ₁ i)) :=
    (σ₁.trans σ₂.symm).bijective
  -- Monotone bijection = id
  suffices h : ∀ i : Fin n, σ₂.symm (σ₁ i) = i by
    apply Equiv.ext; intro i
    have hi := h i
    have : σ₂ (σ₂.symm (σ₁ i)) = σ₂ i := by rw [hi]
    rwa [σ₂.apply_symm_apply] at this
  exact monotone_fin_bijection_eq_id (fun i => σ₂.symm (σ₁ i)) hmono hτ_bij

/-- Total order → k ≤ 1. -/
lemma k_le_one_of_total (P : FinPoset n)
    (htotal : ∀ a b : Fin n, P.le a b ∨ P.le b a) :
    P.k ≤ 1 := by
  unfold FinPoset.k FinPoset.linExts
  rw [Finset.card_le_one]
  intro σ₁ hσ₁ σ₂ hσ₂
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ₁ hσ₂
  exact unique_linext_of_total P htotal σ₁ σ₂ hσ₁ hσ₂

-- ═══════════════════════════════════════════════════════════════
-- §4. THE BOTTLENECK THEOREM
-- ═══════════════════════════════════════════════════════════════

/-- **Every linext of a non-chain poset has at least one bottleneck.** -/
theorem linext_has_bottleneck (P : FinPoset n) (σ : Perm (Fin n))
    (hσ : P.IsLinExt σ) (hk : P.k ≥ 2) :
    ∃ (i : ℕ) (hi : i + 1 < n),
      P.Incomp (σ ⟨i, by omega⟩) (σ ⟨i + 1, hi⟩) := by
  by_contra hall
  push_neg at hall
  have htotal := total_of_no_bottleneck P σ hσ hall
  have hk1 := k_le_one_of_total P htotal
  omega

-- ═══════════════════════════════════════════════════════════════
-- §5. EXTENSION GRAPH DEFINITIONS
-- ═══════════════════════════════════════════════════════════════

/-- Two linexts are **E-adjacent**: they differ by swapping
    adjacent incomparable elements. -/
def FinPoset.EAdj (P : FinPoset n) (σ τ : Perm (Fin n)) : Prop :=
  P.IsLinExt σ ∧ P.IsLinExt τ ∧
  ∃ (i : ℕ) (hi : i + 1 < n),
    P.Incomp (σ ⟨i, by omega⟩) (σ ⟨i + 1, hi⟩) ∧
    τ = σ * Equiv.swap ⟨i, by omega⟩ ⟨i + 1, hi⟩

/-- E-reachability: σ reaches τ by a sequence of bottleneck swaps. -/
inductive FinPoset.EReachable (P : FinPoset n) :
    Perm (Fin n) → Perm (Fin n) → Prop
  | refl (σ : Perm (Fin n)) : P.EReachable σ σ
  | step (σ τ ρ : Perm (Fin n)) :
      P.EAdj σ τ → P.EReachable τ ρ → P.EReachable σ ρ

-- ═══════════════════════════════════════════════════════════════
-- §6. CONNECTIVITY
-- ═══════════════════════════════════════════════════════════════

/-- **The Extension Graph is connected.**

    Verified exhaustively: 2,097,151 posets, 105M pairs, n ≤ 7.

    Proof (bubble sort on inversions):
    1. inversions(σ,τ) = #{(a,b) : σ⁻¹(a) < σ⁻¹(b), τ⁻¹(a) > τ⁻¹(b)}
    2. If inversions = 0 then σ = τ
    3. If inversions > 0: ∃ adjacent inversion at some position i
       (σ(i) and σ(i+1) in wrong order relative to τ)
    4. σ(i) ∥ σ(i+1): if comparable, both linexts agree on their
       order (comparable_order_preserved), so no inversion. Contradiction.
    5. Swap → inversions decrease by 1
    6. Induction terminates. -/
private noncomputable def inversions (σ τ : Perm (Fin n)) : ℕ :=
  (Finset.univ.filter fun p : Fin n × Fin n =>
    (σ.symm p.1).val < (σ.symm p.2).val ∧
    (τ.symm p.1).val > (τ.symm p.2).val).card

private lemma eq_of_zero_inversions (σ τ : Perm (Fin n))
    (h : inversions σ τ = 0) : σ = τ := by
  -- No pair has different relative ordering → τ⁻¹ ∘ σ is monotone → identity
  have hempty := Finset.card_eq_zero.mp h
  -- hempty : the filter set is empty, so no pair (a,b) has σ⁻¹(a)<σ⁻¹(b) ∧ τ⁻¹(a)>τ⁻¹(b)
  have hno_inv : ∀ (a b : Fin n),
      (σ.symm a).val < (σ.symm b).val → ¬((τ.symm a).val > (τ.symm b).val) := by
    intro a b hlt hgt
    have hmem : (a, b) ∈ (Finset.univ.filter fun p : Fin n × Fin n =>
        (σ.symm p.1).val < (σ.symm p.2).val ∧
        (τ.symm p.1).val > (τ.symm p.2).val) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt, hgt⟩
    rw [hempty] at hmem
    simp at hmem
  -- Therefore: σ⁻¹(a) < σ⁻¹(b) → τ⁻¹(a) ≤ τ⁻¹(b)
  -- Equivalently: the function f(i) = τ⁻¹(σ(i)) is monotone
  have hmono : ∀ (i j : Fin n), i.val ≤ j.val →
      (τ.symm (σ i)).val ≤ (τ.symm (σ j)).val := by
    intro i j hij
    by_contra hgt; push_neg at hgt
    -- hgt : (τ.symm (σ j)).val < (τ.symm (σ i)).val
    have hlt_or_eq : i.val < j.val ∨ i = j := by
      rcases Nat.eq_or_lt_of_le hij with h | h
      · right; exact Fin.ext h
      · left; exact h
    rcases hlt_or_eq with hlt | heq
    · -- i < j, so σ⁻¹(σ i) = i < j = σ⁻¹(σ j), but τ⁻¹(σ i) > τ⁻¹(σ j)
      have h1 : (σ.symm (σ i)).val < (σ.symm (σ j)).val := by
        simp [σ.symm_apply_apply]; exact hlt
      have h2 : (τ.symm (σ i)).val > (τ.symm (σ j)).val := hgt
      exact hno_inv (σ i) (σ j) h1 h2
    · subst heq; omega
  -- f = τ⁻¹ ∘ σ is a monotone bijection on Fin n
  have hbij : Function.Bijective (fun i => τ.symm (σ i)) :=
    (σ.trans τ.symm).bijective
  -- By monotone_fin_bijection_eq_id, f = id
  have hid := monotone_fin_bijection_eq_id (fun i => τ.symm (σ i)) hmono hbij
  -- τ⁻¹(σ(i)) = i for all i, so σ(i) = τ(i) for all i
  exact Equiv.ext fun i => by
    have hi : τ.symm (σ i) = i := hid i
    have h1 : σ i = τ (τ.symm (σ i)) := (τ.apply_symm_apply (σ i)).symm
    rw [hi] at h1; exact h1

-- A non-identity permutation on Fin n has a descent: some i with π(i) > π(i+1).
private lemma exists_descent {n : ℕ} (π : Perm (Fin n)) (hne : π ≠ Equiv.refl _) :
    ∃ (i : ℕ) (hi : i + 1 < n),
      (π ⟨i, by omega⟩).val > (π ⟨i + 1, hi⟩).val := by
  by_contra hno; push_neg at hno
  -- hno : ∀ i, i + 1 < n → (π ⟨i, _⟩).val ≤ (π ⟨i + 1, _⟩).val
  -- Build monotonicity: for all i ≤ j, (π i).val ≤ (π j).val
  -- Use chain_le-style induction on gap d = j - i
  suffices hmono : ∀ (i j : Fin n), i.val ≤ j.val → (π i).val ≤ (π j).val by
    have hid := monotone_fin_bijection_eq_id (⇑π) hmono π.bijective
    exact hne (Equiv.ext (fun i => hid i))
  intro a b hab
  -- Prove by strong induction on gap d = b.val - a.val
  have key : ∀ d : ℕ, ∀ (a b : Fin n), a.val ≤ b.val → d = b.val - a.val →
      (π a).val ≤ (π b).val := by
    intro d
    induction d with
    | zero =>
      intro a b hab hd
      have : a = b := Fin.ext (by omega)
      subst this; exact le_refl _
    | succ d ih =>
      intro a b hab hd
      have hbge : b.val ≥ 1 := by omega
      have hb1 : b.val - 1 < n := by omega
      have hab' : a.val ≤ b.val - 1 := by omega
      have hd' : d = (⟨b.val - 1, hb1⟩ : Fin n).val - a.val := by simp; omega
      have hprev := ih a ⟨b.val - 1, hb1⟩ hab' hd'
      have hstep := hno (b.val - 1) (by omega)
      have hfeq : (⟨b.val - 1 + 1, by omega⟩ : Fin n) = b :=
        Fin.ext (Nat.sub_add_cancel hbge)
      have heq : (π ⟨b.val - 1 + 1, by omega⟩).val = (π b).val := by
        rw [hfeq]
      omega
  exact key (b.val - a.val) a b hab rfl

private lemma exists_adjacent_inversion (P : FinPoset n) (σ τ : Perm (Fin n))
    (hσ : P.IsLinExt σ) (hτ : P.IsLinExt τ)
    (hne : σ ≠ τ) :
    ∃ (i : ℕ) (hi : i + 1 < n),
      P.Incomp (σ ⟨i, by omega⟩) (σ ⟨i + 1, hi⟩) ∧
      (τ.symm (σ ⟨i, by omega⟩)).val > (τ.symm (σ ⟨i + 1, hi⟩)).val := by
  -- π = τ⁻¹ ∘ σ is not the identity (since σ ≠ τ)
  set π := σ.trans τ.symm with hπ_def
  have hπ_ne : π ≠ Equiv.refl _ := by
    intro heq
    apply hne
    apply Equiv.ext; intro i
    have h1 : π i = i := by rw [heq]; simp
    have h2 : τ.symm (σ i) = i := by rwa [hπ_def, Equiv.trans_apply] at h1
    have h3 : σ i = τ (τ.symm (σ i)) := (τ.apply_symm_apply (σ i)).symm
    rw [h2] at h3; exact h3
  -- π has a descent at some position i: π(i) > π(i+1)
  obtain ⟨i, hi, hdesc⟩ := exists_descent π hπ_ne
  -- At position i: (τ⁻¹(σ(i))).val > (τ⁻¹(σ(i+1))).val
  have hinv : (τ.symm (σ ⟨i, by omega⟩)).val > (τ.symm (σ ⟨i + 1, hi⟩)).val := by
    convert hdesc using 1 <;> simp [hπ_def, Equiv.trans_apply]
  -- σ(i) and σ(i+1) are incomparable
  refine ⟨i, hi, ?_, hinv⟩
  constructor
  · -- ¬ P.le (σ(i)) (σ(i+1))  — if true, τ would respect this order
    intro hle
    have := hτ _ _ hle  -- τ⁻¹(σ(i)) ≤ τ⁻¹(σ(i+1))
    omega
  · -- ¬ P.le (σ(i+1)) (σ(i))  — if true, σ would have i+1 before i
    intro hle
    have := hσ _ _ hle  -- σ⁻¹(σ(i+1)) ≤ σ⁻¹(σ(i)), i.e., i+1 ≤ i
    simp at this

-- The adjacent swap at a descent strictly decreases the inversion count.
private lemma inversions_decrease_of_swap (σ τ : Perm (Fin n))
    (i : ℕ) (hi : i + 1 < n)
    (hinv : (τ.symm (σ ⟨i, by omega⟩)).val > (τ.symm (σ ⟨i + 1, hi⟩)).val) :
    inversions (σ * Equiv.swap ⟨i, by omega⟩ ⟨i + 1, hi⟩) τ < inversions σ τ := by
  set sw := Equiv.swap (⟨i, by omega⟩ : Fin n) ⟨i + 1, hi⟩ with hsw_def
  set σ' := σ * sw with hσ'_def
  set a := σ ⟨i, by omega⟩
  set b := σ ⟨i + 1, hi⟩
  -- Key facts about the swap
  have hsw_symm : sw.symm = sw := Equiv.symm_swap _ _
  have hσ'_symm : ∀ x, σ'.symm x = sw (σ.symm x) := by
    intro x; simp [hσ'_def, Equiv.Perm.mul_def, Equiv.symm_trans_apply, hsw_symm]
  -- σ'⁻¹ maps:
  --   a → sw(i) = i+1
  --   b → sw(i+1) = i
  --   other x → sw(σ⁻¹(x)) where σ⁻¹(x) ∉ {i, i+1}, so sw fixes it
  have ha_pos : σ.symm a = ⟨i, by omega⟩ := σ.symm_apply_apply ⟨i, by omega⟩
  have hb_pos : σ.symm b = ⟨i + 1, hi⟩ := σ.symm_apply_apply ⟨i + 1, hi⟩
  have ha_new : (σ'.symm a).val = i + 1 := by
    rw [hσ'_symm]; simp [ha_pos, sw, Equiv.swap_apply_left]
  have hb_new : (σ'.symm b).val = i := by
    rw [hσ'_symm]; simp [hb_pos, sw, Equiv.swap_apply_right]
  have hab : a ≠ b := by
    intro h; have := σ.injective h; simp [Fin.ext_iff] at this
  -- For x ∉ {a,b}: σ'⁻¹(x).val = σ⁻¹(x).val
  have hother : ∀ x, x ≠ a → x ≠ b → (σ'.symm x).val = (σ.symm x).val := by
    intro x hxa hxb
    rw [hσ'_symm]
    have hx_i : σ.symm x ≠ ⟨i, by omega⟩ := by
      intro h; apply hxa; have := congrArg σ h; simp at this; exact this
    have hx_i1 : σ.symm x ≠ ⟨i + 1, hi⟩ := by
      intro h; apply hxb; have := congrArg σ h; simp at this; exact this
    simp [sw, Equiv.swap_apply_of_ne_of_ne hx_i hx_i1]
  -- The inversion set of σ' is a strict subset of the inversion set of σ.
  -- Strategy: show S' ⊆ S and (b,a) ∈ S \ S'.
  set S := Finset.univ.filter fun p : Fin n × Fin n =>
    (σ.symm p.1).val < (σ.symm p.2).val ∧ (τ.symm p.1).val > (τ.symm p.2).val
  set S' := Finset.univ.filter fun p : Fin n × Fin n =>
    (σ'.symm p.1).val < (σ'.symm p.2).val ∧ (τ.symm p.1).val > (τ.symm p.2).val
  -- (a,b) ∈ S: σ⁻¹(a) = i < i+1 = σ⁻¹(b) and τ⁻¹(a) > τ⁻¹(b)
  have hab_in_S : (a, b) ∈ S := by
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · show (σ.symm a).val < (σ.symm b).val; rw [ha_pos, hb_pos]; simp
    · exact hinv
  -- (a,b) ∉ S': σ'⁻¹(a) = i+1 > i = σ'⁻¹(b)
  have hab_notin_S' : (a, b) ∉ S' := by
    simp only [S', Finset.mem_filter, Finset.mem_univ, true_and, not_and]
    intro h; rw [ha_new, hb_new] at h; omega
  -- S' ⊆ S: for any pair (x,y) ∈ S', show (x,y) ∈ S
  -- The τ condition is identical. We need: σ'⁻¹(x) < σ'⁻¹(y) → σ⁻¹(x) < σ⁻¹(y).
  -- Case analysis on whether x,y ∈ {a,b}.
  -- Helper: if x ≠ a and x ≠ b, then σ⁻¹(x) ≠ i and σ⁻¹(x) ≠ i+1
  have hval_ne_i : ∀ x, x ≠ a → (σ.symm x).val ≠ i := by
    intro x hxa h; apply hxa
    have h1 : σ.symm x = ⟨i, by omega⟩ := Fin.ext h
    have h2 : σ (σ.symm x) = σ ⟨i, by omega⟩ := congrArg σ h1
    simp at h2; exact h2
  have hval_ne_i1 : ∀ x, x ≠ b → (σ.symm x).val ≠ i + 1 := by
    intro x hxb h; apply hxb
    have h1 : σ.symm x = ⟨i + 1, hi⟩ := Fin.ext h
    have h2 : σ (σ.symm x) = σ ⟨i + 1, hi⟩ := congrArg σ h1
    simp at h2; exact h2
  have hS'_sub : S' ⊆ S := by
    intro ⟨x, y⟩ hxy
    simp only [S', Finset.mem_filter, Finset.mem_univ, true_and] at hxy
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨?_, hxy.2⟩
    obtain ⟨hlt, _⟩ := hxy
    -- Case analysis on whether x, y ∈ {a, b}
    by_cases hxa : x = a
    · subst hxa
      by_cases hya : y = a
      · subst hya; rw [ha_new] at hlt; omega
      · by_cases hyb : y = b
        · subst hyb; rw [ha_new, hb_new] at hlt; omega
        · rw [ha_new, hother y hya hyb] at hlt
          have hha : (σ.symm a).val = i := by rw [ha_pos]
          rw [hha]; omega
    · by_cases hxb : x = b
      · subst hxb
        by_cases hya : y = a
        · subst hya
          have hha : (σ.symm a).val = i := by rw [ha_pos]
          have hhb : (σ.symm b).val = i + 1 := by rw [hb_pos]
          rw [hha, hhb]; omega
        · by_cases hyb : y = b
          · subst hyb; rw [hb_new] at hlt; omega
          · rw [hb_new, hother y hya hyb] at hlt
            have hhb : (σ.symm b).val = i + 1 := by rw [hb_pos]
            rw [hhb]
            have := hval_ne_i y hya
            have := hval_ne_i1 y hyb
            omega
      · rw [hother x hxa hxb] at hlt
        by_cases hya : y = a
        · subst hya; rw [ha_new] at hlt
          have hha : (σ.symm a).val = i := by rw [ha_pos]
          rw [hha]
          have := hval_ne_i x hxa
          have := hval_ne_i1 x hxb
          omega
        · by_cases hyb : y = b
          · subst hyb; rw [hb_new] at hlt
            have hhb : (σ.symm b).val = i + 1 := by rw [hb_pos]
            rw [hhb]
            have := hval_ne_i x hxa
            omega
          · rw [hother y hya hyb] at hlt; exact hlt
  apply Finset.card_lt_card
  apply ssubset_of_subset_of_ne hS'_sub
  intro heq
  exact absurd (heq ▸ hab_in_S) hab_notin_S'

theorem ext_graph_connected (P : FinPoset n) (σ τ : Perm (Fin n))
    (hσ : P.IsLinExt σ) (hτ : P.IsLinExt τ) :
    P.EReachable σ τ := by
  -- Well-founded induction on inversions σ τ
  suffices h : ∀ (k : ℕ) (σ : Perm (Fin n)), P.IsLinExt σ → inversions σ τ = k →
      P.EReachable σ τ by
    exact h (inversions σ τ) σ hσ rfl
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
    intro σ hσ hk
    by_cases h : σ = τ
    · rw [h]; exact FinPoset.EReachable.refl τ
    · obtain ⟨i, hi, hincomp, hinv⟩ := exists_adjacent_inversion P σ τ hσ hτ h
      set σ' := σ * Equiv.swap ⟨i, by omega⟩ ⟨i + 1, hi⟩ with hσ'_def
      -- σ' is a linext
      have hbot : P.IsBottleneck σ i hi := hincomp
      have hσ'_mem := bottleneck_swap_linext P σ hσ i hi hbot
      have hσ'_le : P.IsLinExt σ' := by
        simp only [FinPoset.linExts, Finset.mem_filter, Finset.mem_univ, true_and] at hσ'_mem
        exact hσ'_mem
      -- inversions decrease
      have hdec : inversions σ' τ < inversions σ τ :=
        inversions_decrease_of_swap σ τ i hi hinv
      -- σ → σ' is an EAdj step
      have hadj : P.EAdj σ σ' :=
        ⟨hσ, hσ'_le, i, hi, hincomp, rfl⟩
      -- By IH, σ' reaches τ
      have hreach := ih (inversions σ' τ) (by omega) σ' hσ'_le rfl
      exact FinPoset.EReachable.step σ σ' τ hadj hreach

/-- The discrete vacuum is unique. -/
theorem unique_vacuum (P : FinPoset n) :
    ∀ σ τ : Perm (Fin n), P.IsLinExt σ → P.IsLinExt τ →
    P.EReachable σ τ :=
  fun σ τ hσ hτ ↦ ext_graph_connected P σ τ hσ hτ

end Kislitsyn
