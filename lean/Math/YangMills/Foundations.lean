import Mathlib.GroupTheory.Perm.Basic
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Data.Fintype.Perm
import Mathlib.Tactic

/-!
# Finite Poset Foundations

Minimal definitions for the Yang-Mills verification.
Self-contained — no imports from the 1/3-2/3 conjecture project.

Defines: FinPoset, Incomp, IsLinExt, linExts, k, c.
-/

open scoped Classical
open Finset Equiv

namespace Kislitsyn

variable {n : ℕ}

/-- A finite poset on n labeled elements. -/
structure FinPoset (n : ℕ) where
  le : Fin n → Fin n → Prop
  le_refl     : ∀ a, le a a
  le_antisymm : ∀ a b, le a b → le b a → a = b
  le_trans    : ∀ a b c, le a b → le b c → le a c

/-- Incomparability: neither a ≤ b nor b ≤ a. -/
def FinPoset.Incomp (P : FinPoset n) (x y : Fin n) : Prop :=
  ¬P.le x y ∧ ¬P.le y x

/-- P is not a total order (chain). -/
def FinPoset.NonChain (P : FinPoset n) : Prop :=
  ∃ x y, P.Incomp x y

/-- σ is a linear extension of P. -/
def FinPoset.IsLinExt (P : FinPoset n) (σ : Perm (Fin n)) : Prop :=
  ∀ a b, P.le a b → (σ.symm a).val ≤ (σ.symm b).val

/-- L(P) = the finite set of all linear extensions. -/
noncomputable def FinPoset.linExts (P : FinPoset n) : Finset (Perm (Fin n)) :=
  Finset.univ.filter P.IsLinExt

/-- k = |L(P)| = number of linear extensions. -/
noncomputable def FinPoset.k (P : FinPoset n) : ℕ :=
  P.linExts.card

/-- c(x,y) = |{σ ∈ L(P) : x appears before y in σ}|. -/
noncomputable def FinPoset.c (P : FinPoset n) (x y : Fin n) : ℕ :=
  (P.linExts.filter fun σ ↦ (σ.symm x).val < (σ.symm y).val).card

end Kislitsyn
