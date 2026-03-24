import Math.YangMills.Foundations

/-!
# Hasse DAG — Covering Relation and Degree

The covering relation (transitive reduction) of a FinPoset.
Foundational definitions for the Myrheim-Meyer dimension
estimator and the Restriction Calculus.

## Main definitions

- `FinPoset.Covers u v`: u ⋖ v (u is covered by v)
- `FinPoset.children u`: set of upper covers of u
- `FinPoset.parents u`: set of lower covers of u
- `FinPoset.hasseDeg u`: total Hasse degree

## Main results

- `covers_triangle_free`: Hasse diagrams are triangle-free
- `no_hasse_triangle`: three-element triangle is impossible
-/

open scoped Classical
open Finset

namespace Kislitsyn

variable {n : ℕ}

-- ═════════════════════════════════════════════════════════════════
-- §1. STRICT ORDER AND COVERING RELATION
-- ═════════════════════════════════════════════════════════════════

/-- Strict partial order: u < v iff u ≤ v and u ≠ v. -/
def FinPoset.StrictLt (P : FinPoset n) (u v : Fin n) : Prop :=
  P.le u v ∧ u ≠ v

/-- Covering relation: u ⋖ v iff u < v and no element w
    satisfies u < w < v.  This is the transitive reduction. -/
def FinPoset.Covers (P : FinPoset n) (u v : Fin n) : Prop :=
  P.StrictLt u v ∧ ¬∃ w : Fin n, P.StrictLt u w ∧ P.StrictLt w v

-- ═════════════════════════════════════════════════════════════════
-- §2. BASIC PROPERTIES
-- ═════════════════════════════════════════════════════════════════

lemma FinPoset.covers_le (P : FinPoset n) {u v : Fin n}
    (h : P.Covers u v) : P.le u v :=
  h.1.1

lemma FinPoset.covers_ne (P : FinPoset n) {u v : Fin n}
    (h : P.Covers u v) : u ≠ v :=
  h.1.2

lemma FinPoset.covers_strictLt (P : FinPoset n) {u v : Fin n}
    (h : P.Covers u v) : P.StrictLt u v :=
  h.1

-- ═════════════════════════════════════════════════════════════════
-- §3. TRIANGLE-FREENESS
-- ═════════════════════════════════════════════════════════════════

/-- **Triangle-freeness of Hasse diagrams.**
    If u ⋖ w and w ⋖ v, then ¬(u ⋖ v).

    Proof: w witnesses that u < v is not a covering relation,
    since u < w < v provides an intermediate element. -/
theorem covers_triangle_free (P : FinPoset n)
    {u w v : Fin n} (huw : P.Covers u w) (hwv : P.Covers w v) :
    ¬P.Covers u v := by
  intro ⟨_, hno⟩
  exact hno ⟨w, huw.1, hwv.1⟩

/-- No three elements form a directed triangle in the Hasse graph. -/
theorem no_hasse_triangle (P : FinPoset n)
    {u w v : Fin n} (huw : P.Covers u w) (hwv : P.Covers w v)
    (huv : P.Covers u v) : False :=
  covers_triangle_free P huw hwv huv

/-- Covering is asymmetric: if u ⋖ v then ¬(v ⋖ u). -/
lemma covers_asymm (P : FinPoset n) {u v : Fin n}
    (h : P.Covers u v) : ¬P.Covers v u := by
  intro ⟨⟨hvu, hne⟩, _⟩
  have := P.le_antisymm u v h.1.1 hvu
  exact h.1.2 this

/-- Covering is irreflexive. -/
lemma covers_irrefl (P : FinPoset n) (u : Fin n) :
    ¬P.Covers u u := by
  intro ⟨⟨_, hne⟩, _⟩; exact hne rfl

-- ═════════════════════════════════════════════════════════════════
-- §4. HASSE DEGREE
-- ═════════════════════════════════════════════════════════════════

/-- The set of children (upper covers) of u. -/
noncomputable def FinPoset.children (P : FinPoset n)
    (u : Fin n) : Finset (Fin n) :=
  Finset.univ.filter fun v ↦ P.Covers u v

/-- The set of parents (lower covers) of u. -/
noncomputable def FinPoset.parents (P : FinPoset n)
    (u : Fin n) : Finset (Fin n) :=
  Finset.univ.filter fun v ↦ P.Covers v u

/-- Out-degree: |ch(u)|. -/
noncomputable def FinPoset.hasseDegOut (P : FinPoset n)
    (u : Fin n) : ℕ :=
  (P.children u).card

/-- In-degree: |pa(u)|. -/
noncomputable def FinPoset.hasseDegIn (P : FinPoset n)
    (u : Fin n) : ℕ :=
  (P.parents u).card

/-- Total Hasse degree: |ch(u)| + |pa(u)|. -/
noncomputable def FinPoset.hasseDeg (P : FinPoset n)
    (u : Fin n) : ℕ :=
  P.hasseDegOut u + P.hasseDegIn u

-- ═════════════════════════════════════════════════════════════════
-- §5. HASSE EDGE SET
-- ═════════════════════════════════════════════════════════════════

/-- The set of directed Hasse edges (covering pairs). -/
noncomputable def FinPoset.hasseEdges (P : FinPoset n) :
    Finset (Fin n × Fin n) :=
  Finset.univ.filter fun ⟨u, v⟩ ↦ P.Covers u v

/-- Number of directed Hasse edges. -/
noncomputable def FinPoset.hasseEdgeCount (P : FinPoset n) : ℕ :=
  P.hasseEdges.card

-- ═════════════════════════════════════════════════════════════════
-- §6. MEMBERSHIP LEMMAS
-- ═════════════════════════════════════════════════════════════════

@[simp]
lemma FinPoset.mem_children (P : FinPoset n) (u v : Fin n) :
    v ∈ P.children u ↔ P.Covers u v := by
  simp [FinPoset.children]

@[simp]
lemma FinPoset.mem_parents (P : FinPoset n) (u v : Fin n) :
    v ∈ P.parents u ↔ P.Covers v u := by
  simp [FinPoset.parents]

@[simp]
lemma FinPoset.mem_hasseEdges (P : FinPoset n) (u v : Fin n) :
    (u, v) ∈ P.hasseEdges ↔ P.Covers u v := by
  simp [FinPoset.hasseEdges]

-- ═════════════════════════════════════════════════════════════════
-- §7. CHILDREN/PARENTS DISJOINTNESS
-- ═════════════════════════════════════════════════════════════════

/-- u is not in its own children set. -/
lemma FinPoset.not_mem_children_self (P : FinPoset n) (u : Fin n) :
    u ∉ P.children u := by
  simp; exact covers_irrefl P u

/-- u is not in its own parents set. -/
lemma FinPoset.not_mem_parents_self (P : FinPoset n) (u : Fin n) :
    u ∉ P.parents u := by
  simp; exact covers_irrefl P u

/-- Children and parents are disjoint (a vertex cannot be both
    a child and a parent of the same node). -/
lemma FinPoset.children_parents_disjoint (P : FinPoset n) (u : Fin n) :
    Disjoint (P.children u) (P.parents u) := by
  rw [Finset.disjoint_left]
  intro v hv_ch hv_pa
  simp at hv_ch hv_pa
  exact covers_asymm P hv_ch hv_pa

end Kislitsyn
