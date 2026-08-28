/-
Copyright (c) 2025 Martin Winter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Winter
-/

import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Face.Lattice
import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.DualClosed

/-! This file defines the algebraic relative interior of a convex cone. -/

open Submodule

/-
The relative interior (relint for short) is a topological notion, and hence might depend on the
exact topology chosen on the ambient space. In finite dimensions, the topology is essentially
unique, but in infinite dimensions it is possible that a cone has a non-empty or empty relint
depending on the topology.

Without a topology one can consider algebraic notions of relative interior.

The `core` is one possible notion with the following equivalent definitions: a point x ∈ C lies in
the core iff one of the following equivalent conditions holds:
  * x lies in no proper face of C
  * hull R (C ∪ (-x)) = span R C
  * ∀ t : span R C, ∃ c > 0, x + c • t ∈ C
  * ∀ φ : Dual R M, φ x = 0 → φ ∈ lineal (dual (Dual.eval R M) C)

The `weak relint` is another notion that is not always equivalent to the core. It is the relative
interior w.r.t. the topology obtain from the double-dual closure operation (or, weak topology).

In finite dimensions all these notions are the same, while in infinite dimensions this is not
true anymore. We always have `weak relint ≤ core`.

The core has moreover the property that the cone is the disjoint union of the cores of the faces.
This is not true for the weak relint. One still has disjointness of the weak relints, but not that
they cover all of the cone.

Here we chose the core for defining the algebraic relint. Among its many equivalent definitions,
we chose the most elementary one: `∀ t : span R C, ∃ c > 0, x + c • t ∈ C`, because it does not
depend on duality or the notions of faces or hulls.

See also: https://en.wikipedia.org/wiki/Algebraic_interior

-/

/- TODO:
  * proving that all these definitions are equivalent.
  * the relints of the faces of a cone partition the cone.
  * the relint is preserved under taking the double dual closure.
  * defining the weak relint and proving its relation to the core.
-/

namespace PointedCone

variable {R : Type*} [Field R] [LinearOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {N : Type*} [AddCommGroup N] [Module R N]
variable {p : M →ₗ[R] N →ₗ[R] R}
variable {C D : PointedCone R M} {x : M}

/-- Algebraic relative interior, also known as core. -/
def relint (C : PointedCone R M) : ConvexCone R M where
  carrier := {x ∈ C | ∀ t ∈ span R C, ∃ c > (0 : R), x + c • t ∈ C}
  smul_mem' c hc x hx := by
    refine ⟨C.smul_mem hc.le hx.1, fun t ht ↦ ?_⟩
    obtain ⟨d, hd, hxd⟩ := hx.2 (c⁻¹ • t) (Submodule.smul_mem _ _ ht)
    refine ⟨d, hd, ?_⟩
    have := C.smul_mem hc.le hxd
    rwa [smul_add, smul_comm c d, smul_inv_smul₀ hc.ne'] at this
  add_mem' x hx y hy := by
    refine ⟨C.add_mem hx.1 hy.1, fun t ht ↦ ?_⟩
    obtain ⟨c, hc, hxc⟩ := hx.2 t ht
    refine ⟨c, hc, ?_⟩
    have := C.add_mem hxc hy.1
    rwa [add_assoc, add_comm (c • t) y, ← add_assoc] at this

lemma relint_le : C.relint ≤ C := fun _ hx => hx.1

lemma mem_relint_iff_forall_exists_gt_zero_forall_le_add_smul_mem :
    x ∈ C.relint ↔ x ∈ C ∧ ∀ t ∈ span R C, ∃ c > (0 : R), x + c • t ∈ C := by
  simp [relint]

lemma mem_relint_iff_mem_hull_neg_eq_top :
    x ∈ C.relint ↔ x ∈ C ∧ hull R (insert (-x) C) = Submodule.span R (C : Set M) := by
    sorry

lemma mem_relint_iff_mem_forall_isFaceOf_eq_top_of_mem :
    x ∈ C.relint ↔ x ∈ C ∧ ∀ F : PointedCone R M, F.IsFaceOf C → x ∈ F → F = C := by
  sorry

lemma mem_relint_iff_mem_forall_face_eq_top_of_mem :
    x ∈ C.relint ↔ x ∈ C ∧ ∀ F : Face C, x ∈ F → F = ⊤ := by
  sorry

variable [Fact p.SeparatingLeft] in
lemma mem_relint_iff_forall_dual_zero_le_mem_lineal_of_eq_zero :
    x ∈ C.relint ↔ x ∈ C ∧ ∀ y ∈ dual p C, p x y = 0 → y ∈ (dual p C).lineal := by
  sorry

/- Construction for `mem_relint_iff_forall_dual_zero_le_mem_lineal_of_eq_zero.disproof` below:
the lexicographic cone on `ℕ →₀ ℚ`, whose dual cone is trivial. The pairing `pair` is the dot
product pairing from `Counterexamples.DualDualSpan`. -/
namespace Counterexamples.RelintLex

open Counterexamples.DualDualSpan (pair pair_single pair_apply)
open Finsupp

export Counterexamples.DualDualSpan (pair pair_single pair_apply)

lemma pair_apply_single (x : ℕ →₀ ℚ) (i : ℕ) (a : ℚ) : pair x (single i a) = x i * a := by
  rw [pair_apply, Finsupp.sum]
  rw [Finset.sum_eq_single i (fun j _ hj => by simp [Ne.symm hj])
    (fun hi => by simp [Finsupp.notMem_support_iff.mp hi])]
  simp

/-- The lexicographic cone: `x` lies in the cone iff `x = 0` or the nonzero coordinate of `x`
with the largest index is positive. -/
noncomputable def lex : PointedCone ℚ (ℕ →₀ ℚ) where
  carrier := {x | x = 0 ∨ ∃ i, 0 < x i ∧ ∀ j, i < j → x j = 0}
  zero_mem' := Or.inl rfl
  add_mem' := by
    intro x y hx hy
    rcases hx with rfl | ⟨i, hi, hti⟩
    · simpa using hy
    rcases hy with rfl | ⟨k, hk, htk⟩
    · simpa using Or.inr ⟨i, hi, hti⟩
    rcases lt_trichotomy i k with hik | rfl | hki
    · refine Or.inr ⟨k, ?_, fun j hj => ?_⟩
      · simpa [Finsupp.add_apply, hti k hik] using hk
      · simp [Finsupp.add_apply, hti j (hik.trans hj), htk j hj]
    · refine Or.inr ⟨i, ?_, fun j hj => ?_⟩
      · simpa [Finsupp.add_apply] using add_pos hi hk
      · simp [Finsupp.add_apply, hti j hj, htk j hj]
    · refine Or.inr ⟨i, ?_, fun j hj => ?_⟩
      · simpa [Finsupp.add_apply, htk i hki] using hi
      · simp [Finsupp.add_apply, hti j hj, htk j (hki.trans hj)]
  smul_mem' := by
    intro c x hx
    rw [← Nonneg.coe_smul]
    rcases hx with rfl | ⟨i, hi, hti⟩
    · simp
    by_cases hc : (c : ℚ) = 0
    · simp [hc]
    · refine Or.inr ⟨i, ?_, fun j hj => ?_⟩
      · rw [Finsupp.smul_apply, smul_eq_mul]
        exact mul_pos (lt_of_le_of_ne c.2 (Ne.symm hc)) hi
      · rw [Finsupp.smul_apply, hti j hj, smul_zero]

lemma mem_lex_iff {x : ℕ →₀ ℚ} :
    x ∈ lex ↔ x = 0 ∨ ∃ i, 0 < x i ∧ ∀ j, i < j → x j = 0 := Iff.rfl

lemma single_mem_lex {i : ℕ} {a : ℚ} (ha : 0 < a) : single i a ∈ lex :=
  Or.inr ⟨i, by simpa using ha,
    fun j hj => by rw [Finsupp.single_apply, ite_eq_right (by omega)]⟩

lemma step_mem_lex {i : ℕ} {c : ℚ} (hc : 0 < c) :
    c • single (i + 1) (1 : ℚ) - single i 1 ∈ lex := by
  refine Or.inr ⟨i + 1, ?_, fun j hj => ?_⟩
  · rw [Finsupp.sub_apply, Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul, mul_one,
      Finsupp.single_apply, ite_eq_right (by omega), sub_zero]
    exact hc
  · rw [Finsupp.sub_apply, Finsupp.smul_apply, Finsupp.single_apply, ite_eq_right (by omega),
      Finsupp.single_apply, ite_eq_right (by omega), smul_zero, sub_zero]

/-- Every vector in the dual of the lex cone vanishes. -/
lemma eq_zero_of_mem_dual_lex {y : ℕ →₀ ℚ}
    (hy : y ∈ dual pair (lex : PointedCone ℚ (ℕ →₀ ℚ))) : y = 0 := by
  have hnn : ∀ i, 0 ≤ y i := fun i => by
    simpa [pair_single] using hy (single_mem_lex (i := i) one_pos)
  have hstep : ∀ i, ∀ c : ℚ, 0 < c → 0 ≤ c * y (i + 1) - y i := by
    intro i c hc
    have := hy (step_mem_lex (i := i) hc)
    simpa [map_sub, pair_single] using this
  ext i
  simp only [Finsupp.coe_zero, Pi.zero_apply]
  refine le_antisymm ?_ (hnn i)
  by_contra hpos
  rw [not_le] at hpos
  have hd : (0 : ℚ) < y (i + 1) + 1 := by have := hnn (i + 1); linarith
  set c := y i / (y (i + 1) + 1) with hcdef
  have hc : 0 < c := div_pos hpos hd
  have hkey : c * (y (i + 1) + 1) = y i := by
    rw [hcdef]
    exact div_mul_cancel₀ _ hd.ne'
  have h2 := hstep i c hc
  nlinarith

end Counterexamples.RelintLex

open Counterexamples.RelintLex in
/-- The statement `mem_relint_iff_forall_dual_zero_le_mem_lineal_of_eq_zero` above is **false**
in infinite dimensions.

For the "lex" cone `{0} ∪ {x | the nonzero coordinate of x with largest index is positive}` on
`ℕ →₀ ℚ` the dual cone is trivial: from the constraints given by `e i` and `c • e (i+1) - e i`
(for all `c > 0`) any nonnegative functional is forced to vanish. Hence the right hand side holds
vacuously for every `x ∈ C`, while the relint is empty: no positive multiple of `-e 1` can be
added to `e 0` without leaving the cone. A correct version needs a finite rank hypothesis such as
`C.FinRank`. -/
theorem mem_relint_iff_forall_dual_zero_le_mem_lineal_of_eq_zero.disproof :
    (∀ {R : Type} [Field R] [LinearOrder R] [IsOrderedRing R]
        {M : Type} [AddCommGroup M] [Module R M]
        {N : Type} [AddCommGroup N] [Module R N]
        (p : M →ₗ[R] N →ₗ[R] R) [Fact p.SeparatingLeft] (C : PointedCone R M) (x : M),
        (x ∈ C.relint ↔ x ∈ C ∧ ∀ y ∈ dual p C, p x y = 0 → y ∈ (dual p C).lineal)) →
    False := by
  intro h
  have : Fact pair.SeparatingLeft :=
    ⟨fun x hx => by
      ext i
      simpa [pair_apply_single] using hx (Finsupp.single i 1)⟩
  -- The right hand side holds for `e 0 ∈ lex` since the dual cone is trivial ...
  have h1 : Finsupp.single 0 (1 : ℚ) ∈ lex.relint := by
    rw [h pair lex (Finsupp.single 0 1)]
    refine ⟨single_mem_lex one_pos, fun y hy _ => ?_⟩
    simp [eq_zero_of_mem_dual_lex hy]
  -- ... but `e 0` is not in the relint: `e 0 - c • e 1` has lead coefficient `-c < 0`.
  obtain ⟨-, hrel⟩ := mem_relint_iff_forall_exists_gt_zero_forall_le_add_smul_mem.mp h1
  have hspan : -(Finsupp.single 1 (1 : ℚ)) ∈ Submodule.span ℚ (lex : Set (ℕ →₀ ℚ)) :=
    Submodule.neg_mem _ (Submodule.subset_span (single_mem_lex one_pos))
  obtain ⟨c, hc, hmem⟩ := hrel _ hspan
  have he : ∀ j, (Finsupp.single 0 (1 : ℚ) + c • -Finsupp.single 1 1 : ℕ →₀ ℚ) j =
      (Finsupp.single 0 (1 : ℚ)) j - c * (Finsupp.single 1 (1 : ℚ)) j := by
    intro j
    simp only [Finsupp.add_apply, Finsupp.smul_apply, Finsupp.neg_apply, smul_eq_mul, mul_neg,
      sub_eq_add_neg]
  rcases mem_lex_iff.mp hmem with h0 | ⟨i, hi, hti⟩
  · have h00 := DFunLike.congr_fun h0 0
    rw [he 0] at h00
    simp at h00
  · rw [he i] at hi
    rcases i with - | - | i
    · have h1e := hti 1 (by omega)
      rw [he 1] at h1e
      simp at h1e
      exact hc.ne' h1e
    · simp at hi
      linarith
    · simp at hi

variable [Fact p.SeparatingLeft] in
lemma mem_relint_dual {y : N} :
    y ∈ (dual p C).relint ↔ y ∈ dual p C ∧ ∀ x ∈ C, p x y = 0 → x ∈ C.lineal := by
  sorry

/- Construction for `mem_relint_dual.disproof` below: the open upper halfplane together with the
nonnegative `x`-axis in `ℚ²`, a cone that is not dual closed, with the dot product pairing. -/
namespace Counterexamples.RelintDual

/-- The dot product pairing on `ℚ × ℚ`. -/
noncomputable def pair2 : (ℚ × ℚ) →ₗ[ℚ] (ℚ × ℚ) →ₗ[ℚ] ℚ :=
  LinearMap.mk₂ ℚ (fun x y => x.1 * y.1 + x.2 * y.2)
    (fun x x' y => by simp only [Prod.fst_add, Prod.snd_add]; ring)
    (fun c x y => by simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring)
    (fun x y y' => by simp only [Prod.fst_add, Prod.snd_add]; ring)
    (fun c x y => by simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring)

@[simp] lemma pair2_apply (x y : ℚ × ℚ) : pair2 x y = x.1 * y.1 + x.2 * y.2 := rfl

/-- The open upper halfplane together with the nonnegative `x`-axis. -/
def hp : PointedCone ℚ (ℚ × ℚ) where
  carrier := {x | 0 < x.2 ∨ (x.2 = 0 ∧ 0 ≤ x.1)}
  zero_mem' := Or.inr ⟨rfl, le_rfl⟩
  add_mem' := by
    intro x y hx hy
    rcases hx with hx | ⟨hx2, hx1⟩ <;> rcases hy with hy | ⟨hy2, hy1⟩
    · exact Or.inl (by rw [Prod.snd_add]; exact add_pos hx hy)
    · exact Or.inl (by rw [Prod.snd_add, hy2, add_zero]; exact hx)
    · exact Or.inl (by rw [Prod.snd_add, hx2, zero_add]; exact hy)
    · exact Or.inr ⟨by rw [Prod.snd_add, hx2, hy2, add_zero],
        by rw [Prod.fst_add]; exact add_nonneg hx1 hy1⟩
  smul_mem' := by
    intro c x hx
    rw [← Nonneg.coe_smul]
    by_cases hc : (c : ℚ) = 0
    · exact Or.inr ⟨by rw [Prod.smul_snd, hc, smul_eq_mul, zero_mul],
        by rw [Prod.smul_fst, hc, smul_eq_mul, zero_mul]⟩
    have hcpos := lt_of_le_of_ne c.2 (Ne.symm hc)
    rcases hx with hx | ⟨hx2, hx1⟩
    · exact Or.inl (by rw [Prod.smul_snd, smul_eq_mul]; exact mul_pos hcpos hx)
    · exact Or.inr ⟨by rw [Prod.smul_snd, hx2, smul_zero],
        by rw [Prod.smul_fst, smul_eq_mul]; exact mul_nonneg c.2 hx1⟩

lemma mem_hp_iff {x : ℚ × ℚ} : x ∈ hp ↔ 0 < x.2 ∨ (x.2 = 0 ∧ 0 ≤ x.1) := Iff.rfl

end Counterexamples.RelintDual

open Counterexamples.RelintDual in
/-- The statement `mem_relint_dual` above is **false** for cones that are not dual closed,
already in `ℚ²`.

For the cone `hp = {(a, b) | 0 < b} ∪ {(a, 0) | 0 ≤ a}` (the open upper halfplane together with
the nonnegative `x`-axis) the dual cone is the ray spanned by `(0, 1)`, and `(0, 1)` lies in its
relint; but `(0, 1)` annihilates `(1, 0) ∈ hp`, which is not in `hp.lineal`. A correct version
needs `C.DualClosed p` together with a finite rank hypothesis on `dual p C`. -/
theorem mem_relint_dual.disproof :
    (∀ {R : Type} [Field R] [LinearOrder R] [IsOrderedRing R]
        {M : Type} [AddCommGroup M] [Module R M]
        {N : Type} [AddCommGroup N] [Module R N]
        (p : M →ₗ[R] N →ₗ[R] R) [Fact p.SeparatingLeft] (C : PointedCone R M) (y : N),
        (y ∈ (dual p C).relint ↔ y ∈ dual p C ∧ ∀ x ∈ C, p x y = 0 → x ∈ C.lineal)) →
    False := by
  intro h
  have : Fact pair2.SeparatingLeft :=
    ⟨fun x hx => by
      have h1 := hx (1, 0)
      have h2 := hx (0, 1)
      simp at h1 h2
      exact Prod.ext h1 h2⟩
  have hsnd : ∀ x ∈ hp, (0 : ℚ) ≤ x.2 := by
    rintro x (hx | ⟨hx2, -⟩)
    · exact hx.le
    · exact le_of_eq hx2.symm
  have hdual1 : ((0, 1) : ℚ × ℚ) ∈ dual pair2 hp := fun x hx => by
    simpa using hsnd x hx
  have hfst : ∀ y ∈ dual pair2 hp, y.1 = 0 := by
    intro y hy
    by_contra h1
    have hkey : ∀ t : ℚ, 0 ≤ t * y.1 + y.2 := fun t => by
      simpa using hy (x := (t, 1)) (Or.inl one_pos)
    have := hkey ((-y.2 - 1) / y.1)
    rw [div_mul_cancel₀ _ h1] at this
    linarith
  -- `(0, 1)` lies in the relint of the dual cone ...
  have hLHS : ((0, 1) : ℚ × ℚ) ∈ (dual pair2 hp).relint := by
    rw [mem_relint_iff_forall_exists_gt_zero_forall_le_add_smul_mem]
    refine ⟨hdual1, fun t ht => ?_⟩
    have ht1 : t.1 = 0 := by
      have hle : Submodule.span ℚ ((dual pair2 hp : PointedCone ℚ (ℚ × ℚ)) : Set (ℚ × ℚ)) ≤
          LinearMap.ker (LinearMap.fst ℚ ℚ ℚ) :=
        Submodule.span_le.mpr fun y hy => LinearMap.mem_ker.mpr (hfst y hy)
      exact hle ht
    by_cases h2 : 0 ≤ t.2
    · refine ⟨1, one_pos, fun x hx => ?_⟩
      have hx2 := hsnd x hx
      simp [ht1]
      nlinarith
    · rw [not_le] at h2
      refine ⟨(-(2 * t.2))⁻¹, inv_pos.mpr (by linarith), fun x hx => ?_⟩
      have hx2 := hsnd x hx
      simp [ht1]
      nlinarith [mul_inv_cancel₀ (ne_of_lt h2 : t.2 ≠ 0), hx2, mul_nonneg hx2 hx2]
  -- ... but `(1, 0) ∈ hp` pairs to zero with `(0, 1)` without lying in the lineality space.
  obtain ⟨-, hRHS⟩ := (h pair2 hp (0, 1)).mp hLHS
  have hlin := hRHS (1, 0) (Or.inr ⟨rfl, by norm_num⟩) (by simp)
  rw [mem_lineal] at hlin
  rcases hlin.2 with hpos | ⟨-, hge⟩
  · simp at hpos
  · simp at hge
    linarith

lemma finset_sum_mem_relint_of_subset_of_le_span {s : Finset M} (hs : (s : Set M) ⊆ C)
    (hC : C ≤ Submodule.span R (s : Set M)) : ∑ x ∈ s, x ∈ relint C := by
  sorry

lemma finset_sum_mem_relint_hull {s : Finset M} : ∑ x ∈ s, x ∈ relint (hull R (s : Set M)) := by
  sorry

lemma relint_nonempty_of_finSalRank (h : C.FinSalRank) : Nonempty C.relint := sorry

-- Easier to prove than `relint_nonempty`, perhaps prove this first.
lemma relint_nonempty_of_finRank (h : C.FinRank) : Nonempty C.relint := by
  /-
    * choose a basis of span R C in C
    * since C.FinRank, this basis is finite
    * use `finset_sum_mem_relint_of_subset_of_le_span`
  -/
  let := (Submodule.fg_iff_finiteDimensional _).mp h
  obtain ⟨s, hsC, _, hs, _⟩ := exists_finset_span_eq_linearIndepOn R (C : Set M)
  refine ⟨∑ x ∈ s, x, finset_sum_mem_relint_of_subset_of_le_span hsC ?_⟩
  intro x hx
  rw [hs]
  exact Submodule.subset_span hx

 -- potential short proof of `IsExposedFace.exists_dual_pos`
variable (p) [Fact p.SeparatingLeft] in
example {C : PointedCone R M} (hC : C.FinSalRank) :
    ∃ φ : N, ∀ x ∈ C, 0 ≤ p x φ ∧ (p x φ = 0 → x ∈ C.lineal) := by
  obtain ⟨φ, hφ⟩ := relint_nonempty_of_finSalRank (hC.dual_finSalRank p)
  rw [mem_relint_dual] at hφ
  exact ⟨φ, fun _ h => ⟨by simpa using hφ.1 h, hφ.2 _ h⟩⟩

lemma ofSubmodule_relint (S : Submodule R M) : (S : PointedCone R M).relint = S := by
  refine le_antisymm relint_le fun _ hx ↦ ⟨hx, fun _ ht ↦ ⟨1, zero_lt_one, ?_⟩⟩
  rw [one_smul]
  exact S.add_mem hx (by simpa using ht)

end PointedCone
