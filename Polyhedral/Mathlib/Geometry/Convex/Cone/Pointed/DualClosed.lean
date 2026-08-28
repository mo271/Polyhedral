/-
Copyright (c) 2025 Martin Winter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Winter
-/

import Polyhedral.Mathlib.Algebra.Module.Submodule.Dual.DualClosed
import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Dual
import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Rank

/-! This file defines dual closed cones, that is, cones that are identical to their
double dual.

Main definition:
* `DualClosed p C` states that `dual p.flip (dual p C) = C`.
 -/

namespace PointedCone

open Function Module LinearMap Pointwise
open Submodule (span)

variable {R M N : Type*}

section CommRing

variable [CommRing R] [PartialOrder R] [IsOrderedRing R]
variable [AddCommGroup M] [Module R M]
variable [AddCommGroup N] [Module R N]

variable {C D : PointedCone R M}
variable {p : M →ₗ[R] N →ₗ[R] R}

variable (p) in
/-- A cone is dual closed if it is identical to its double dual. -/
abbrev DualClosed (C : PointedCone R M) := dual p.flip (dual p C) = C

variable (p) in
@[simp] lemma DualClosed.def (hC : DualClosed p C) :
     dual p.flip (dual p C) = C := hC

variable (p) in
@[simp] lemma DualClosed.def_flip {C : PointedCone R N} (hC : DualClosed p.flip C) :
     dual p (dual p.flip C) = C := hC

lemma DualClosed.def_iff : DualClosed p C ↔ dual p.flip (dual p C) = C := by rfl

lemma DualClosed.def_flip_iff {C : PointedCone R N} :
    DualClosed p.flip C ↔ dual p (dual p.flip C) = C := by rfl

@[simp] lemma DualClosed.coe_iff {S : Submodule R M} :
    DualClosed p S ↔ S.DualClosed p := by
  change dual p.flip (dual p S) = S ↔ _
  rw [dual_eq_submodule_dual p S, dual_coe_coe_eq_dual_coe, dual_eq_submodule_dual p.flip]
  exact ofSubmodule_inj

lemma dualClosed_coe {S : Submodule R M} (hS : S.DualClosed p) :
    DualClosed p S := DualClosed.coe_iff.mpr hS

lemma dualClosed_coe' {S : Submodule R M} (hS : DualClosed p S) :
    S.DualClosed p := DualClosed.coe_iff.mp hS

variable (p) in
lemma dual_dualClosed (C : PointedCone R M) : (dual p C).DualClosed p.flip := by
  simp [DualClosed, dual_dual_flip_dual]

variable (p) in
lemma dual_flip_DualClosed (C : PointedCone R N) : (dual p.flip C).DualClosed p
    := dual_dualClosed p.flip C

lemma DualClosed.dual_inj (hC : C.DualClosed p) (hD : D.DualClosed p)
    (hCD : dual p C = dual p D) : C = D := by
  rw [← hC, ← hD, hCD]

@[simp] lemma DualClosed.dual_inj_iff (hC : C.DualClosed p)
    (hD : D.DualClosed p) : dual p C = dual p D ↔ C = D := ⟨dual_inj hC hD, by intro h; congr ⟩

lemma DualClosed.exists_of_dual_flip (hC : C.DualClosed p) :
    ∃ D : PointedCone R N, D.DualClosed p.flip ∧ dual p.flip D = C
  := ⟨dual p C, by simp [DualClosed, hC.def]⟩

lemma DualClosed.exists_of_dual {C : PointedCone R N} (hC : C.DualClosed p.flip) :
    ∃ D : PointedCone R M, D.DualClosed p ∧ dual p D = C
  := hC.exists_of_dual_flip

lemma DualClosed.inf (hS : C.DualClosed p) (hT : D.DualClosed p) :
    (C ⊓ D).DualClosed p := by
  rw [← hS, ← hT, ← dual_sup_dual_inf_dual, DualClosed, dual_flip_dual_dual_flip]

theorem DualClosed.eq_sInf (hC : C.DualClosed p) :
    C = sInf { D : PointedCone R M | D.DualClosed p ∧ C ≤ D } := by
  rw [Eq.comm, le_antisymm_iff]
  constructor
  · exact sInf_le ⟨hC, by simp⟩
  simp only [SetLike.le_def, Submodule.mem_sInf, Set.mem_ofPred_eq, and_imp]
  intro x hx D hD hsD
  rw [← hD]; rw [← hC] at hx
  exact (dual_dual_mono p hsD) hx

lemma DualClosed.dual_le_of_dual_le {D : PointedCone R N} (hC : C.DualClosed p)
    (hCD : dual p C ≤ D) : dual p.flip D ≤ C := by
  rw [← hC]; exact dual_antitone hCD

-- NOTE: This is the characterizing property of an antitone GaloisConnection.
lemma dual_le_iff_dual_le_of_dualClosed {D : PointedCone R N} (hC : C.DualClosed p)
    (hD : D.DualClosed p.flip) : dual p C ≤ D ↔ dual p.flip D ≤ C :=
  ⟨hC.dual_le_of_dual_le, hD.dual_le_of_dual_le⟩

variable (p) in
lemma dual_dual_eval_le_dual_dual_bilin (s : Set M) :
    dual .id (dual (Dual.eval R M) s) ≤ dual p.flip (dual p s) :=
  fun _ hx y hy => @hx (p.flip y) hy

lemma DualClosed.to_eval {S : PointedCone R M} (hS : S.DualClosed p) :
    S.DualClosed (Dual.eval R M) := by
  have h := dual_dual_eval_le_dual_dual_bilin p S
  rw [hS] at h
  exact le_antisymm h subset_dual_dual

lemma DualClosed.neg {C : PointedCone R M} (hC : C.DualClosed p) : (-C).DualClosed p := by
  unfold DualClosed
  repeat rw [Submodule.coe_set_neg, dual_neg]
  rw [hC]

lemma dual_inf_dual_sup_dual_of_dualClosed (C D : PointedCone R M)
    (hC : C.DualClosed p) (hD : D.DualClosed p) (hCD : (dual p C ⊔ dual p D).DualClosed p.flip) :
      dual p (C ⊓ D) = dual p C ⊔ dual p D := by
  change dual p (C ∩ D) = _ -- don't we have a theorem for this?
  nth_rw 1 [← hC, ← hD, ← Submodule.coe_inf, ← dual_sup_dual_inf_dual]
  exact hCD

lemma dual_inf_eq_sup_dual_iff_dualClosed (hC : C.DualClosed p) (hD : D.DualClosed p) :
    (dual p C ⊔ dual p D).DualClosed p.flip ↔ dual p (C ⊓ D) = dual p C ⊔ dual p D :=
  ⟨dual_inf_dual_sup_dual_of_dualClosed C D hC hD, fun h => h ▸ dual_dualClosed p (C ⊓ D)⟩

end CommRing

section LinearOrder

variable [CommRing R] [LinearOrder R] [IsOrderedRing R]
variable [AddCommGroup M] [Module R M]
variable [AddCommGroup N] [Module R N]

variable {C D : PointedCone R M}
variable {p : M →ₗ[R] N →ₗ[R] R}

lemma DualClosed.lineal (hC : C.DualClosed p) : C.lineal.DualClosed p := by
  rw [← coe_iff, ofSubmodule_lineal]
  exact DualClosed.inf hC hC.neg

/- WARNING: `C` being dual closed does *not* imply that `span R C` is dual closed! Not even
over ℝ or with a separating pairing!

But see `DualClosed.span_dualClosed` which assumes `FinSalRank`.
-/

-- # FARKAS

/- Separation lemma for dual closed cones. -/
lemma exists_pos_forall_nonneg_of_not_mem (hC : C.DualClosed p)
    {x : M} (hx : x ∉ C) : ∃ φ : N, p x φ < 0 ∧ ∀ y ∈ C, 0 ≤ p y φ := by
  rw [← hC] at hx
  simp only [mem_dual, SetLike.mem_coe, flip_apply, not_forall, not_le] at hx
  obtain ⟨φ, _, _⟩ := hx
  use φ

alias farkas := exists_pos_forall_nonneg_of_not_mem

/-- The dual of a cone being ⊥ is equivalent to all non-zero linear forms
  attaining negative values on the cone. -/
lemma dual_eq_bot_iff_forall_eq_zero_or_exists_neg :
    dual p C = ⊥ ↔ ∀ φ : N, φ = 0 ∨ ∃ x ∈ C, p x φ < 0 := by
  simp only [SetLike.ext_iff, mem_dual, SetLike.mem_coe, Submodule.mem_bot]
  constructor <;> intro h φ
  · by_cases hφ : φ = 0
    · left; exact hφ
    · replace h := (h φ).mp.mt hφ
      push Not at h
      right; exact h
  · constructor
    · intro h'
      rcases h φ
      · assumption
      · absurd h'
        push Not
        assumption
    · simp +contextual

-- /-- The dual of a cone being ⊥ is equivalent to all non-zero linear forms
--   attaining negative values on the cone. -/
-- lemma dual_eq_bot_iff_forall_eq_zero_or_exists_neg' {C : PointedCone R M} :
--     dual p C ≠ ⊥ ↔ ∃ φ : N, φ ≠ 0 ∧ ∀ x ∈ C, 0 ≤ p x φ := by
--   simp only [SetLike.ext_iff, mem_dual, SetLike.mem_coe, Submodule.mem_bot]
--   constructor <;> intro h φ
--   · by_cases hφ : φ = 0
--     · left; exact hφ
--     · replace h := (h φ).mp.mt hφ
--       push_neg at h
--       right; exact h
--   · constructor
--     · intro h'
--       rcases h φ
--       · assumption
--       · absurd h'
--         push_neg
--         assumption
--     · simp +contextual

/-- The double dual of a cone being ⊤ is equivalent to every non-zero linear
  form attaining a negative value on the cone. In infinite dimensional vector spaces
  there exists such cones other than ⊤ itself (e.g. the lexicographic cone). -/
lemma dual_dual_eq_top_iff_exists_ne_zero_forall_nonneg :
    dual p.flip (dual p C) ≠ ⊤ ↔ ∃ φ : N, p.flip φ ≠ 0 ∧ ∀ x ∈ C, 0 ≤ p x φ := by
  constructor <;> intro h
  · obtain ⟨x, hx⟩ := SetLike.exists_not_mem_of_ne_top _ h
    obtain ⟨φ, hxφ, hφ⟩ := farkas (dual_dualClosed _ _) hx
    use φ
    constructor
    · by_contra hφ
      rw [flip_apply] at hxφ
      simp [hφ] at hxφ
    exact fun y hy => hφ y (subset_dual_dual hy)
  · obtain ⟨φ, h0φ, hφ⟩ := h
    by_contra h
    rw [dual_top_iff_le_ker] at h
    have := h hφ
    contradiction

lemma exists_ne_zero_forall_nonneg_of_dualClosed_ne_top
    (hC : C.DualClosed p) (h : C ≠ ⊤) : ∃ φ : N, p.flip φ ≠ 0 ∧ ∀ x ∈ C, 0 ≤ p x φ := by
  simp [← dual_dual_eq_top_iff_exists_ne_zero_forall_nonneg, hC, h]


end LinearOrder

section Field

variable [Field R] [LinearOrder R] [IsOrderedRing R]
variable [AddCommGroup M] [Module R M]
variable [AddCommGroup N] [Module R N]

variable {C D : PointedCone R M}
variable {p : M →ₗ[R] N →ₗ[R] R}

-- Q: Do we need Field?
-- /-- For a dual closed cone, the dual of the lineality space is the submodule span of the dual. -/
-- lemma DualClosed.dual_lineal_span_dual {C : PointedCone R M} (hC : C.DualClosed p) :
--     Submodule.dual p C.lineal = Submodule.span R (dual p C) := by
--   rw [Eq.comm, le_antisymm_iff]
--   constructor
--   · exact span_dual_le_dual_lineal
--   simp only [lineal, Submodule.dual_sSup_sInf_dual]
--   have hh := (dual_dualClosed p C).submodule_span_dualClosed
--   rw [hh.eq_sInf]
--   --rw [submodule_span_dual]
--   refine sInf_le_sInf ?_
--   intro T
--   simp only [Set.mem_image, Set.mem_ofPred_eq, exists_exists_and_eq_and]
--   intro ⟨hdc, h⟩
--   use Submodule.dual p.flip T
--   constructor
--   · rw [← hC, ← dual_eq_submodule_dual]
--     exact dual_antitone h  -- (le_trans dual_le_submodule_dual h)
--   · exact hdc
--
-- variable [Fact (Surjective p)] in
-- /-- For a dual closed cone, the dual of the lineality space is the submodule span of the dual. -/
-- lemma DualClosed.dual_lineal_span_dual'' {C : PointedCone R M} (hC : C.DualClosed p) :
--     Submodule.dual p C.lineal = Submodule.span R (dual p C) := by
--   simp only [lineal, Submodule.dual_sSup_sInf_dual]
--   unfold Submodule.span
--   congr; ext T
--   simp only [Set.mem_image, Set.mem_ofPred_eq, exists_exists_and_eq_and]
--   constructor
--   · intro h -- this direction needs neither Field nor dual closed
--     obtain ⟨S, hSC, hS⟩ := h
--     rw [← hS]
--     nth_rw 3 [← ofSubmodule_coe]
--     rw [SetLike.coe_subset_coe, ← dual_eq_submodule_dual]
--     exact dual_le_dual hSC
--   · intro h -- this direction needs Field and dual closed; maybe not Field
--     use Submodule.dual p.flip T
--     constructor
--     · rw [← hC, ← dual_eq_submodule_dual]
--       exact dual_antitone h
--     · exact T.dualClosed p.flip
--
-- variable [Fact (Surjective p)] in
-- /-- For a dual closed cone, the dual of the submodule span is the lineality space of the dual. -/
-- lemma DualClosed.dual_span_lineal_dual {C : PointedCone R M} (hC : C.DualClosed p) :
--     .dual p (Submodule.span R (C : Set M)) = (dual p C).lineal := by
--   have h := hC.dual_lineal_span_dual.symm
--   obtain ⟨D, hD, rfl⟩ := hC.exists_of_dual_flip
--   --rw [DualClosed, flip_flip] at hD
--   rw [hD.def_flip] at *
--   simp at *
--   sorry

lemma DualClosed.dual_dual_span (hC : C.DualClosed p) :
    span R (dual p.flip (dual p C)) = .dual p.flip (Submodule.dual p (span R (C : Set M))) := by
  sorry

/- The statement `DualClosed.dual_dual_span` above is **false**: with the hypothesis `hC` it
claims that the span of a dual closed cone is a dual closed submodule, which fails in infinite
dimensions. The counterexample below works over `M = N = ℕ →₀ ℚ` with the standard dot pairing
`pair`. Let

* `u n = e 0 + e 2 + ⋯ + e (2n) + e (2n+1)` and `v n = -(e 0 + e 2 + ⋯ + e (2n)) + e (2n+1)`,
* `cone = dual pair.flip {u n, v n | n}`, which is dual closed as a dual cone.

For `x ∈ cone` with support bounded by `n` the constraints from `u n` and `v n` read
`±(∑ₖ x (2k)) ≥ 0`, so the "even sum" functional `phi` vanishes on `cone` and hence on its span;
since `phi (e 0) = 1 ≠ 0` the span is a proper submodule. On the other hand `cone` contains all
odd basis vectors `o n = e (2n+1)` as well as the elements
`q m = e (2m) - e 0 + (e 1 + e 3 + ⋯ + e (2m-1))`, and any `y` orthogonal to all of them is `0`,
so `Submodule.dual pair (span ℚ cone) = ⊥` and the right hand side of the statement is `⊤`.

A correct version of the statement needs a finite rank hypothesis such as `C.FinSalRank`
(compare `DualClosed.span_dualClosed` below). -/
namespace Counterexamples.DualDualSpan

open Finsupp

/-- The dot product pairing on `ℕ →₀ ℚ`. -/
noncomputable def pair : (ℕ →₀ ℚ) →ₗ[ℚ] (ℕ →₀ ℚ) →ₗ[ℚ] ℚ :=
  Finsupp.lsum ℚ fun i => LinearMap.toSpanSingleton ℚ ((ℕ →₀ ℚ) →ₗ[ℚ] ℚ) (Finsupp.lapply i)

lemma pair_single (i : ℕ) (a : ℚ) (y : ℕ →₀ ℚ) : pair (single i a) y = a * y i := by
  simp [pair, LinearMap.toSpanSingleton_apply, smul_eq_mul]

lemma pair_apply (x y : ℕ →₀ ℚ) : pair x y = x.sum fun i a => a * y i := by
  simp [pair, Finsupp.lsum_apply, Finsupp.sum, LinearMap.toSpanSingleton_apply, smul_eq_mul]

/-- The positive halves of the constraint pairs. -/
noncomputable def u (n : ℕ) : ℕ →₀ ℚ :=
  (∑ k ∈ Finset.range (n + 1), single (2 * k) 1) + single (2 * n + 1) 1

/-- The negative halves of the constraint pairs. -/
noncomputable def v (n : ℕ) : ℕ →₀ ℚ :=
  -(∑ k ∈ Finset.range (n + 1), single (2 * k) 1) + single (2 * n + 1) 1

/-- The dual closed cone. -/
noncomputable def cone : PointedCone ℚ (ℕ →₀ ℚ) :=
  dual pair.flip (Set.range u ∪ Set.range v)

lemma cone_dualClosed : cone.DualClosed pair :=
  dual_flip_dual_dual_flip (p := pair) (Set.range u ∪ Set.range v)

lemma mem_cone_iff {x : ℕ →₀ ℚ} :
    x ∈ cone ↔ ∀ y ∈ Set.range u ∪ Set.range v, 0 ≤ pair x y := by
  simp only [cone, mem_dual, LinearMap.flip_apply]

lemma sum_single_even_apply (n : ℕ) (i : ℕ) :
    (∑ k ∈ Finset.range (n + 1), single (2 * k) (1 : ℚ)) i =
      if Even i ∧ i ≤ 2 * n then 1 else 0 := by
  rw [Finsupp.finsetSum_apply]
  rcases Nat.even_or_odd i with ⟨k, hk⟩ | ⟨k, hk⟩
  · have hcong : ∀ k' ∈ Finset.range (n + 1),
        (single (2 * k') (1 : ℚ)) i = if k' = k then 1 else 0 := by
      intro k' _
      rw [Finsupp.single_apply]
      simp only [show (2 * k' = i) ↔ (k' = k) from by omega]
    rw [Finset.sum_congr rfl hcong,
      Finset.sum_ite_eq' (Finset.range (n + 1)) k fun _ => (1 : ℚ)]
    simp only [Finset.mem_range]
    simp only [show (Even i ∧ i ≤ 2 * n) ↔ (k < n + 1) from by
      constructor
      · rintro ⟨-, h⟩; omega
      · intro h; exact ⟨⟨k, by omega⟩, by omega⟩]
  · have hcong : ∀ k' ∈ Finset.range (n + 1), (single (2 * k') (1 : ℚ)) i = 0 := by
      intro k' _
      rw [Finsupp.single_apply, ite_eq_right (by omega)]
    rw [Finset.sum_congr rfl hcong]
    simp only [Finset.sum_const_zero]
    rw [ite_eq_right]
    rintro ⟨⟨r, hr⟩, -⟩
    omega

lemma u_apply (n : ℕ) (i : ℕ) :
    u n i = (if Even i ∧ i ≤ 2 * n then 1 else 0) + (if i = 2 * n + 1 then 1 else 0) := by
  rw [u, Finsupp.add_apply, sum_single_even_apply, Finsupp.single_apply]
  simp only [show (2 * n + 1 = i) ↔ (i = 2 * n + 1) from eq_comm]

lemma v_apply (n : ℕ) (i : ℕ) :
    v n i = -(if Even i ∧ i ≤ 2 * n then 1 else 0) + (if i = 2 * n + 1 then 1 else 0) := by
  rw [v, Finsupp.add_apply, Finsupp.neg_apply, sum_single_even_apply, Finsupp.single_apply]
  simp only [show (2 * n + 1 = i) ↔ (i = 2 * n + 1) from eq_comm]

lemma u_apply_even (j m : ℕ) : u j (2 * m) = if m ≤ j then 1 else 0 := by
  rw [u_apply, ite_eq_right (show ¬(2 * m = 2 * j + 1) by omega), add_zero]
  simp only [show (Even (2 * m) ∧ 2 * m ≤ 2 * j) ↔ (m ≤ j) from by
    constructor
    · rintro ⟨-, h⟩; omega
    · intro h; exact ⟨⟨m, by omega⟩, by omega⟩]

lemma u_apply_odd (j n : ℕ) : u j (2 * n + 1) = if n = j then 1 else 0 := by
  rw [u_apply, ite_eq_right (by rintro ⟨⟨r, hr⟩, -⟩; omega), zero_add]
  simp only [show (2 * n + 1 = 2 * j + 1) ↔ (n = j) from by omega]

lemma v_apply_even (j m : ℕ) : v j (2 * m) = -(if m ≤ j then 1 else 0) := by
  rw [v_apply, ite_eq_right (show ¬(2 * m = 2 * j + 1) by omega), add_zero]
  simp only [show (Even (2 * m) ∧ 2 * m ≤ 2 * j) ↔ (m ≤ j) from by
    constructor
    · rintro ⟨-, h⟩; omega
    · intro h; exact ⟨⟨m, by omega⟩, by omega⟩]

lemma v_apply_odd (j n : ℕ) : v j (2 * n + 1) = if n = j then 1 else 0 := by
  rw [v_apply, ite_eq_right (by rintro ⟨⟨r, hr⟩, -⟩; omega), neg_zero, zero_add]
  simp only [show (2 * n + 1 = 2 * j + 1) ↔ (n = j) from by omega]

/-- The "even coordinate sum" functional. It is not representable by any element of `ℕ →₀ ℚ`. -/
noncomputable def phi : (ℕ →₀ ℚ) →ₗ[ℚ] ℚ :=
  Finsupp.lsum ℚ fun i => if Even i then (LinearMap.id : ℚ →ₗ[ℚ] ℚ) else 0

lemma phi_apply (x : ℕ →₀ ℚ) : x.sum (fun i a => if Even i then a else 0) = phi x := by
  rw [phi, Finsupp.lsum_apply]
  refine Finsupp.sum_congr fun i _ => ?_
  rw [apply_ite (fun f : ℚ →ₗ[ℚ] ℚ => f (x i))]
  simp

lemma phi_single (i : ℕ) (a : ℚ) : phi (single i a) = if Even i then a else 0 := by
  rw [phi, Finsupp.lsum_single, apply_ite (fun f : ℚ →ₗ[ℚ] ℚ => f a)]
  simp

/-- The even sum functional vanishes on `cone`. -/
lemma cone_le_ker_phi : (cone : Set (ℕ →₀ ℚ)) ⊆ (LinearMap.ker phi : Submodule ℚ (ℕ →₀ ℚ)) := by
  intro x hx
  set n := x.support.sup id with hn
  have hsupp : ∀ i ∈ x.support, i ≤ 2 * n ∧ i ≠ 2 * n + 1 := by
    intro i hi
    have := Finset.le_sup (f := id) hi
    simp only [id_eq] at this
    omega
  have hu : pair x (u n) = phi x := by
    rw [pair_apply, ← phi_apply]
    refine Finsupp.sum_congr fun i hi => ?_
    rw [u_apply, ite_eq_right (hsupp i hi).2]
    rcases Nat.even_or_odd i with he | ho
    · rw [ite_eq_left ⟨he, (hsupp i hi).1⟩, ite_eq_left he]; ring
    · rw [ite_eq_right fun hc => (Nat.not_even_iff_odd.mpr ho) hc.1,
        ite_eq_right (Nat.not_even_iff_odd.mpr ho)]
      ring
  have hv : pair x (v n) = -phi x := by
    rw [pair_apply, ← phi_apply, Finsupp.sum, Finsupp.sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [v_apply, ite_eq_right (hsupp i hi).2]
    rcases Nat.even_or_odd i with he | ho
    · rw [ite_eq_left ⟨he, (hsupp i hi).1⟩, ite_eq_left he]; ring
    · rw [ite_eq_right fun hc => (Nat.not_even_iff_odd.mpr ho) hc.1,
        ite_eq_right (Nat.not_even_iff_odd.mpr ho)]
      ring
  have h1 := mem_cone_iff.mp hx (u n) (Or.inl ⟨n, rfl⟩)
  have h2 := mem_cone_iff.mp hx (v n) (Or.inr ⟨n, rfl⟩)
  rw [hu] at h1
  rw [hv] at h2
  simp only [SetLike.mem_coe, LinearMap.mem_ker]
  linarith

/-- The odd basis vectors, all of which lie in `cone`. -/
noncomputable def o (n : ℕ) : ℕ →₀ ℚ := single (2 * n + 1) 1

lemma o_mem_cone (n : ℕ) : o n ∈ cone := by
  rw [mem_cone_iff]
  rintro y (⟨j, rfl⟩ | ⟨j, rfl⟩)
  · rw [o, pair_single, one_mul, u_apply_odd]
    split <;> norm_num
  · rw [o, pair_single, one_mul, v_apply_odd]
    split <;> norm_num

/-- The even difference elements, all of which lie in `cone`. -/
noncomputable def q (m : ℕ) : ℕ →₀ ℚ :=
  single (2 * m) 1 - single 0 1 + ∑ n ∈ Finset.range m, single (2 * n + 1) 1

lemma pair_q (m : ℕ) (y : ℕ →₀ ℚ) :
    pair (q m) y = y (2 * m) - y 0 + ∑ n ∈ Finset.range m, y (2 * n + 1) := by
  simp only [q, map_add, map_sub, map_sum, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.sum_apply, pair_single, one_mul]

lemma q_mem_cone (m : ℕ) : q m ∈ cone := by
  rw [mem_cone_iff]
  have hodd : ∀ j, ∑ n ∈ Finset.range m, (if n = j then (1 : ℚ) else 0) =
      if j < m then 1 else 0 := by
    intro j
    rw [Finset.sum_ite_eq' (Finset.range m) j fun _ => (1 : ℚ)]
    simp
  rintro y (⟨j, rfl⟩ | ⟨j, rfl⟩)
  · rw [pair_q, u_apply_even, show u j 0 = 1 by simpa using u_apply_even j 0,
      Finset.sum_congr rfl fun n _ => u_apply_odd j n, hodd]
    by_cases hmj : m ≤ j
    · rw [ite_eq_left hmj, ite_eq_right (by omega)]; norm_num
    · rw [ite_eq_right hmj, ite_eq_left (by omega)]; norm_num
  · rw [pair_q, v_apply_even, show v j 0 = -1 by simpa using v_apply_even j 0,
      Finset.sum_congr rfl fun n _ => v_apply_odd j n, hodd]
    by_cases hmj : m ≤ j
    · rw [ite_eq_left hmj, ite_eq_right (by omega)]; norm_num
    · rw [ite_eq_right hmj, ite_eq_left (by omega)]; norm_num

/-- Only `0` is orthogonal to all of `cone`. -/
lemma dual_span_cone_eq_bot :
    Submodule.dual pair (Submodule.span ℚ (cone : Set (ℕ →₀ ℚ)) : Set (ℕ →₀ ℚ)) = ⊥ := by
  rw [eq_bot_iff]
  intro y hy
  have hkey : ∀ x ∈ cone, pair x y = 0 := fun x hx =>
    (hy (Submodule.subset_span hx)).symm
  -- all odd coordinates of `y` vanish
  have hodd : ∀ n, y (2 * n + 1) = 0 := by
    intro n
    have := hkey (o n) (o_mem_cone n)
    rwa [o, pair_single, one_mul] at this
  -- all even coordinates of `y` agree with `y 0`
  have heven : ∀ m, y (2 * m) = y 0 := by
    intro m
    have := hkey (q m) (q_mem_cone m)
    rw [pair_q, Finset.sum_congr rfl fun n _ => hodd n] at this
    simp only [Finset.sum_const_zero, add_zero] at this
    linarith
  -- `y` has finite support, so `y 0 = 0`
  have h0 : y 0 = 0 := by
    set m := y.support.sup id + 1 with hm
    have h2m : y (2 * m) = 0 := by
      apply Finsupp.notMem_support_iff.mp
      intro hmem
      have := Finset.le_sup (f := id) hmem
      simp only [id_eq] at this
      omega
    rw [← heven m, h2m]
  simp only [Submodule.mem_bot]
  ext i
  rcases Nat.even_or_odd i with ⟨k, hk⟩ | ⟨k, hk⟩
  · have := heven k
    rw [show i = 2 * k by omega]
    simp [this, h0]
  · rw [show i = 2 * k + 1 by omega]
    simp [hodd k]

end Counterexamples.DualDualSpan

open Counterexamples.DualDualSpan in
theorem DualClosed.dual_dual_span.disproof :
    (∀ {R : Type} [Field R] [LinearOrder R] [IsOrderedRing R]
        {M : Type} [AddCommGroup M] [Module R M]
        {N : Type} [AddCommGroup N] [Module R N]
        (p : M →ₗ[R] N →ₗ[R] R) (C : PointedCone R M), C.DualClosed p →
        Submodule.span R (dual p.flip (dual p C)) =
          Submodule.dual p.flip (Submodule.dual p (Submodule.span R (C : Set M)))) →
    False := by
  intro h
  have hE := h pair cone cone_dualClosed
  rw [cone_dualClosed, dual_span_cone_eq_bot] at hE
  -- the right hand side is everything ...
  rw [show ((⊥ : Submodule ℚ (ℕ →₀ ℚ)) : Set (ℕ →₀ ℚ)) = {0} from Submodule.bot_coe,
    Submodule.dual_bot] at hE
  -- ... so `phi` would vanish on all of `ℕ →₀ ℚ`, but `phi (single 0 1) = 1`.
  have hspan : Submodule.span ℚ (cone : Set (ℕ →₀ ℚ)) ≤ LinearMap.ker phi :=
    Submodule.span_le.mpr cone_le_ker_phi
  rw [hE] at hspan
  have h1 : phi (Finsupp.single 0 1) = 0 := hspan Submodule.mem_top
  rw [phi_single] at h1
  norm_num at h1

lemma DualClosed.dual_dual_lineal (hC : C.DualClosed p) :
    (dual p.flip (dual p C)).lineal = .dual p.flip (Submodule.dual p C.lineal) := by
  sorry

variable (p) [Fact (Surjective p.flip)] in
/-- Every submodule of a vector space is dual closed. -/
lemma dualClosed (S : Submodule R M) : DualClosed p S :=
    dualClosed_coe <| S.dualClosed p

/-- If a cone has dual closed lineality and has finite salient rank, then its span is
also dual closed. -/
lemma DualClosed.span_dualClosed_of_dualClosed_lineal (hC : C.lineal.DualClosed p)
    (h : C.FinSalRank) : (span R C).DualClosed p := by
  obtain ⟨D, hD, hCD⟩ := h.exists_finRank_sup_lineal
  rw [hCD, ← coe_sup_submodule_span, Submodule.span_union, coe_ofSubmodule,
    Submodule.span_eq C.lineal]
  simpa [sup_comm] using Submodule.DualClosed.sup_fg hC hD

/-- If a cone is dual closed and has finite salient rank, then its span is also dual closed. -/
lemma DualClosed.span_dualClosed (hC : C.DualClosed p)
    (h : C.FinSalRank) : (span R C).DualClosed p :=
  span_dualClosed_of_dualClosed_lineal hC.lineal h

end Field

end PointedCone
