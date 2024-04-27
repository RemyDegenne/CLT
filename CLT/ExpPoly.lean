/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Topology.ContinuousFunction.Compact
import Mathlib.Analysis.Fourier.FourierTransform

/-!
# Exponential polynomials

Bounded continuous functions of the form `x ↦ ∑ i in s, a i * exp (⟪u i, x⟫_ℝ * I)` for finite `s`.

These functions are a star-subalgebra of `E →ᵇ ℂ` (see `expPoly`).

-/

open scoped BigOperators

open BoundedContinuousFunction Complex

namespace Clt

@[simp]
lemma conj_exp_mul_I (x : ℝ) : starRingEnd ℂ (exp (x * I)) = exp (- x * I) := by
  have h := coe_inv_circle_eq_conj ⟨exp (x * I), ?_⟩
  · simp only [coe_inv_unitSphere] at h
    rw [← h, neg_mul, exp_neg]
  · simp [exp_mul_I, abs_cos_add_sin_mul_I]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable
def expInnerMulI : Multiplicative E →* (E →ᵇ ℂ) where
  toFun := fun u ↦
    { toFun := fun x ↦ expMapCircle ⟪Multiplicative.toAdd u, x⟫_ℝ
      continuous_toFun := by
        -- `continuity` fails
        refine continuous_induced_dom.comp (expMapCircle.continuous.comp ?_)
        exact continuous_const.inner continuous_id
      map_bounded' := by
        refine ⟨2, fun x y ↦ ?_⟩
        calc dist _ _
          ≤ (‖_‖ : ℝ) + ‖_‖ := dist_le_norm_add_norm _ _
        _ ≤ 1 + 1 := add_le_add (by simp) (by simp)
        _ = 2 := by ring }
  map_one' := by
    simp only [toAdd_one, inner_zero_left, expMapCircle_zero, OneMemClass.coe_one]
    rfl
  map_mul' := fun x y ↦ by
    simp only [toAdd_mul, expMapCircle_apply, inner_add_left, ofReal_add, add_mul, exp_add]
    rfl

lemma expInnerMulI_apply (u : Multiplicative E) (x : E) :
    expInnerMulI u x = exp (⟪Multiplicative.toAdd u, x⟫_ℝ * I) := by
  simp only [expInnerMulI, expMapCircle_apply, MonoidHom.coe_mk, OneHom.coe_mk]
  rfl

noncomputable
def expInnerMulIₐ : AddMonoidAlgebra ℝ E →ₐ[ℝ] (E →ᵇ ℂ) :=
  AddMonoidAlgebra.lift ℝ E (E →ᵇ ℂ) expInnerMulI

lemma expInnerMulIₐ_apply (x : AddMonoidAlgebra ℝ E) (v : E) :
    expInnerMulIₐ x v = ∑ a in x.support, x a * exp (⟪a, v⟫_ℝ * I) := by
  simp only [expInnerMulIₐ, AddMonoidAlgebra.lift_apply, expMapCircle_apply, expInnerMulI_apply]
  rw [Finsupp.sum_of_support_subset x subset_rfl]
  · simp [expInnerMulI_apply]
  · simp

variable (E) in
/-- The star-subalgebra of exponential polynomials. -/
noncomputable
def expPoly : StarSubalgebra ℝ (E →ᵇ ℂ) where
  toSubalgebra := AlgHom.range expInnerMulIₐ
  star_mem' := by
    intro x hx
    simp only [Subsemiring.coe_carrier_toSubmonoid, Subalgebra.coe_toSubsemiring,
      AlgHom.coe_range, Set.mem_range] at hx ⊢
    obtain ⟨y, rfl⟩ := hx
    let f : E ↪ E := ⟨fun x ↦ -x, (fun _ _ ↦ neg_inj.mp)⟩
    refine ⟨y.embDomain f, ?_⟩
    ext1 u
    simp only [star_apply, IsROrC.star_def, expInnerMulIₐ_apply, Finsupp.support_embDomain,
      Finset.sum_map, Function.Embedding.coeFn_mk, inner_neg_left, ofReal_neg, neg_mul]
    rw [map_sum]
    congr
    ext1 v
    simp only [map_mul]
    congr
    · change y.embDomain f (f v) = starRingEnd ℂ (y v)
      rw [Finsupp.embDomain_apply, conj_ofReal] -- why is `conj_ofReal` not simp?
    · rw [conj_exp_mul_I, neg_mul]

lemma mem_expPoly (f : E →ᵇ ℂ) :
    f ∈ expPoly E
      ↔ ∃ y : AddMonoidAlgebra ℝ E, f = fun x ↦ ∑ a in y.support, y a * exp (⟪a, x⟫_ℝ * I) := by
  change f ∈ AlgHom.range expInnerMulIₐ ↔ _
  simp only [AlgHom.mem_range]
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨y, ?_⟩
    ext1 u
    rw [expInnerMulIₐ_apply]
  · rintro ⟨y, h⟩
    refine ⟨y, ?_⟩
    ext1 u
    rw [h, expInnerMulIₐ_apply]

variable (E) in
def toContinuousFunₐ : (E →ᵇ ℂ) →⋆ₐ[ℝ] C(E, ℂ) where
  toFun := (↑)
  map_one' := rfl
  map_mul' := fun _ _ ↦ rfl
  map_zero' := rfl
  map_add' := fun _ _ ↦ rfl
  commutes' := fun _ ↦ rfl
  map_star' := fun _ ↦ rfl

lemma expPoly_separatesPoints : ((expPoly E).map (toContinuousFunₐ E)).SeparatesPoints := by
  intro x y hxy_ne
  simp only [toContinuousFunₐ, StarSubalgebra.coe_toSubalgebra, StarSubalgebra.coe_map,
    StarAlgHom.coe_mk', AlgHom.coe_mk, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
    Set.mem_image, SetLike.mem_coe, mem_expPoly, exists_exists_and_eq_and, ContinuousMap.coe_coe,
    ne_eq]
  obtain ⟨v, hv_ne⟩ : ∃ v, inner v x ≠ inner v y := by
    by_contra! h
    exact hxy_ne (ext_inner_left ℝ h)
  obtain ⟨r, hr_ne⟩ : ∃ r : ℝ,
      cexp (((inner (r • v) x : ℝ) : ℂ) * I) ≠ cexp (((inner (r • v) y : ℝ) : ℂ) * I) := by
    simp_rw [inner_smul_left, IsROrC.conj_to_real, ofReal_mul]
    sorry
  let u := AddMonoidAlgebra.single (r • v) (1 : ℝ)
  refine ⟨expInnerMulIₐ u, ⟨u, ?_⟩, ?_⟩
  · ext x
    rw [expInnerMulIₐ_apply]
  · rw [expInnerMulIₐ_apply,expInnerMulIₐ_apply]
    simp only [ne_eq, one_ne_zero, not_false_eq_true, Finsupp.support_single_ne_zero,
      Finset.sum_singleton, Finsupp.single_eq_same, ofReal_one, one_mul]
    exact hr_ne

end Clt
