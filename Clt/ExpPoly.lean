/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Data.Real.Irrational
import Mathlib.Topology.ContinuousMap.Bounded.Star
import Mathlib.Topology.ContinuousMap.Star


/-!
# Exponential polynomials

Bounded continuous functions of the form `x ↦ ∑ i in s, a i * exp (⟪u i, x⟫_ℝ * I)` for finite `s`.

These functions are a star-subalgebra of `E →ᵇ ℂ` (see `expPoly`).

-/


noncomputable section

open scoped RealInnerProductSpace

open BoundedContinuousFunction Complex

namespace Clt

section PR

variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
    [AddCommGroup W] [Module ℝ W] [TopologicalSpace W]
    {e : AddChar ℝ Circle} {L : V →ₗ[ℝ] W →ₗ[ℝ] ℝ}

@[simp]
lemma starRingEnd_addChar (x : ℝ) : starRingEnd ℂ (e x) = e (-x) := by
  have h := Circle.coe_inv_eq_conj ⟨e x, ?_⟩
  · simp only [Circle.coe_inv] at h
    simp [← h, e.map_neg_eq_inv]
  · simp only [Submonoid.unitSphere, SetLike.coe_mem]

def probChar (he : Continuous e) (hL : Continuous fun p : V × W ↦ L p.1 p.2)
    (w : Multiplicative W) :
    V →ᵇ ℂ where
  toFun := fun v ↦ e (L v (Multiplicative.toAdd w))
  continuous_toFun :=
    continuous_induced_dom.comp (he.comp (hL.comp (Continuous.Prod.mk_left w)))
  map_bounded' := by
    refine ⟨2, fun x y ↦ ?_⟩
    calc dist _ _
      ≤ (‖_‖ : ℝ) + ‖_‖ := dist_le_norm_add_norm _ _
    _ ≤ 1 + 1 := add_le_add (by simp) (by simp)
    _ = 2 := by ring

@[simp]
lemma probChar_apply (he : Continuous e) (hL : Continuous fun p : V × W ↦ L p.1 p.2)
    (w : Multiplicative W) :
    probChar he hL w v = e (L v (Multiplicative.toAdd w)) := rfl

lemma probChar_one (he : Continuous e) (hL : Continuous fun p : V × W ↦ L p.1 p.2) :
    probChar he hL 1 = 1 := by ext; simp

lemma probChar_mul (he : Continuous e) (hL : Continuous fun p : V × W ↦ L p.1 p.2)
    (x y : Multiplicative W) :
    probChar he hL (x * y) = probChar he hL x * probChar he hL y := by
  ext
  simp [e.map_add_eq_mul]

lemma probChar_inv (he : Continuous e) (hL : Continuous fun p : V × W ↦ L p.1 p.2)
    (w : Multiplicative W) :
    probChar he hL w⁻¹ = star (probChar he hL w) := by ext; simp

theorem probChar_SeparatesPoints (he : Continuous e) (he' : e ≠ 1)
    (hL : Continuous fun p : V × W ↦ L p.1 p.2) (hL' : ∀ v ≠ 0, L v ≠ 0) {v v' : V} (hv : v ≠ v') :
    ∃ w : W, probChar he hL w v ≠ probChar he hL w v' := by
  obtain ⟨w, hw⟩ := DFunLike.ne_iff.mp (hL' (v - v') (sub_ne_zero_of_ne hv))
  obtain ⟨a, ha⟩ := DFunLike.ne_iff.mp he'
  use (a / (L (v - v') w)) • w
  simp only [map_sub, LinearMap.sub_apply, probChar_apply, ne_eq]
  rw [← div_eq_one_iff_eq (Circle.coe_ne_zero _), div_eq_inv_mul, ← coe_inv_unitSphere,
    ← e.map_neg_eq_inv, ← Submonoid.coe_mul, ← e.map_add_eq_mul, OneMemClass.coe_eq_one]
  calc e (- L v' ((a / (L v w - L v' w)) • w) + L v ((a / (L v w - L v' w)) • w))
  _ = e (- (a / (L v w - L v' w)) • L v' w + (a / (L v w - L v' w)) • L v w) := by
    congr
    · rw [neg_smul, ← map_smul (L v')]
    · rw [← map_smul (L v)]
  _ = e ((a / (L (v - v') w)) • (L (v - v') w)) := by
    simp only [neg_mul, map_sub, LinearMap.sub_apply]
    congr
    module
  _ = e a := by
    congr
    simp only [map_sub, LinearMap.sub_apply, smul_eq_mul]
    rw [div_mul_cancel₀]
    convert hw
    simp
  _ ≠ 1 := ha

def expInnerMulI' (he : Continuous e) (hL : Continuous fun p : V × W ↦ L p.1 p.2) :
    Multiplicative W →* (V →ᵇ ℂ) where
  toFun := probChar he hL
  map_one' := probChar_one he hL
  map_mul' := probChar_mul he hL

@[simp]
lemma expInnerMulI'_apply (he : Continuous e) (hL : Continuous fun p : V × W ↦ L p.1 p.2)
    (w : Multiplicative W) (v : V) :
    expInnerMulI' he hL w v = e (L v (Multiplicative.toAdd w)) := by simp [expInnerMulI']

def expInnerMulIₐ' (he : Continuous e) (hL : Continuous fun p : V × W ↦ L p.1 p.2) :
    AddMonoidAlgebra ℝ W →ₐ[ℝ] (V →ᵇ ℂ) :=
  AddMonoidAlgebra.lift ℝ W (V →ᵇ ℂ) (expInnerMulI' he hL)

@[simp]
lemma expInnerMulIₐ'_apply (he : Continuous e) (hL : Continuous fun p : V × W ↦ L p.1 p.2)
    (w : AddMonoidAlgebra ℝ W) (v : V) :
    expInnerMulIₐ' he hL w v = ∑ a ∈ w.support, w a * (e (L v a) : ℂ) := by
  simp only [expInnerMulIₐ', AddMonoidAlgebra.lift_apply]
  rw [Finsupp.sum_of_support_subset w subset_rfl]
  · simp only [coe_sum, BoundedContinuousFunction.coe_smul, expInnerMulI'_apply, toAdd_ofAdd,
      real_smul, Finset.sum_apply]
  · simp

/-- The star-subalgebra of exponential polynomials. -/
def expPoly' (he : Continuous e) (hL : Continuous fun p : V × W ↦ L p.1 p.2) :
    StarSubalgebra ℝ (V →ᵇ ℂ) where
  toSubalgebra := (expInnerMulIₐ' he hL).range
  star_mem' := by
    intro x hx
    simp only [Subsemiring.coe_carrier_toSubmonoid, Subalgebra.coe_toSubsemiring,
      AlgHom.coe_range, Set.mem_range] at hx ⊢
    obtain ⟨y, rfl⟩ := hx
    set f : W ↪ W := ⟨fun x ↦ -x, (fun _ _ ↦ neg_inj.mp)⟩ with hf
    refine ⟨y.embDomain f, ?_⟩
    ext1 u
    simp only [expInnerMulIₐ'_apply, Finsupp.support_embDomain, Finset.sum_map,
      Finsupp.embDomain_apply, star_apply, star_sum, star_mul', RCLike.star_def, conj_ofReal,
      starRingEnd_addChar]
    simp_rw [← map_neg (L u)]
    rfl

lemma mem_expPoly' (he : Continuous e) (hL : Continuous fun p : V × W ↦ L p.1 p.2)
    (f : V →ᵇ ℂ) :
    f ∈ expPoly' he hL
      ↔ ∃ w : AddMonoidAlgebra ℝ W, f = fun x ↦ ∑ a ∈ w.support, w a * (e (L x a) : ℂ) := by
  change f ∈ (expInnerMulIₐ' he hL).range ↔ _
  rw [AlgHom.mem_range]
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨y, ?_⟩
    ext
    simp
  · rintro ⟨y, h⟩
    refine ⟨y, ?_⟩
    ext
    simp [h]

def toContinuousFunₐ : (V →ᵇ ℂ) →⋆ₐ[ℝ] C(V, ℂ) where
  toFun := (↑)
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl
  map_star' _ := rfl

lemma probChar_mem_expPoly' (he : Continuous e) (hL : Continuous fun p : V × W ↦ L p.1 p.2) :
    probChar he hL w ∈ expPoly' he hL := by
  rw [mem_expPoly']
  refine ⟨AddMonoidAlgebra.single w 1, ?_⟩
  ext v
  simp only [probChar_apply, AddMonoidAlgebra.single]
  rw [Finset.sum_eq_single]
  swap; · exact w
  · simp only [Finsupp.single_eq_same, ofReal_one, one_mul, SetLike.coe_eq_coe]
    rfl
  · simp [Finsupp.single_apply_ne_zero]
  · simp

lemma expPoly'_separatesPoints (he : Continuous e) (he' : e ≠ 1)
    (hL : Continuous fun p : V × W ↦ L p.1 p.2) (hL' : ∀ v ≠ 0, L v ≠ 0) :
    ((expPoly' he hL).map toContinuousFunₐ).SeparatesPoints := by
  intro v v' hvv'
  obtain ⟨w, hw⟩ := probChar_SeparatesPoints he he' hL hL' hvv'
  use probChar he hL w
  simp only [StarSubalgebra.coe_toSubalgebra, StarSubalgebra.coe_map, Set.mem_image,
    SetLike.mem_coe, exists_exists_and_eq_and, ne_eq, SetLike.coe_eq_coe]
  refine ⟨?_, hw⟩
  refine ⟨probChar he hL w, probChar_mem_expPoly' he hL, rfl⟩

end PR

@[simp]
lemma conj_exp_mul_I (x : ℝ) : starRingEnd ℂ (exp (x * I)) = exp (- x * I) := by
  have h := Circle.coe_inv_eq_conj ⟨exp (x * I), ?_⟩
  · simp only [Circle.coe_inv] at h
    rw [← h, neg_mul, exp_neg]
  · simp [exp_mul_I, abs_cos_add_sin_mul_I, Submonoid.unitSphere]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def expInnerMulI : Multiplicative E →* (E →ᵇ ℂ) where
  toFun := fun u ↦
    { toFun := fun x ↦ Circle.exp ⟪Multiplicative.toAdd u, x⟫
      continuous_toFun := by
        -- `continuity` fails
        refine continuous_induced_dom.comp (Circle.exp.continuous.comp ?_)
        exact continuous_const.inner continuous_id
      map_bounded' := by
        refine ⟨2, fun x y ↦ ?_⟩
        calc dist _ _
          ≤ (‖_‖ : ℝ) + ‖_‖ := dist_le_norm_add_norm _ _
        _ ≤ 1 + 1 := add_le_add (by simp) (by simp)
        _ = 2 := by ring }
  map_one' := by
    simp only [toAdd_one, inner_zero_left, Circle.exp_zero, OneMemClass.coe_one]
    rfl
  map_mul' := fun x y ↦ by
    simp only [toAdd_mul, inner_add_left, Circle.exp_add, Circle.coe_mul, Circle.coe_exp]
    rfl

lemma expInnerMulI_apply (u x : E) :
    expInnerMulI u x = exp (⟪u, x⟫ * I) := by
  simp only [expInnerMulI, Circle.coe_exp, AddChar.coe_mk]
  rfl

def expInnerMulIₐ : AddMonoidAlgebra ℝ E →ₐ[ℝ] (E →ᵇ ℂ) :=
  AddMonoidAlgebra.lift ℝ E (E →ᵇ ℂ) expInnerMulI

lemma expInnerMulIₐ_apply (x : AddMonoidAlgebra ℝ E) (v : E) :
    expInnerMulIₐ x v = ∑ a ∈ x.support, x a * exp (⟪a, v⟫ * I) := by
  simp only [expInnerMulIₐ, AddMonoidAlgebra.lift_apply, Circle.exp, expInnerMulI_apply]
  rw [Finsupp.sum_of_support_subset x subset_rfl]
  · simp [expInnerMulI_apply]
    rfl
  · simp

variable (E) in
/-- The star-subalgebra of exponential polynomials. -/
def expPoly : StarSubalgebra ℝ (E →ᵇ ℂ) where
  toSubalgebra := AlgHom.range expInnerMulIₐ
  star_mem' := by
    intro x hx
    simp only [Subsemiring.coe_carrier_toSubmonoid, Subalgebra.coe_toSubsemiring,
      AlgHom.coe_range, Set.mem_range] at hx ⊢
    obtain ⟨y, rfl⟩ := hx
    set f : E ↪ E := ⟨fun x ↦ -x, (fun _ _ ↦ neg_inj.mp)⟩ with hf
    refine ⟨y.embDomain f, ?_⟩
    ext1 u
    simp [expInnerMulIₐ_apply, Finsupp.support_embDomain, Finset.sum_map,
      Finsupp.embDomain_apply, star_apply, star_sum, star_mul', RCLike.star_def, conj_ofReal,
      conj_exp_mul_I]
    congr
    ext1 v
    congr
    simp only [hf, Function.Embedding.coeFn_mk, inner_neg_left, ofReal_neg, neg_mul]

lemma mem_expPoly (f : E →ᵇ ℂ) :
    f ∈ expPoly E
      ↔ ∃ y : AddMonoidAlgebra ℝ E, f = fun x ↦ ∑ a ∈ y.support, y a * exp (⟪a, x⟫ * I) := by
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

lemma expPoly_separatesPoints : ((expPoly E).map toContinuousFunₐ).SeparatesPoints := by
  intro x y hxy_ne
  simp only [toContinuousFunₐ, StarSubalgebra.coe_toSubalgebra, StarSubalgebra.coe_map,
    StarAlgHom.coe_mk', AlgHom.coe_mk, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
    Set.mem_image, SetLike.mem_coe, exists_exists_and_eq_and, ContinuousMap.coe_coe, ne_eq]
  obtain ⟨v, hv_ne⟩ : ∃ v, inner v x ≠ inner v y := by
    by_contra! h
    exact hxy_ne (ext_inner_left ℝ h)
  obtain ⟨r, hr_ne⟩ : ∃ r : ℝ,
      cexp (((inner (r • v) x : ℝ) : ℂ) * I) ≠ cexp (((inner (r • v) y : ℝ) : ℂ) * I) := by
    simp_rw [inner_smul_left, RCLike.conj_to_real, ofReal_mul, ne_eq, Complex.exp_eq_exp_iff_exists_int]
    -- use (inner v x - inner v y)⁻¹ would suffice, if we knew pi was irrational (#6718)
    use √2 * Real.pi * (inner v x - inner v y)⁻¹
    push_neg
    intro n hn
    apply irrational_sqrt_two.ne_int (n * 2)
    rw [← sub_eq_iff_eq_add', ← sub_mul, ← mul_sub, ← mul_assoc] at hn
    simp only [mul_eq_mul_right_iff, I_ne_zero, or_false] at hn
    norm_cast at hn
    rw [inv_mul_cancel_right₀ (sub_ne_zero_of_ne hv_ne)] at hn
    simpa [← mul_assoc, Real.pi_ne_zero] using hn
  set u := AddMonoidAlgebra.single (r • v) (1 : ℝ) with hu
  use expInnerMulIₐ u, ⟨u, rfl⟩
  rw [expInnerMulIₐ_apply,expInnerMulIₐ_apply]
  simp only [hu, ne_eq, one_ne_zero, not_false_eq_true, Finsupp.support_single_ne_zero,
    Finset.sum_singleton, Finsupp.single_eq_same, ofReal_one, one_mul]
  exact hr_ne

end Clt
