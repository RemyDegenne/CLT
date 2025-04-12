/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
import Mathlib.MeasureTheory.Group.Convolution
import Mathlib.Probability.Notation
import Mathlib

/-!
# Characteristic function of a measure

## Main definitions

* `FooBar`

## Main statements

* `fooBar_unique`

## Notation



## Implementation details



-/


noncomputable section

open MeasureTheory ComplexConjugate Complex

open scoped RealInnerProductSpace Real

section Character

open scoped FourierTransform Real

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

@[fun_prop]
lemma integrable_probChar {μ : Measure ℝ} [IsProbabilityMeasure μ] (y : ℝ) :
    Integrable (fun x ↦ (Real.probChar (y * x) : ℂ)) μ := by
  rw [← integrable_norm_iff]
  · simp
  · exact Measurable.aestronglyMeasurable <| by fun_prop

theorem fourierIntegral_probChar_eq_integral_exp {V : Type _} [AddCommGroup V] [Module ℝ V]
    [MeasurableSpace V] {W : Type _} [AddCommGroup W] [Module ℝ W] (L : V →ₗ[ℝ] W →ₗ[ℝ] ℝ)
    (μ : Measure V) (f : V → E) (w : W) :
    VectorFourier.fourierIntegral Real.probChar μ L f w =
      ∫ v : V, exp (-↑(L v w) * I) • f v ∂μ := by
  simp_rw [VectorFourier.fourierIntegral, Circle.smul_def, Real.probChar_apply, ofReal_neg]

end

namespace BoundedContinuousFunction

variable {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The bounded continuous map `x ↦ exp(⟪x, t⟫ * I)`. -/
def innerProbChar (t : E) : BoundedContinuousFunction E ℂ :=
  BoundedContinuousFunction.char Real.continuous_probChar
    (L := bilinFormOfRealInner) continuous_inner t

lemma innerProbChar_apply (t x : E) : innerProbChar t x = exp (⟪x, t⟫ * I) := rfl

@[simp]
lemma innerProbChar_zero : innerProbChar (0 : E) = 1 := by simp [innerProbChar]

end BoundedContinuousFunction

end Character

open BoundedContinuousFunction

namespace ProbabilityTheory

variable {E 𝕜 : Type*} [RCLike 𝕜] [MeasurableSpace E] {μ : Measure E} {t : E}

/-- The characteristic function of a measure in an inner product space. -/
def charFun [Inner ℝ E] (μ : Measure E) (t : E) : ℂ := ∫ x, exp (⟪x, t⟫ * I) ∂μ

lemma charFun_apply [Inner ℝ E] (t : E) : charFun μ t = ∫ x, exp (⟪x, t⟫ * I) ∂μ := rfl

lemma charFun_apply_real {μ : Measure ℝ} {t : ℝ} :
    charFun μ t = ∫ x, exp (t * x * I) ∂μ := by simp [charFun_apply]

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

@[simp]
lemma charFun_zero (μ : Measure E) : charFun μ 0 = (μ Set.univ).toReal := by
  simp [charFun_apply]

@[simp]
lemma charFun_zero_measure : charFun (0 : Measure E) t = 0 := by simp [charFun_apply]

lemma charFun_eq_integral_innerProbChar : charFun μ t = ∫ v, innerProbChar t v ∂μ := by
  simp [charFun_apply, innerProbChar_apply]

lemma charFun_eq_integral_probChar (y : E) : charFun μ y = ∫ x, (Real.probChar ⟪x, y⟫ : ℂ) ∂μ := by
  simp [charFun_apply, Real.probChar_apply]

lemma charFun_eq_fourierIntegral (t : E) :
    charFun μ t = VectorFourier.fourierIntegral Real.probChar μ sesqFormOfInner 1 (-t) := by
  simp only [charFun_apply, real_smul, fourierIntegral_probChar_eq_integral_exp,
    Pi.one_apply, smul_eq_mul, mul_one, map_neg, ofReal_neg, neg_neg]
  simp_rw [real_inner_comm t]
  congr

/-- Relate `charFun` to the "standard" Fourier integral defined by `Real.fourierChar`. -/
lemma charFun_eq_fourierIntegral' (t : E) :
    charFun μ t = VectorFourier.fourierIntegral Real.fourierChar μ
      sesqFormOfInner 1 (-(2 * π)⁻¹ • t) := by
  have h : (2 : ℂ) * π ≠ 0 := by simp [Real.pi_ne_zero]
  simp only [charFun_apply, real_smul, VectorFourier.fourierIntegral, Real.fourierChar, neg_smul,
    map_neg, _root_.map_smul, smul_eq_mul, neg_neg, AddChar.coe_mk, ← mul_assoc, Pi.one_apply,
    Circle.smul_def, Circle.coe_exp, ofReal_mul, ofReal_ofNat, ofReal_inv, mul_inv_cancel₀ h,
    one_mul, mul_one]
  simp_rw [real_inner_comm t]
  congr

lemma charFun_neg (t : E) : charFun μ (-t) = conj (charFun μ t) := by
  simp [charFun_apply, ← integral_conj, ← exp_conj]

lemma norm_charFun_le (t : E) : ‖charFun μ t‖ ≤ (μ Set.univ).toReal := by
  rw [charFun_eq_fourierIntegral]
  refine (VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _).trans_eq ?_
  simp

lemma norm_charFun_le_one [IsProbabilityMeasure μ] (t : E) : ‖charFun μ t‖ ≤ 1 :=
  (norm_charFun_le _).trans_eq (by simp)

lemma norm_one_sub_charFun_le_two [IsProbabilityMeasure μ] :
    ‖1 - charFun μ t‖ ≤ 2 :=
  calc ‖1 - charFun μ t‖
  _ ≤ ‖(1 : ℂ)‖ + ‖charFun μ t‖ := norm_sub_le _ _
  _ ≤ 1 + 1 := by simp [norm_charFun_le_one]
  _ = 2 := by norm_num

lemma stronglyMeasurable_charFun [OpensMeasurableSpace E] [SecondCountableTopology E] [SFinite μ] :
    StronglyMeasurable (charFun μ) :=
  (Measurable.stronglyMeasurable (by fun_prop)).integral_prod_left

@[fun_prop]
lemma measurable_charFun [OpensMeasurableSpace E] [SecondCountableTopology E] [SFinite μ] :
    Measurable (charFun μ) :=
  stronglyMeasurable_charFun.measurable

lemma intervalIntegrable_charFun {μ : Measure ℝ} [IsFiniteMeasure μ] {a b : ℝ} :
    IntervalIntegrable (charFun μ) ℙ a b :=
  IntervalIntegrable.mono_fun' (g := fun _ ↦ (μ Set.univ).toReal) (by simp)
    stronglyMeasurable_charFun.aestronglyMeasurable (ae_of_all _ norm_charFun_le)

variable [BorelSpace E] [SecondCountableTopology E]

lemma charFun_map_smul (r : ℝ) (t : E) :
    charFun (μ.map (r • ·)) t = charFun μ (r • t) := by
  rw [charFun_apply, charFun_apply, integral_map]
  · simp_rw [inner_smul_right, ← real_inner_smul_left]
  · fun_prop
  · exact Measurable.aestronglyMeasurable <| by fun_prop

lemma charFun_map_mul {μ : Measure ℝ} (r : ℝ) (t : ℝ) :
    charFun (μ.map (r * ·)) t = charFun μ (r * t) :=
  charFun_map_smul r t

/-- The characteristic function of a convolution of measures
is the product of the respective characteristic functions. -/
lemma charFun_conv (μ ν : Measure E) [IsFiniteMeasure μ] [IsFiniteMeasure ν] (t : E) :
    charFun (μ ∗ ν) t = charFun μ t * charFun ν t := by
  simp_rw [charFun_apply]
  -- todo: missing lemma `integral_conv`
  unfold Measure.conv
  rw [integral_map, integral_prod]
  · simp_rw [inner_add_left]
    push_cast
    simp_rw [add_mul, exp_add, integral_mul_left, integral_mul_right]
  · apply (integrable_const (1 : ℝ)).mono
    · exact Measurable.aestronglyMeasurable <| by fun_prop
    · simp
  · fun_prop
  · exact Measurable.aestronglyMeasurable <| by fun_prop

/--
The characteristic function of the sum of `n` i.i.d. variables with characteristic function `f` is
`f ^ n`.

We express this in terms of the pushforward of $P^{\otimes n}$ by summation.

(A more general version not assuming identical distribution is possible)

(Should I express this using pushforward of `iIndepFun` etc?)
-/
lemma charFun_map_sum_pi_const (μ : Measure E) [IsFiniteMeasure μ] (n : ℕ) (t : E) :
    charFun ((Measure.pi fun (_ : Fin n) ↦ μ).map fun x ↦ ∑ i, x i) t = charFun μ t ^ n := by
  induction' n with n ih
  · simp [Measure.map_const, charFun_apply]
  · rw [pow_succ', ← ih, ← charFun_conv]
    congr 1
    have h := (measurePreserving_piFinSuccAbove (fun (_ : Fin (n + 1)) ↦ μ) 0).map_eq
    nth_rw 2 [← μ.map_id]
    rw [Measure.conv, Measure.map_prod_map, ← h, Measure.map_map, Measure.map_map]
    · congr 1 with x
      apply Fin.sum_univ_succ
    all_goals { fun_prop }

section bounds

section SinDiv

lemma sin_le_half {x : ℝ} (hx : 2 ≤ x) : Real.sin x ≤ x / 2 :=
  calc Real.sin x ≤ 1 := Real.sin_le_one x
    _ ≤ x / 2 := by linarith

lemma abs_sin_div_le_one (x : ℝ) : |Real.sin x / x| ≤ 1 := by
  rw [abs_div]
  refine div_le_of_le_mul₀ (abs_nonneg _) zero_le_one ?_
  rw [one_mul]
  exact Real.abs_sin_le_abs

lemma sin_div_le_one (x : ℝ) : Real.sin x / x ≤ 1 := by
  have h := abs_sin_div_le_one x
  rw [abs_le] at h
  exact h.2

lemma sin_div_le_inv_abs (x : ℝ) : Real.sin x / x ≤ |x|⁻¹ := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · rw [abs_of_nonpos hx.le, ← one_div, le_div_iff₀, div_eq_mul_inv]
    · ring_nf
      rw [mul_assoc, mul_inv_cancel₀ hx.ne, mul_one, neg_le]
      exact Real.neg_one_le_sin x
    · simpa using hx
  · simp
  · rw [abs_of_nonneg hx.le, div_eq_mul_inv, mul_inv_le_iff₀ hx, inv_mul_cancel₀ hx.ne']
    exact Real.sin_le_one x

lemma sin_div_le_half {x : ℝ} (hx : 2 ≤ |x|) : Real.sin x / x ≤ 2⁻¹ :=
  calc Real.sin x / x
    _ ≤ |x|⁻¹ := sin_div_le_inv_abs x
    _ ≤ 2⁻¹ := by rwa [inv_le_inv₀ (by positivity) (by positivity)]

lemma integrable_sin_div_const_mul {μ : Measure ℝ} [IsFiniteMeasure μ] (r : ℝ) :
    Integrable (fun x ↦ if x = 0 then 1 else Real.sin (r * x) / (r * x)) μ := by
    refine Integrable.mono' (g := fun _ ↦ 1) (integrable_const _) ?_ <| ae_of_all _ fun x ↦ ?_
    · exact (Measurable.ite (by simp) (by fun_prop) (by fun_prop)).aestronglyMeasurable
    · split_ifs with h
      · norm_num
      rw [Real.norm_eq_abs]
      exact abs_sin_div_le_one (r * x)

end SinDiv

lemma integral_exp_Icc (r : ℝ) : ∫ t in -r..r, cexp (t * I) = 2 * Real.sin r :=
  calc ∫ t in -r..r, cexp (t * I)
  _ = (cexp (I * r) - cexp (I * (-r))) / I := by
    simp_rw [mul_comm _ I]
    rw [integral_exp_mul_complex]
    · simp
    · simp
  _ = 2 * Real.sin r := by
    simp_rw [mul_comm I]
    simp only [exp_mul_I, cos_neg, sin_neg, add_sub_add_left_eq_sub, div_I, ofReal_sin]
    rw [sub_mul, mul_assoc, mul_assoc, two_mul]
    simp

lemma integral_charFun_Icc {μ : Measure ℝ} [IsProbabilityMeasure μ] {r : ℝ} (hr : 0 < r) :
    ∫ t in -r..r, charFun μ t
      = 2 * r * ∫ x, if x = 0 then 1 else Real.sin (r * x) / (r * x) ∂μ := by
  have h_int r : Integrable (Function.uncurry fun (x y : ℝ) ↦ cexp (x * y * I))
      ((volume.restrict (Set.Ioc (-r) r)).prod μ) := by
    -- integrable since bounded and the measure is finite
    rw [← integrable_norm_iff]
    swap; · exact Measurable.aestronglyMeasurable <| by fun_prop
    suffices (fun a => ‖Function.uncurry (fun (x y : ℝ) ↦ cexp (x * y * I)) a‖) = fun _ ↦ 1 by
      rw [this]
      fun_prop
    ext p
    rw [← Prod.mk.eta (p := p)]
    norm_cast
    simp only [Function.uncurry_apply_pair, norm_exp_ofReal_mul_I]
  calc ∫ t in -r..r, charFun μ t
  _ = ∫ x in -r..r, ∫ y, cexp (x * y * I) ∂μ := by simp_rw [charFun_apply_real]
  _ = ∫ y, ∫ x in Set.Ioc (-r) r, cexp (x * y * I) ∂volume ∂μ
      - ∫ y, ∫ x in Set.Ioc r (-r), cexp (x * y * I) ∂volume ∂μ := by
    rw [intervalIntegral]
    congr 1
    · rw [integral_integral_swap]
      exact h_int r
    · rw [integral_integral_swap]
      convert h_int (-r)
      simp
  _ = ∫ y, ∫ x in -r..r, cexp (x * y * I) ∂volume ∂μ:= by
    have h_le (y : ℝ) a : ‖∫ (x : ℝ) in Set.Ioc (-a) a, cexp (x * y * I)‖
        ≤ (ENNReal.ofReal (a + a)).toReal := by
      refine (norm_integral_le_integral_norm _).trans_eq ?_
      norm_cast
      simp_rw [norm_exp_ofReal_mul_I]
      simp
    rw [← integral_sub]
    · congr
    · refine Integrable.mono' (integrable_const (ENNReal.ofReal (r + r)).toReal) ?_
        (ae_of_all _ fun y ↦ h_le y r)
      refine StronglyMeasurable.aestronglyMeasurable ?_
      refine StronglyMeasurable.integral_prod_left (f := fun (x y : ℝ) ↦ cexp (x * y * I)) ?_
      exact Measurable.stronglyMeasurable (by fun_prop)
    · refine Integrable.mono' (integrable_const (ENNReal.ofReal (-r + -r)).toReal) ?_
        (ae_of_all _ fun y ↦ ?_)
      · refine StronglyMeasurable.aestronglyMeasurable ?_
        refine StronglyMeasurable.integral_prod_left (f := fun (x y : ℝ) ↦ cexp (x * y * I)) ?_
        exact Measurable.stronglyMeasurable (by fun_prop)
      · convert h_le y (-r) using 2
        simp
  _ = ∫ y, if y = 0 then 2 * (r : ℂ)
      else y⁻¹ * ∫ x in (-(y * r))..(y * r), cexp (x * I) ∂volume ∂μ := by
    congr with y
    by_cases hy : y = 0
    · simp [hy, two_mul]
    simp only [hy, ↓reduceIte, ofReal_inv]
    have h := intervalIntegral.integral_comp_smul_deriv (E := ℂ) (a := -r) (b := r)
      (f := fun x ↦ y * x) (f' := fun _ ↦ y) (g := fun x ↦ cexp (x * I)) ?_ (by fun_prop)
      (by fun_prop)
    swap
    · intro x hx
      simp_rw [mul_comm y]
      exact hasDerivAt_mul_const _
    simp only [Function.comp_apply, ofReal_mul, real_smul, intervalIntegral.integral_const_mul,
      mul_neg] at h
    rw [← h, ← mul_assoc]
    norm_cast
    simp_rw [mul_comm _ y]
    simp [mul_inv_cancel₀ hy]
  _ = ∫ x, 2 * (r : ℂ) * if x = 0 then 1 else Real.sin (r * x) / (r * x) ∂μ := by
    congr with y
    by_cases hy : y = 0
    · simp [hy]
    simp only [hy, ↓reduceIte, ofReal_inv, ofReal_div, ofReal_sin, ofReal_mul]
    rw [integral_exp_Icc]
    norm_cast
    field_simp
    ring_nf
  _ = 2 * r * ∫ x, if x = 0 then 1 else Real.sin (r * x) / (r * x) ∂μ := by
    norm_cast
    rw [integral_complex_ofReal, ← integral_mul_left]

lemma measure_abs_ge_le_charFun {μ : Measure ℝ} [IsProbabilityMeasure μ] {r : ℝ} (hr : 0 < r) :
    (μ {x | r < |x|}).toReal
      ≤ 2⁻¹ * r * ‖∫ t in (-2 * r⁻¹)..(2 * r⁻¹), 1 - charFun μ t‖ := by
  have h_int :
      Integrable (fun x ↦ if x = 0 then 1 else Real.sin (2 * r⁻¹ * x) / (2 * r⁻¹ * x)) μ :=
    integrable_sin_div_const_mul _
  calc (μ {x | r < |x|}).toReal
  _ = (μ {x | 2 < |2 * r⁻¹ * x|}).toReal := by
    congr with x
    simp only [Set.mem_setOf_eq, abs_mul, Nat.abs_ofNat]
    rw [abs_of_nonneg (a := r⁻¹) (by positivity), mul_assoc, ← inv_mul_lt_iff₀ (by positivity),
      inv_mul_cancel₀ (by positivity), lt_inv_mul_iff₀ (by positivity), mul_one]
  _ = ∫ x in {x | 2 < |2 * r⁻¹ * x|}, 1 ∂μ := by simp
  _ = 2 * ∫ x in {x | 2 < |2 * r⁻¹ * x|}, 2⁻¹ ∂μ := by
    rw [← integral_mul_left]
    congr with _
    rw [mul_inv_cancel₀ (by positivity)]
  _ ≤ 2 * ∫ x in {x | 2 < |2 * r⁻¹ * x|}, 1 - if x = 0 then 1
      else Real.sin (2 * r⁻¹ * x) / (2 * r⁻¹ * x) ∂μ := by
    gcongr (2 : ℝ) * ?_
    refine setIntegral_mono_on ?_ ((integrable_const _).sub h_int).integrableOn ?_ fun x hx ↦ ?_
    · exact Integrable.integrableOn <| by fun_prop
    · exact MeasurableSet.preimage measurableSet_Ioi (by fun_prop)
    · have hx_ne : x ≠ 0 := by
        intro hx0
        simp only [hx0, Set.mem_setOf_eq, mul_zero, abs_zero] at hx
        linarith
      simp only [hx_ne, ↓reduceIte, ge_iff_le]
      rw [le_sub_iff_add_le, ← le_sub_iff_add_le']
      norm_num
      rw [one_div]
      exact sin_div_le_half (le_of_lt hx)
  _ ≤ 2 * ∫ x, 1 - if x = 0 then 1 else Real.sin (2 * r⁻¹ * x) / (2 * r⁻¹ * x) ∂μ := by
    gcongr
    refine setIntegral_le_integral ((integrable_const _).sub h_int) <| ae_of_all _ fun x ↦ ?_
    simp only [Pi.zero_apply, sub_nonneg]
    split_ifs with h
    · exact le_rfl
    · exact sin_div_le_one (2 * r⁻¹ * x)
  _ ≤ 2 *
      ‖∫ x, 1 - if x = 0 then 1 else Real.sin (2 * r⁻¹ * x) / (2 * r⁻¹ * x) ∂μ‖ := by
    gcongr
    exact Real.le_norm_self _
  _ = 2⁻¹ * r *
      ‖2 * (r : ℂ)⁻¹ + 2 * r⁻¹ -
        2 * (2 * r⁻¹) * ∫ x, if x = 0 then 1 else Real.sin (2 * r⁻¹ * x) / (2 * r⁻¹ * x) ∂μ‖ := by
    norm_cast
    rw [← two_mul, mul_assoc 2, ← mul_sub, norm_mul, Real.norm_ofNat, ← mul_assoc,
      ← mul_one_sub, norm_mul, Real.norm_of_nonneg (r := 2 * r⁻¹) (by positivity), ← mul_assoc]
    congr
    · ring_nf
      rw [mul_inv_cancel₀ (by positivity), one_mul]
    · rw [integral_sub (integrable_const _) h_int]
      simp
  _ = 2⁻¹ * r * ‖∫ t in (-2 * r⁻¹)..(2 * r⁻¹), 1 - charFun μ t‖ := by
    rw [intervalIntegral.integral_sub intervalIntegrable_const intervalIntegrable_charFun]
    simp only [neg_mul, intervalIntegral.integral_const, sub_neg_eq_add, real_smul, ofReal_add,
      ofReal_mul, ofReal_ofNat, ofReal_inv, mul_one, ge_iff_le]
    rw [integral_charFun_Icc (by positivity)]
    push_cast
    rfl

lemma measure_abs_inner_ge_le_charFun {μ : Measure E} [IsProbabilityMeasure μ] {a : E}
    {r : ℝ} (hr : 0 < r) :
    (μ {x | r < |⟪a, x⟫|}).toReal
      ≤ 2⁻¹ * r * ‖∫ t in (-2 * r⁻¹)..(2 * r⁻¹), 1 - charFun μ (t • a)‖ := by
  let μ' : Measure ℝ := μ.map (fun x ↦ ⟪a, x⟫)
  have : IsProbabilityMeasure μ' := isProbabilityMeasure_map (by fun_prop)
  convert measure_abs_ge_le_charFun (μ := μ') hr with x
  · unfold μ'
    rw [Measure.map_apply]
    · simp
    · fun_prop
    · exact MeasurableSet.preimage measurableSet_Ioi (by fun_prop)
  · unfold μ'
    simp_rw [charFun_apply, inner_smul_right]
    simp only [conj_trivial, ofReal_mul, RCLike.inner_apply]
    rw [integral_map]
    · simp_rw [real_inner_comm a]
    · fun_prop
    · exact Measurable.aestronglyMeasurable <| by fun_prop

lemma measure_Icc_le_charFun {μ : Measure ℝ} [IsProbabilityMeasure μ] {r : ℝ} (hr : 0 < r) :
    (μ (Set.Icc (-r) r)).toReal ≤ 2 * r * ∫ t in (- r⁻¹)..(r⁻¹), ‖charFun μ t‖ := by
  sorry

lemma abs_sub_charFun_le {μ : Measure ℝ} [IsProbabilityMeasure μ] {s t : ℝ} :
    ‖charFun μ s - charFun μ t‖ ≤ 2 * ∫ x, min (|(s - t) * x|) 1 ∂μ := by
  sorry

end bounds

end ProbabilityTheory
