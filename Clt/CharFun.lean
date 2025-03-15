/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
import Mathlib.MeasureTheory.Group.Convolution
import Mathlib.Probability.Notation

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

/-- The additive character of `ℝ` given by `fun x ↦ exp (- x * I)`. -/
def probFourierChar : AddChar ℝ Circle where
  toFun x := .exp (-x)
  map_zero_eq_one' := by beta_reduce; rw [neg_zero, Circle.exp_zero]
  map_add_eq_mul' x y := by beta_reduce; rw [neg_add, Circle.exp_add]

theorem probFourierChar_apply' (x : ℝ) : probFourierChar x = exp (↑(-x) * I) := rfl

theorem probFourierChar_apply (x : ℝ) : probFourierChar x = exp (- ↑x * I) := by
  simp only [probFourierChar_apply', ofReal_neg]

@[continuity, fun_prop]
theorem continuous_probFourierChar : Continuous probFourierChar :=
  Circle.exp.continuous.comp continuous_neg

variable {E : Type _} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem fourierIntegral_probFourierChar_eq_integral_exp {V : Type _} [AddCommGroup V] [Module ℝ V]
    [MeasurableSpace V] {W : Type _} [AddCommGroup W] [Module ℝ W] (L : V →ₗ[ℝ] W →ₗ[ℝ] ℝ)
    (μ : Measure V) (f : V → E) (w : W) :
    VectorFourier.fourierIntegral probFourierChar μ L f w =
      ∫ v : V, exp (↑(L v w) * I) • f v ∂μ := by
  simp_rw [VectorFourier.fourierIntegral, Circle.smul_def, probFourierChar_apply, ofReal_neg, neg_neg]

end Character

open scoped ProbabilityTheory

namespace ProbabilityTheory

variable {E : Type*} [MeasurableSpace E]

/-- The characteristic function of a measure. -/
def charFun [Inner ℝ E] (μ : Measure E) (t : E) : ℂ := ∫ x, exp (⟪t, x⟫ • I) ∂μ

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma charFun_eq_fourierIntegral (μ : Measure E) (t : E) :
    charFun μ t = VectorFourier.fourierIntegral probFourierChar μ sesqFormOfInner 1 t := by
  simp only [charFun, real_smul, fourierIntegral_probFourierChar_eq_integral_exp, Pi.one_apply,
    smul_eq_mul, mul_one]
  congr

/-- Relate `charFun` to the "standard" Fourier integral defined by `Real.fourierChar`. -/
lemma charFun_eq_fourierIntegral' (μ : Measure E) (t : E) :
    charFun μ t = VectorFourier.fourierIntegral Real.fourierChar μ sesqFormOfInner 1 (-(2 * π)⁻¹ • t) := by
  have h : (2 : ℂ) * π ≠ 0 := by simp [Real.pi_ne_zero]
  simp only [charFun, real_smul, VectorFourier.fourierIntegral, Real.fourierChar, neg_smul, map_neg,
    _root_.map_smul, smul_eq_mul, neg_neg, AddChar.coe_mk, ← mul_assoc, Pi.one_apply,
    Circle.smul_def, Circle.coe_exp, ofReal_mul, ofReal_ofNat, ofReal_inv, mul_inv_cancel₀ h,
    one_mul, mul_one]
  congr

@[simp]
lemma charFun_zero (μ : Measure E) [IsProbabilityMeasure μ] : charFun μ 0 = 1 := by
  simp only [charFun, inner_zero_left, zero_smul, exp_zero, integral_const, measure_univ,
    ENNReal.one_toReal, one_smul]

lemma charFun_neg (μ : Measure E) (t : E) : charFun μ (-t) = conj (charFun μ t) := by
  simp [charFun, ← integral_conj, ← exp_conj]

lemma norm_charFun_le_one (μ : Measure E) [IsProbabilityMeasure μ] (t : E) : ‖charFun μ t‖ ≤ 1 := by
  rw [charFun_eq_fourierIntegral]
  refine (VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _).trans_eq ?_
  simp only [Pi.one_apply, norm_one, integral_const, measure_univ, ENNReal.one_toReal, smul_eq_mul,
    mul_one]

variable [BorelSpace E] [SecondCountableTopology E]

lemma charFun_map_smul (μ : Measure E) (r : ℝ) (t : E) :
    charFun (μ.map (r • ·)) t = charFun μ (r • t) := by
  unfold charFun
  rw [integral_map]
  · simp_rw [inner_smul_right, ← real_inner_smul_left]
  · apply aemeasurable_id.const_smul
  · apply continuous_exp.comp_aestronglyMeasurable
    apply (measurable_id.const_inner.smul_const I).aestronglyMeasurable

lemma charFun_map_mul (μ : Measure ℝ) (r : ℝ) (t : ℝ) :
    charFun (μ.map (r * ·)) t = charFun μ (r * t) :=
  charFun_map_smul μ r t

/-- The characteristic function of the sum of two independent random variables
is the product of the respective characteristic functions. -/
lemma charFun_conv (μ ν : Measure E) [IsFiniteMeasure μ] [IsFiniteMeasure ν] (t : E) :
    charFun (μ ∗ ν) t = charFun μ t * charFun ν t := by
  unfold charFun Measure.conv
  rw [integral_map, integral_prod]
  · simp_rw [inner_add_right, add_smul, exp_add, integral_mul_left, integral_mul_right]
  · apply (integrable_const (1 : ℝ)).mono
    · apply continuous_exp.comp_aestronglyMeasurable
      apply (measurable_add.const_inner.smul_const I).aestronglyMeasurable
    · simp
  · exact measurable_add.aemeasurable
  · apply continuous_exp.comp_aestronglyMeasurable
    apply (measurable_id.const_inner.smul_const I).aestronglyMeasurable

/--
The characteristic function of the sum of `n` i.i.d. variables with characteristic function `f` is `f ^ n`.

We express this in terms of the pushforward of $P^{\otimes n}$ by summation.

(A more general version not assuming identical distribution is possible)

(Should I express this using pushforward of `iIndepFun` etc?)
-/
lemma charFun_map_sum_pi_const (μ : Measure E) [IsFiniteMeasure μ] (n : ℕ) (t : E) :
    charFun ((Measure.pi fun (_ : Fin n) ↦ μ).map fun x ↦ ∑ i, x i) t = charFun μ t ^ n := by
  induction' n with n ih
  · simp [Measure.map_const, charFun]
  · rw [pow_succ', ← ih, ← charFun_conv]
    congr 1
    have h := (measurePreserving_piFinSuccAbove (fun (_ : Fin (n + 1)) ↦ μ) 0).map_eq
    nth_rw 2 [← μ.map_id]
    rw [Measure.conv, Measure.map_prod_map, ← h, Measure.map_map, Measure.map_map]
    · congr 1 with x
      apply Fin.sum_univ_succ
    all_goals { fun_prop }

section bounds

lemma integral_one_sub_charFun {μ : Measure ℝ} [IsProbabilityMeasure μ] {r : ℝ} (hr : 0 < r) :
    ∫ t in (-r)..r, 1 - charFun μ t
      = 2 * r * ∫ x, (1 - sin (r * x) / (r * x)) ∂μ := by
  sorry

lemma measure_abs_ge_le_charFun {μ : Measure ℝ} [IsProbabilityMeasure μ] {r : ℝ} (hr : 0 < r) :
    (μ {x | r < |x|}).toReal
      ≤ 2⁻¹ * r * ‖∫ t in (-2 * r⁻¹)..(2 * r⁻¹), 1 - charFun μ t‖ := by
  have h := integral_one_sub_charFun (r := 2 * r⁻¹) (μ := μ) (by positivity)
  sorry

lemma measure_Icc_le_charFun {μ : Measure ℝ} [IsProbabilityMeasure μ] {r : ℝ} (hr : 0 < r) :
    (μ (Set.Icc (-r) r)).toReal ≤ 2 * r * ∫ t in (- r⁻¹)..(r⁻¹), ‖charFun μ t‖ := by
  sorry

lemma abs_sub_charFun_le {μ : Measure ℝ} [IsProbabilityMeasure μ] {s t : ℝ} :
    ‖charFun μ s - charFun μ t‖ ≤ 2 * ∫ x, min (|(s - t) * x|) 1 ∂μ := by
  sorry

end bounds

end ProbabilityTheory
