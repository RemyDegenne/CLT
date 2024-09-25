/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Analysis.Fourier.FourierTransform
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

open scoped RealInnerProductSpace

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

@[continuity]
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

end ProbabilityTheory
