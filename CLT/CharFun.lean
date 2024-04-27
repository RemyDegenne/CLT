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


open MeasureTheory ComplexConjugate Complex

open scoped RealInnerProductSpace

section character

open scoped FourierTransform Real

/-- The additive character of `ℝ` given by `fun x ↦ exp (- x * I)`. -/
noncomputable
def probFourierChar : Multiplicative ℝ →* circle where
  toFun z := expMapCircle (- Multiplicative.toAdd z)
  map_one' := by simp only; rw [toAdd_one, neg_zero, expMapCircle_zero]
  map_mul' x y := by simp only; rw [toAdd_mul, neg_add, expMapCircle_add]

theorem probFourierChar_apply' (x : ℝ) : probFourierChar x = exp (↑(-x) * I) := rfl

theorem probFourierChar_apply (x : ℝ) : probFourierChar x = exp (- ↑x * I) := by
  simp only [probFourierChar_apply', ofReal_neg]

@[continuity]
theorem continuous_probFourierChar : Continuous probFourierChar :=
  (map_continuous expMapCircle).comp continuous_toAdd.neg

variable {E : Type _} [NormedAddCommGroup E] [CompleteSpace E] [NormedSpace ℂ E]

theorem fourierIntegral_probFourierChar_eq_integral_exp {V : Type _} [AddCommGroup V] [Module ℝ V]
    [MeasurableSpace V] {W : Type _} [AddCommGroup W] [Module ℝ W] (L : V →ₗ[ℝ] W →ₗ[ℝ] ℝ)
    (μ : Measure V) (f : V → E) (w : W) :
    VectorFourier.fourierIntegral probFourierChar μ L f w =
      ∫ v : V, exp (↑(L v w) * I) • f v ∂μ := by
  simp_rw [VectorFourier.fourierIntegral, probFourierChar_apply, ofReal_neg, neg_neg]

end character

open scoped ProbabilityTheory

namespace ProbabilityTheory

variable {E : Type*} [MeasurableSpace E]

/-- The characteristic function of a measure. -/
noncomputable
def charFun [Inner ℝ E] (μ : Measure E) (t : E) : ℂ := ∫ x, exp (⟪t, x⟫ • I) ∂μ

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma charFun_eq_fourierIntegral (μ : Measure E) (t : E) :
    charFun μ t = VectorFourier.fourierIntegral probFourierChar μ sesqFormOfInner
      (fun _ ↦ (1 : ℂ)) t := by
  simp only [charFun, fourierIntegral_probFourierChar_eq_integral_exp, real_smul, smul_eq_mul,
    mul_one]
  congr

@[simp]
lemma charFun_zero (μ : Measure E) [IsProbabilityMeasure μ] : charFun μ 0 = 1 := by
  simp only [charFun, inner_zero_left, zero_smul, exp_zero, integral_const, measure_univ,
    ENNReal.one_toReal, one_smul]

lemma charFun_neg (μ : Measure E) (t : E) : charFun μ (-t) = conj (charFun μ t) := by
  simp [charFun, ← integral_conj, ← exp_conj, conj_ofReal]
  -- todo: conj_ofReal should be simp

lemma norm_charFun_le_one (μ : Measure E) [IsProbabilityMeasure μ] (t : E) : ‖charFun μ t‖ ≤ 1 := by
  rw [charFun_eq_fourierIntegral]
  refine (VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _).trans_eq ?_
  simp only [CstarRing.norm_one, integral_const, smul_eq_mul, mul_one, measure_univ,
    ENNReal.one_toReal]

end ProbabilityTheory
