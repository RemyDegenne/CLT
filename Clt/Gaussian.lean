/-
Copyright (c) 2024 Thomas Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Zhu, Rémy Degenne
-/
import Mathlib.Probability.Distributions.Gaussian
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Clt.CharFun

/-!
Properties of Gaussian distributions and its characteristic function.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Complex
open scoped NNReal Real

namespace ProbabilityTheory

variable (μ : ℝ) (v : ℝ≥0)

theorem charFun_gaussianReal : charFun (gaussianReal μ v) t = exp (t * μ * I - v * t ^ 2 / 2) := by
  unfold charFun gaussianReal
  split_ifs with hv
  · simp [hv]
  calc
    _ = ∫ x, (gaussianPDFReal μ v x).toNNReal • cexp (inner t x • I) ∂ℙ :=
      integral_withDensity_eq_integral_smul (measurable_gaussianPDFReal μ v).real_toNNReal _
    _ = ∫ x, gaussianPDFReal μ v x * cexp (t * x * I) ∂ℙ := by
      congr; ext x
      simp [NNReal.smul_def, Real.coe_toNNReal _ (gaussianPDFReal_nonneg μ v x)]
    _ = (√(2 * π * v))⁻¹ * ∫ x : ℝ, cexp (-(2 * v)⁻¹ * x ^ 2 + (t * I + μ / v) * x + -μ ^ 2 / (2 * v)) ∂ℙ := by
      unfold gaussianPDFReal
      simp_rw [ofReal_mul, mul_assoc _ _ (exp _), integral_mul_left, ofReal_exp, ← exp_add]
      congr; ext x; congr 1
      push_cast
      ring
    _ = (√(2 * π * v))⁻¹ * (π / - -(2 * v)⁻¹) ^ (1 / 2 : ℂ) * cexp (-μ ^ 2 / (2 * v) - (t * I + μ / v) ^ 2 / (4 * -(2 * v)⁻¹)) := by
      rw [integral_cexp_quadratic (by simpa using pos_iff_ne_zero.mpr hv), ← mul_assoc]
    _ = 1 * cexp (-μ ^ 2 / (2 * v) - (t * I + μ / v) ^ 2 / (4 * -(2 * v)⁻¹)) := by
      congr 1
      field_simp [Real.sqrt_eq_rpow]
      rw [ofReal_cpow (by positivity)]
      push_cast
      ring_nf
    _ = _ := by
      rw [one_mul]
      congr 1
      have : (v : ℂ) ≠ 0 := by simpa
      field_simp
      ring_nf
      simp

end ProbabilityTheory
