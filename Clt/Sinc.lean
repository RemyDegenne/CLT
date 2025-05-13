/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-!

# Sinc function

-/

open MeasureTheory Real

namespace Real

variable {x : ℝ}

/-- The function `sin x / x` mofified to take the value 1 at 0, which makes it continuous. -/
noncomputable def sinc (x : ℝ) : ℝ := if x = 0 then 1 else Real.sin x / x

lemma sinc_apply : sinc x = if x = 0 then 1 else Real.sin x / x := rfl

@[simp]
lemma sinc_zero : sinc 0 = 1 := by simp [sinc]

lemma sinc_of_ne_zero (hx : x ≠ 0) : sinc x = Real.sin x / x := by simp [sinc, hx]

lemma abs_sinc_le_one (x : ℝ) : |sinc x| ≤ 1 := by
  by_cases hx : x = 0
  · simp [hx]
  rw [sinc_of_ne_zero hx, abs_div]
  refine div_le_of_le_mul₀ (abs_nonneg _) zero_le_one ?_
  rw [one_mul]
  exact Real.abs_sin_le_abs

lemma sinc_le_one (x : ℝ) : sinc x ≤ 1 := (abs_le.mp (abs_sinc_le_one x)).2

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

end Real

@[fun_prop, measurability]
lemma measurable_sinc : Measurable sinc := Measurable.ite (by simp) (by fun_prop) (by fun_prop)

@[fun_prop, measurability]
lemma stronglyMeasurable_sinc : StronglyMeasurable sinc := measurable_sinc.stronglyMeasurable

@[fun_prop]
lemma integrable_sinc {μ : Measure ℝ} [IsFiniteMeasure μ] :
    Integrable sinc μ := by
  refine Integrable.mono' (g := fun _ ↦ 1) (integrable_const _) ?_ <| ae_of_all _ fun x ↦ ?_
  · exact stronglyMeasurable_sinc.aestronglyMeasurable
  · rw [Real.norm_eq_abs]
    exact abs_sinc_le_one x

lemma integrable_sinc_const_mul {μ : Measure ℝ} [IsFiniteMeasure μ] (r : ℝ) :
    Integrable (fun x ↦ sinc (r * x)) μ :=
  (integrable_map_measure stronglyMeasurable_sinc.aestronglyMeasurable (by fun_prop)).mp
    integrable_sinc
