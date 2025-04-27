/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Probability.Variance

/-!
# Covariance of real random variables

-/

open MeasureTheory
open scoped ENNReal NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {X Y Z : Ω → ℝ} {μ : Measure Ω}

variable (X Y μ) in
/-- The covariance of two real-valued random variables defined as
the integral of `(X - 𝔼[X])(Y - 𝔼[Y])`. -/
noncomputable def covariance : ℝ := ∫ ω, (X ω - μ[X]) * (Y ω - μ[Y]) ∂μ

@[inherit_doc]
scoped notation "cov[" X ", " Y "; " μ "]" => ProbabilityTheory.covariance X Y μ

/-- The covariance of the real-valued random variables `X` and `Y`
according to the volume measure. -/
scoped notation "cov[" X ", " Y "]" => cov[X, Y; MeasureTheory.MeasureSpace.volume]

lemma covariance_self {X : Ω → ℝ} (hX : AEMeasurable X μ) :
    cov[X, X; μ] = Var[X; μ] := by
  rw [covariance, variance_eq_integral hX]
  congr with x
  ring

@[simp] lemma covariance_zero_left : cov[0, Y; μ] = 0 := by simp [covariance]

@[simp] lemma covariance_zero_right : cov[X, 0; μ] = 0 := by simp [covariance]

@[simp] lemma covariance_zero_measure : cov[X, Y; (0 : Measure Ω)] = 0 := by simp [covariance]

lemma covariance_add_left [IsFiniteMeasure μ]
    (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) (hZ : MemLp Z 2 μ) :
    cov[X + Y, Z; μ] = cov[X, Z; μ] + cov[Y, Z; μ] := by
  simp_rw [covariance]
  simp only [Pi.add_apply]
  rw [← integral_add]
  · congr with x
    rw [integral_add]
    rotate_left
    · exact hX.integrable (by simp)
    · exact hY.integrable (by simp)
    ring
  · refine MemLp.integrable_mul (q := 2) (p := 2) ?_ ?_
    · exact hX.sub (memLp_const _)
    · exact hZ.sub (memLp_const _)
  · refine MemLp.integrable_mul (q := 2) (p := 2) ?_ ?_
    · exact hY.sub (memLp_const _)
    · exact hZ.sub (memLp_const _)

lemma covariance_add_right [IsFiniteMeasure μ]
    (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) (hZ : MemLp Z 2 μ) :
    cov[X, Y + Z; μ] = cov[X, Y; μ] + cov[X, Z; μ] := by
  simp_rw [covariance]
  simp only [Pi.add_apply]
  rw [← integral_add]
  · congr with x
    rw [integral_add]
    rotate_left
    · exact hY.integrable (by simp)
    · exact hZ.integrable (by simp)
    ring
  · refine MemLp.integrable_mul (q := 2) (p := 2) ?_ ?_
    · exact hX.sub (memLp_const _)
    · exact hY.sub (memLp_const _)
  · refine MemLp.integrable_mul (q := 2) (p := 2) ?_ ?_
    · exact hX.sub (memLp_const _)
    · exact hZ.sub (memLp_const _)

lemma covariance_smul_left (c : ℝ) :
    cov[c • X, Y; μ] = c * cov[X, Y; μ] := by
  simp_rw [covariance]
  simp only [Pi.smul_apply, smul_eq_mul]
  simp_rw [← integral_mul_left, ← mul_assoc, mul_sub]
  congr with ω
  congr <;> rw [integral_mul_left]

lemma covariance_smul_right (c : ℝ) :
    cov[X, c • Y; μ] = c * cov[X, Y; μ] := by
  simp_rw [covariance]
  simp only [Pi.smul_apply, smul_eq_mul]
  simp_rw [← integral_mul_left, ← mul_assoc, mul_comm c, mul_assoc, mul_sub, mul_comm c]
  congr with ω
  rw [integral_mul_right]

@[simp]
lemma covariance_neg_left : cov[-X, Y; μ] = -cov[X, Y; μ] := by
  calc cov[-X, Y; μ]
  _ = cov[(-1 : ℝ) • X, Y; μ] := by simp
  _ = - cov[X, Y; μ] := by rw [covariance_smul_left]; simp

@[simp]
lemma covariance_neg_right : cov[X, -Y; μ] = -cov[X, Y; μ] := by
  calc cov[X, -Y; μ]
  _ = cov[X, (-1 : ℝ) • Y; μ] := by simp
  _ = - cov[X, Y; μ] := by rw [covariance_smul_right]; simp

lemma covariance_sub_left [IsFiniteMeasure μ]
    (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) (hZ : MemLp Z 2 μ) :
    cov[X - Y, Z; μ] = cov[X, Z; μ] - cov[Y, Z; μ] := by
  simp_rw [sub_eq_add_neg]
  rw [covariance_add_left hX hY.neg hZ, covariance_neg_left]

lemma covariance_sub_right [IsFiniteMeasure μ]
    (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) (hZ : MemLp Z 2 μ) :
    cov[X, Y - Z; μ] = cov[X, Y; μ] - cov[X, Z; μ] := by
  simp_rw [sub_eq_add_neg]
  rw [covariance_add_right hX hY hZ.neg, covariance_neg_right]

end ProbabilityTheory
