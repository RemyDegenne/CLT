/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Matrix.Order
import Mathlib.Probability.Distributions.Gaussian.Basic


/-!
# Multivariate Gaussian distributions
-/

open MeasureTheory ProbabilityTheory Filter Matrix NormedSpace
open scoped ENNReal NNReal Topology RealInnerProductSpace

namespace ProbabilityTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E]
  {d : ℕ}

variable (E) in
/-- Standard Gaussian distribution on `E`. -/
noncomputable
def stdGaussianMulti : Measure E :=
  (Measure.pi (fun _ : Fin (Module.finrank ℝ E) ↦ gaussianReal 0 1)).map
    (fun x ↦ ∑ i, x i • stdOrthonormalBasis ℝ E i)

variable [BorelSpace E]

instance isProbabilityMeasure_stdGaussianMulti : IsProbabilityMeasure (stdGaussianMulti E) where
  measure_univ := by
    rw [stdGaussianMulti, Measure.map_apply (by fun_prop) .univ]
    simp

lemma integrable_eval_pi {i : Fin d} {μ : Fin d → Measure ℝ} [∀ i, IsProbabilityMeasure (μ i)]
    {f : ℝ → ℝ} (hf : Integrable f (μ i)) :
    Integrable (fun a ↦ f (a i)) (Measure.pi μ) := by
  sorry

lemma integral_eval_pi {i : Fin d} {μ : Fin d → Measure ℝ} [∀ i, IsProbabilityMeasure (μ i)]
    {f : ℝ → ℝ} (hf : Integrable f (μ i)) :
    ∫ (a : Fin d → ℝ), f (a i) ∂Measure.pi μ = ∫ x, f x ∂μ i := by
  sorry

lemma isCentered_stdGaussianMulti : ∀ L : StrongDual ℝ E, (stdGaussianMulti E)[L] = 0 := by
  intro L
  rw [stdGaussianMulti, integral_map _ (by fun_prop)]
  swap; · exact (Finset.measurable_sum _ (by fun_prop)).aemeasurable -- todo: add fun_prop tag
  simp only [map_sum, map_smul, smul_eq_mul]
  rw [integral_finset_sum]
  swap
  · intro i _
    refine Integrable.mul_const ?_ _
    convert integrable_eval_pi (i := i) (f := id) ?_
    · infer_instance
    · rw [← memLp_one_iff_integrable]
      exact memLp_id_gaussianReal 1
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  rw [integral_mul_const]
  have : (∫ (a : Fin (Module.finrank ℝ E) → ℝ), a i ∂Measure.pi fun x ↦ gaussianReal 0 1)
      = ∫ x, x ∂gaussianReal 0 1 := by
    convert integral_eval_pi (i := i) ?_
    · rfl
    · infer_instance
    · rw [← memLp_one_iff_integrable]
      exact memLp_id_gaussianReal 1
  simp [this]

lemma variance_dual_stdGaussianMulti (L : StrongDual ℝ E) :
    Var[L; stdGaussianMulti E] = ∑ i, L (stdOrthonormalBasis ℝ E i) ^ 2 := by
  sorry

instance isGaussian_stdGaussianMulti : IsGaussian (stdGaussianMulti E) := by
  refine isGaussian_of_charFunDual_eq fun L ↦ ?_
  rw [integral_complex_ofReal, isCentered_stdGaussianMulti L]
  simp only [Complex.ofReal_zero, zero_mul, zero_sub]
  -- todo: need a lemma `charFunDual_map_sum_pi`
  sorry


open scoped MatrixOrder

/-- Gaussian measure on `ℝ^d` with a given covariance matrix. -/
noncomputable
def multivariateGaussian (μ : EuclideanSpace ℝ (Fin d)) (S : Matrix (Fin d) (Fin d) ℝ) :
    Measure (EuclideanSpace ℝ (Fin d)) :=
  (stdGaussianMulti (EuclideanSpace ℝ (Fin d))).map (fun x ↦ μ + toEuclideanCLM (𝕜 := ℝ)
    (CFC.sqrt S) x)

end ProbabilityTheory
