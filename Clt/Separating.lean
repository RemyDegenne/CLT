/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Analysis.SpecialFunctions.MulExpNegMulSqIntegral

/-!
# Separating sets of functions

-/

open BoundedContinuousFunction

open scoped ENNReal

namespace MeasureTheory

variable {α E : Type*} [MeasurableSpace α] [TopologicalSpace α] [NormedRing E] [NormedAlgebra ℝ E]

/-- A subalgebra `A` of the bounded continuous function from `α` to `E` is separating in the
probability measures if for all probability measures `μ ≠ ν`, there exists `f ∈ A` such that
`∫ x, f x ∂μ ≠ ∫ x, f x ∂ν`. -/
structure Separating (A : Subalgebra ℝ (α →ᵇ E)) : Prop where
  exists_ne : ∀ ⦃μ ν : ProbabilityMeasure α⦄, μ ≠ ν → ∃ f ∈ A, ∫ x, f x ∂μ ≠ ∫ x, f x ∂ν

lemma ProbabilityMeasure.ext_of_Separating {μ ν : ProbabilityMeasure α} {A : Subalgebra ℝ (α →ᵇ E)}
    (hA : Separating A) (h : ∀ f ∈ A, ∫ x, f x ∂μ = ∫ x, f x ∂ν) :
    μ = ν := by
  by_contra h_ne
  obtain ⟨f, hfA, hf_ne⟩ := hA.exists_ne h_ne
  exact hf_ne (h f hfA)

end MeasureTheory
