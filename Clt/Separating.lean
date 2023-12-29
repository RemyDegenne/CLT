/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Topology.ContinuousFunction.Compact
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Separating sets of functions

-/

open BoundedContinuousFunction

open scoped ENNReal

namespace MeasureTheory

variable {α E : Type*} {mα : MeasurableSpace α} [TopologicalSpace α]
  [NormedRing E] [NormedAlgebra ℝ E]

/-- A subalgebra `A` of the bounded continuous function from `α` to `E` is separating in the
probability measures if for all probability measures `μ ≠ ν`, there exists `f ∈ A` such that
`∫ x, f x ∂μ ≠ ∫ x, f x ∂ν`. -/
structure Separating (A : Subalgebra ℝ (α →ᵇ E)) : Prop :=
(exists_ne : ∀ μ ν : ProbabilityMeasure α, μ ≠ ν → ∃ f ∈ A, ∫ x, f x ∂μ ≠ ∫ x, f x ∂ν)


end MeasureTheory
