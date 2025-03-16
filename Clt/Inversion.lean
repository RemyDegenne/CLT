/-
Copyright (c) 2024 Thomas Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Zhu, Rémy Degenne
-/
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Clt.Tight

/-!
Inverting the characteristic function
-/

noncomputable section

open Filter MeasureTheory ProbabilityTheory
open scoped Topology

section FromMathlibPR19761

-- See Mathlib#19761, these conditions might change
variable {V : Type*} [SeminormedAddCommGroup V] [Module ℝ V] [InnerProductSpace ℝ V]
    [MeasurableSpace V] [BorelSpace V] [CompleteSpace V] [SecondCountableTopology V]

/-- This is already proven in Mathlib#19761, for FiniteMeasure -/
theorem ProbabilityMeasure.ext_of_charFun_eq (μ ν : ProbabilityMeasure V)
    (h : charFun (μ : Measure V) = charFun ν) :
    μ = ν := by
  sorry

end FromMathlibPR19761

/--
The Lévy continuity theorem https://en.wikipedia.org/wiki/L%C3%A9vy%27s_continuity_theorem.

See blueprint.

The <= direction follows from definition, but it is not needed.
The => direction is much harder:
* If `μs` is tight, then the statement follows in general
  * For each subsequence of `μs`, we need find a sub-subsequence that converges weakly to `μ`.
    This requires Prokhorov's theorem for relative compactness.
* μs is tight in `ℝ^d` if their `charFun`s are equicontinuous at 0
* This is in particular if they converge to a function continuous at 0

This is stated in ℝ, instead of `ℝ^d` as in the blueprint (TODO).
-/
theorem MeasureTheory.ProbabilityMeasure.tendsto_iff_tendsto_charFun {μ : ℕ → ProbabilityMeasure ℝ}
    {μ₀ : ProbabilityMeasure ℝ} :
    Tendsto μ atTop (𝓝 μ₀) ↔
      ∀ t : ℝ, Tendsto (fun n ↦ charFun (μ n) t) atTop (𝓝 (charFun μ₀ t)) := by
  sorry
