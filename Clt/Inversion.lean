import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Clt.CharFun

/-!
Inverting the characteristic function
-/

noncomputable section

open Filter MeasureTheory ProbabilityTheory
open scoped Topology

section FromMathlibPR19761

-- See Mathlib#19761, these conditions might change
variable {V : Type*} [SeminormedAddCommGroup V] [Module ℝ V] [InnerProductSpace ℝ V] [MeasurableSpace V]
    [BorelSpace V] [CompleteSpace V] [SecondCountableTopology V]

/-- This is already proven in Mathlib#19761, for FiniteMeasure -/
theorem ProbabilityMeasure.ext_of_charFun_eq (μ ν : ProbabilityMeasure V) (h : charFun (μ : Measure V) = charFun ν) : μ = ν := by
  sorry

end FromMathlibPR19761

namespace ProbabilityTheory

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
theorem charFun_tendsto_iff_measure_tendsto (μ : ProbabilityMeasure ℝ) (μs : ℕ → ProbabilityMeasure ℝ) :
    (∀ t, Tendsto (fun i ↦ charFun (μs i) t) atTop (𝓝 (charFun (μ : Measure ℝ) t))) ↔ Tendsto μs atTop (𝓝 μ) := by
  sorry

end ProbabilityTheory
