/-
Copyright (c) 2024 Thomas Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Zhu, Rémy Degenne
-/
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.FiniteMeasureExt
import Clt.ExpPoly
import Clt.Tight
import Clt.MomentGenerating

/-!
Inverting the characteristic function
-/

noncomputable section

open Filter MeasureTheory ProbabilityTheory BoundedContinuousFunction Real RCLike
open scoped Topology

section FromMathlibPR19761

-- See Mathlib#19761, these conditions might change
variable {V : Type*} [SeminormedAddCommGroup V] [Module ℝ V] [InnerProductSpace ℝ V]
    [MeasurableSpace V] [BorelSpace V] [CompleteSpace V] [SecondCountableTopology V]

/-- This is already proven in Mathlib#19761, for FiniteMeasure -/
theorem MeasureTheory.ProbabilityMeasure.ext_of_charFun_eq (μ ν : ProbabilityMeasure V)
    (h : charFun (μ : Measure V) = charFun ν) :
    μ = ν := by
  sorry

end FromMathlibPR19761

lemma MeasureTheory.ProbabilityMeasure.tendsto_of_tight_of_separatesPoints
    {E 𝕜 : Type*} [RCLike 𝕜] [MeasurableSpace E]
    [MetricSpace E] [CompleteSpace E] [SecondCountableTopology E] [BorelSpace E]
    {μ : ℕ → ProbabilityMeasure E}
    (h_tight : IsTightMeasureSet {(μ n : Measure E) | n}) {μ₀ : ProbabilityMeasure E}
    {A : StarSubalgebra 𝕜 (E →ᵇ 𝕜)} (hA : (A.map (toContinuousMapStarₐ 𝕜)).SeparatesPoints)
    (heq : ∀ g : E →ᵇ ℝ, (ofRealAm (K := 𝕜)).compLeftContinuousBounded ℝ lipschitzWith_ofReal g ∈ A
      → Tendsto (fun n ↦ ∫ x, g x ∂(μ n)) atTop (𝓝 (∫ x, g x ∂μ₀))) :
    Tendsto μ atTop (𝓝 μ₀) := by
  refine Filter.tendsto_of_subseq_tendsto fun ns hns ↦ ?_
  have h_compact : IsCompact (closure {μ n | n}) :=
    isCompact_closure_of_isTightMeasureSet (S := {μ n | n}) ?_
  swap; · convert h_tight; simp
  obtain ⟨μ', hμ'_mem, φ, hφ_mono, hφ_tendsto⟩ : ∃ μ' ∈ closure {μ n | n},
      ∃ φ, StrictMono φ ∧ Tendsto ((fun n ↦ μ (ns n)) ∘ φ) atTop (𝓝 μ') :=
    IsCompact.tendsto_subseq h_compact (x := fun n ↦ μ (ns n)) fun n ↦ subset_closure ⟨ns n, rfl⟩
  refine ⟨φ, ?_⟩
  suffices μ' = μ₀ from this ▸ hφ_tendsto
  suffices (μ' : Measure E) = μ₀ by ext; rw [this]
  refine ext_of_forall_mem_subalgebra_integral_eq_of_pseudoEMetric_complete_countable' hA
    fun g hg ↦ ?_
  specialize heq g hg
  suffices Tendsto (fun n ↦ ∫ x, g x ∂(μ (ns (φ n)))) atTop (𝓝 (∫ x, g x ∂μ')) from
    tendsto_nhds_unique this <| heq.comp (hns.comp hφ_mono.tendsto_atTop)
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto] at hφ_tendsto
  exact hφ_tendsto g

lemma MeasureTheory.ProbabilityMeasure.tendsto_of_tendsto_charFun {μ : ℕ → ProbabilityMeasure ℝ}
    {μ₀ : ProbabilityMeasure ℝ}
    (h : ∀ t : ℝ, Tendsto (fun n ↦ charFun (μ n) t) atTop (𝓝 (charFun μ₀ t))) :
    Tendsto μ atTop (𝓝 μ₀) := by
  have h_tight : IsTightMeasureSet (α := ℝ) {μ n | n} :=
    isTightMeasureSet_of_tendsto_charFun (by fun_prop) h
  --refine tendsto_of_tight_of_separatesPoints h_tight ?_ ?_
  sorry

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
  refine ⟨fun h t ↦ ?_, tendsto_of_tendsto_charFun⟩
  --rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto] at h
  sorry
