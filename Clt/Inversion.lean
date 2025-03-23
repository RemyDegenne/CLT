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

lemma RCLike.lipschitzWith_re {𝕜 : Type*} [RCLike 𝕜] :
    LipschitzWith 1 (re (K := 𝕜)) := by
  intro x y
  simp only [ENNReal.coe_one, one_mul, edist_eq_enorm_sub]
  calc ‖re x - re y‖ₑ
  _ = ‖re (x - y)‖ₑ := by rw [ AddMonoidHom.map_sub re x y]
  _ ≤ ‖x - y‖ₑ := by rw [enorm_le_iff_norm_le]; exact norm_re_le_norm (x - y)

lemma RCLike.lipschitzWith_im {𝕜 : Type*} [RCLike 𝕜] :
    LipschitzWith 1 (im (K := 𝕜)) := by
  intro x y
  simp only [ENNReal.coe_one, one_mul, edist_eq_enorm_sub]
  calc ‖im x - im y‖ₑ
  _ = ‖im (x - y)‖ₑ := by rw [ AddMonoidHom.map_sub im x y]
  _ ≤ ‖x - y‖ₑ := by rw [enorm_le_iff_norm_le]; exact norm_im_le_norm (x - y)

theorem MeasureTheory.ProbabilityMeasure.tendsto_iff_forall_integral_complex_tendsto
    {γ Ω : Type*} {F : Filter γ} {mΩ : MeasurableSpace Ω} [TopologicalSpace Ω]
    [OpensMeasurableSpace Ω]
    {μs : γ → ProbabilityMeasure Ω} {μ : ProbabilityMeasure Ω} :
    Tendsto μs F (𝓝 μ) ↔
      ∀ f : Ω →ᵇ ℂ,
        Tendsto (fun i ↦ ∫ ω, f ω ∂(μs i : Measure Ω)) F (𝓝 (∫ ω, f ω ∂(μ : Measure Ω))) := by
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
  refine ⟨fun h f ↦ ?_, fun h f ↦ ?_⟩
  · rw [← integral_re_add_im (integrable μ f)]
    simp_rw [← integral_re_add_im (integrable (μs _) f)]
    refine Tendsto.add ?_ ?_
    · specialize h (f.comp re RCLike.lipschitzWith_re)
      simp only [re_to_complex, Complex.coe_algebraMap]
      simp only [comp_apply, re_to_complex] at h
      exact Tendsto.comp (continuous_ofReal.tendsto _) h
    · specialize h (f.comp im RCLike.lipschitzWith_im)
      simp only [im_to_complex, Complex.coe_algebraMap]
      simp only [comp_apply, im_to_complex] at h
      exact (Tendsto.comp (continuous_ofReal.tendsto _) h).mul_const _
  · specialize h ((ofRealAm (K := ℂ)).compLeftContinuousBounded ℝ lipschitzWith_ofReal f)
    simp only [AlgHom.compLeftContinuousBounded_apply_apply, ofRealAm_coe,
      Complex.coe_algebraMap] at h
    simp_rw [integral_complex_ofReal] at h
    exact tendsto_ofReal_iff.mp h

lemma RCLike.isUniformEmbedding_ofReal {𝕜 : Type*} [RCLike 𝕜] :
    IsUniformEmbedding ((↑) : ℝ → 𝕜) :=
  ofRealLI.isometry.isUniformEmbedding

lemma _root_.Filter.tendsto_ofReal_iff' {α 𝕜 : Type*} [RCLike 𝕜]
    {l : Filter α} {f : α → ℝ} {x : ℝ} :
    Tendsto (fun x ↦ (f x : 𝕜)) l (𝓝 (x : 𝕜)) ↔ Tendsto f l (𝓝 x) :=
  RCLike.isUniformEmbedding_ofReal.isClosedEmbedding.tendsto_nhds_iff.symm

theorem MeasureTheory.ProbabilityMeasure.tendsto_iff_forall_integral_rcLike_tendsto
    {γ Ω : Type*} (𝕜 : Type*) [RCLike 𝕜]
    {F : Filter γ} {mΩ : MeasurableSpace Ω} [TopologicalSpace Ω] [OpensMeasurableSpace Ω]
    {μs : γ → ProbabilityMeasure Ω} {μ : ProbabilityMeasure Ω} :
    Tendsto μs F (𝓝 μ) ↔
      ∀ f : Ω →ᵇ 𝕜,
        Tendsto (fun i ↦ ∫ ω, f ω ∂(μs i : Measure Ω)) F (𝓝 (∫ ω, f ω ∂(μ : Measure Ω))) := by
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
  refine ⟨fun h f ↦ ?_, fun h f ↦ ?_⟩
  · rw [← integral_re_add_im (integrable μ f)]
    simp_rw [← integral_re_add_im (integrable (μs _) f)]
    refine Tendsto.add ?_ ?_
    · exact Tendsto.comp (continuous_ofReal.tendsto _) (h (f.comp re RCLike.lipschitzWith_re))
    · exact (Tendsto.comp (continuous_ofReal.tendsto _)
        (h (f.comp im RCLike.lipschitzWith_im))).mul_const _
  · specialize h ((ofRealAm (K := 𝕜)).compLeftContinuousBounded ℝ lipschitzWith_ofReal f)
    simp only [AlgHom.compLeftContinuousBounded_apply_apply, ofRealAm_coe,
      Complex.coe_algebraMap, integral_ofReal] at h
    exact tendsto_ofReal_iff'.mp h

lemma MeasureTheory.ProbabilityMeasure.tendsto_of_tight_of_separatesPoints
    {E 𝕜 : Type*} [RCLike 𝕜] [MeasurableSpace E]
    [MetricSpace E] [CompleteSpace E] [SecondCountableTopology E] [BorelSpace E]
    {μ : ℕ → ProbabilityMeasure E}
    (h_tight : IsTightMeasureSet {(μ n : Measure E) | n}) {μ₀ : ProbabilityMeasure E}
    {A : StarSubalgebra 𝕜 (E →ᵇ 𝕜)} (hA : (A.map (toContinuousMapStarₐ 𝕜)).SeparatesPoints)
    (heq : ∀ g ∈ A, Tendsto (fun n ↦ ∫ x, g x ∂(μ n)) atTop (𝓝 (∫ x, g x ∂μ₀))) :
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
  refine ext_of_forall_mem_subalgebra_integral_eq_of_pseudoEMetric_complete_countable hA
    fun g hg ↦ ?_
  specialize heq g hg
  suffices Tendsto (fun n ↦ ∫ x, g x ∂(μ (ns (φ n)))) atTop (𝓝 (∫ x, g x ∂μ')) from
    tendsto_nhds_unique this <| heq.comp (hns.comp hφ_mono.tendsto_atTop)
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_rcLike_tendsto 𝕜] at hφ_tendsto
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
