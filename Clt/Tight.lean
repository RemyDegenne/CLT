/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Tight
import Clt.CharFun

/-!
# Tightness and characteristic functions

-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

variable {E ι : Type*} {mE : MeasurableSpace E} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {μ : ι → Measure E} [∀ i, IsProbabilityMeasure (μ i)]

lemma equiContinuousAt_charFun_zero_of_isTightMeasureSet (hμ : IsTightMeasureSet {μ i | i}) :
    EquicontinuousAt (fun i ↦ charFun (μ i)) 0 := by
  sorry

lemma isTightMeasureSet_of_equiContinuousAt_charFun
    (hμ : EquicontinuousAt (fun i ↦ charFun (μ i)) 0) :
    IsTightMeasureSet {μ i | i} := by
  sorry

lemma isTightMeasureSet_iff_equiContinuousAt_charFun :
    IsTightMeasureSet {μ i | i} ↔ EquicontinuousAt (fun i ↦ charFun (μ i)) 0 :=
  ⟨equiContinuousAt_charFun_zero_of_isTightMeasureSet,
    isTightMeasureSet_of_equiContinuousAt_charFun⟩

/-- Let $(\mu_n)_{n \in \mathbb{N}}$ be measures on $\mathbb{R}^d$ with characteristic functions
$(\hat{\mu}_n)$. If $\hat{\mu}_n$ converges pointwise to a function $f$ which is continuous at 0,
then $(\mu_n)$ is tight. -/
-- TODO: only works in finite dimension.
lemma isTightMeasureSet_of_tendsto_charFun {μ : ℕ → Measure E} [∀ i, IsProbabilityMeasure (μ i)]
    {f : E → ℂ} (hf : ContinuousAt f 0)
    (h : ∀ t, Tendsto (fun n ↦ charFun (μ n) t) atTop (𝓝 (f t))) :
    IsTightMeasureSet {μ i | i} := by
  rw [isTightMeasureSet_iff_equiContinuousAt_charFun]
  sorry

/-- Let $\mu, \mu_1, \mu_2, \ldots$ be probability measures on $\mathbb{R}^d$ with characteristic
functions $\hat{\mu}, \hat{\mu}_1, \hat{\mu}_2, \ldots$. Then $\mu_n \xrightarrow{w} \mu$ iff
for all $t$, $\hat{\mu}_n(t) \to \hat{\mu}(t)$. -/
-- TODO: generalize from ℝ to ℝ^d
theorem ProbabilityMeasure.tendsto_iff_tendsto_charFun {μ : ℕ → ProbabilityMeasure ℝ}
    {μ₀ : ProbabilityMeasure ℝ} :
    Tendsto μ atTop (𝓝 μ₀) ↔
      ∀ t : ℝ, Tendsto (fun n ↦ charFun (μ n) t) atTop (𝓝 (charFun μ₀ t)) := by
  sorry
