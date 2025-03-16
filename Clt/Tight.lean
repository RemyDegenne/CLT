/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Clt.CharFun
import Clt.Prokhorov

/-!
# Tightness and characteristic functions

-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

variable {E ι : Type*} {mE : MeasurableSpace E} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {μ : ι → Measure E} [∀ i, IsProbabilityMeasure (μ i)]

lemma equicontinuousAt_charFun_zero_of_isTightMeasureSet (hμ : IsTightMeasureSet {μ i | i}) :
    EquicontinuousAt (fun i ↦ charFun (μ i)) 0 := by
  sorry

lemma isTightMeasureSet_of_equicontinuousAt_charFun
    (hμ : EquicontinuousAt (fun i ↦ charFun (μ i)) 0) :
    IsTightMeasureSet {μ i | i} := by
  sorry

lemma isTightMeasureSet_iff_equicontinuousAt_charFun :
    IsTightMeasureSet {μ i | i} ↔ EquicontinuousAt (fun i ↦ charFun (μ i)) 0 :=
  ⟨equicontinuousAt_charFun_zero_of_isTightMeasureSet,
    isTightMeasureSet_of_equicontinuousAt_charFun⟩

/-- Let $(\mu_n)_{n \in \mathbb{N}}$ be measures on $\mathbb{R}^d$ with characteristic functions
$(\hat{\mu}_n)$. If $\hat{\mu}_n$ converges pointwise to a function $f$ which is continuous at 0,
then $(\mu_n)$ is tight. -/
-- TODO: only works in finite dimension.
lemma isTightMeasureSet_of_tendsto_charFun {μ : ℕ → Measure E} [∀ i, IsProbabilityMeasure (μ i)]
    {f : E → ℂ} (hf : ContinuousAt f 0)
    (h : ∀ t, Tendsto (fun n ↦ charFun (μ n) t) atTop (𝓝 (f t))) :
    IsTightMeasureSet {μ i | i} := by
  sorry
