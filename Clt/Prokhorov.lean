/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Tight

open MeasureTheory
open scoped ENNReal Topology


/-- **Prokhorov's theorem** -/
theorem isTightMeasureSet_iff_isCompact_closure
  {E : Type*} {mE : MeasurableSpace E} [MetricSpace E] [CompleteSpace E]
  [SecondCountableTopology E] [BorelSpace E] {S : Set (ProbabilityMeasure E)} :
    IsTightMeasureSet {((μ : ProbabilityMeasure E) : Measure E) | μ ∈ S}
      ↔ IsCompact (closure S) := by
  sorry -- do not work on this. Somebody claimed it.

lemma isCompact_closure_of_isTightMeasureSet
    {E : Type*} {mE : MeasurableSpace E} [MetricSpace E] [BorelSpace E]
    {S : Set (ProbabilityMeasure E)}
    (hS : IsTightMeasureSet {((μ : ProbabilityMeasure E) : Measure E) | μ ∈ S}) :
    IsCompact (closure S) := by
  sorry
