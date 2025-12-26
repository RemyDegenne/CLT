/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Miyahara Kō, Lawrence Wu
-/
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.Topology.MetricSpace.Sequences
import Mathlib.Order.Monotone.Union

open MeasureTheory Filter Topology TopologicalSpace Set EMetric
open scoped NNReal ENNReal

/-- **Prokhorov's theorem** -/
theorem isTightMeasureSet_iff_isCompact_closure
  {E : Type*} {mE : MeasurableSpace E} [MetricSpace E] [CompleteSpace E]
  [SecondCountableTopology E] [BorelSpace E] {S : Set (ProbabilityMeasure E)} :
    IsTightMeasureSet {((μ : ProbabilityMeasure E) : Measure E) | μ ∈ S}
      ↔ IsCompact (closure S) := by
  sorry -- do not work on this. Somebody claimed it.

/- One direction is already available in Mathlib:
lemma isCompact_closure_of_isTightMeasureSet {S : Set (ProbabilityMeasure E)}
    (hS : IsTightMeasureSet {((μ : ProbabilityMeasure E) : Measure E) | μ ∈ S}) :
    IsCompact (closure S) :=
-/
