/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
import Mathlib.MeasureTheory.Group.Convolution
import Mathlib.Probability.Notation
import Mathlib

/-!
# Characteristic function of a measure

## Main definitions

* `FooBar`

## Main statements

* `fooBar_unique`

## Notation



## Implementation details



-/


noncomputable section

open MeasureTheory ComplexConjugate Complex Real

open scoped RealInnerProductSpace Real

section Character

open scoped FourierTransform Real

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

@[fun_prop]
lemma integrable_probChar {μ : Measure ℝ} [IsProbabilityMeasure μ] (y : ℝ) :
    Integrable (fun x ↦ (Real.probChar (y * x) : ℂ)) μ := by
  rw [← integrable_norm_iff]
  · simp
  · exact Measurable.aestronglyMeasurable <| by fun_prop

end

end Character

open BoundedContinuousFunction

namespace ProbabilityTheory

variable {E : Type*} [MeasurableSpace E] {μ ν : Measure E} {t : E}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [BorelSpace E] [SecondCountableTopology E]

/--
The characteristic function of the sum of `n` i.i.d. variables with characteristic function `f` is
`f ^ n`.

We express this in terms of the pushforward of $P^{\otimes n}$ by summation.

(A more general version not assuming identical distribution is possible)

(Should I express this using pushforward of `iIndepFun` etc?)
-/
lemma charFun_map_sum_pi_const (μ : Measure E) [IsFiniteMeasure μ] (n : ℕ) (t : E) :
    charFun ((Measure.pi fun (_ : Fin n) ↦ μ).map fun x ↦ ∑ i, x i) t = charFun μ t ^ n := by
  induction' n with n ih
  · simp [Measure.map_const, charFun_apply]
  · rw [pow_succ', ← ih, ← charFun_conv]
    congr 1
    have h := (measurePreserving_piFinSuccAbove (fun (_ : Fin (n + 1)) ↦ μ) 0).map_eq
    nth_rw 2 [← μ.map_id]
    rw [Measure.conv, Measure.map_prod_map, ← h, Measure.map_map, Measure.map_map]
    · congr 1 with x
      apply Fin.sum_univ_succ
    all_goals { fun_prop }

section bounds

lemma measure_Icc_le_charFun {μ : Measure ℝ} [IsProbabilityMeasure μ] {r : ℝ} (hr : 0 < r) :
    (μ (Set.Icc (-r) r)).toReal ≤ 2 * r * ∫ t in (- r⁻¹)..(r⁻¹), ‖charFun μ t‖ := by
  sorry

lemma abs_sub_charFun_le {μ : Measure ℝ} [IsProbabilityMeasure μ] {s t : ℝ} :
    ‖charFun μ s - charFun μ t‖ ≤ 2 * ∫ x, min (|(s - t) * x|) 1 ∂μ := by
  sorry

end bounds

end ProbabilityTheory
