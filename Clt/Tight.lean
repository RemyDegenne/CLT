/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.MeasureTheory.Measure.Regular

/-!
# Characteristic function of a measure

## Main definitions

* `Tight`: A set `S` of measures is tight if for all `0 < ε`, there exists `K` compact such that
  for all `μ` in `S`, `μ Kᶜ ≤ ε`.

## Main statements

* `fooBar_unique`

## Notation



## Implementation details



-/

open scoped ENNReal

namespace MeasureTheory

variable {α : Type*} {mα : MeasurableSpace α} {μ : Measure α}
  [TopologicalSpace α]

/-- A set `S` of measures is tight if for all `0 < ε`, there exists `K` compact such that for all
`μ` in `S`, `μ Kᶜ ≤ ε`. -/
def Tight (S : Set (Measure α)) : Prop :=
  ∀ ε : ℝ≥0∞, 0 < ε → ∃ K : Set α, IsCompact K ∧ ∀ μ ∈ S, μ Kᶜ ≤ ε

-- TODO: the T2Space hypothesis is here only to make compact sets closed. It could be removed if
-- InnerRegular was about compact and closed sets, and not only compact sets.
lemma tight_singleton [T2Space α] [OpensMeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] [μ.InnerRegular] :
    Tight {μ} := by
  cases eq_zero_or_neZero μ with
  | inl hμ =>
    rw [hμ]
    refine fun _ _ ↦ ⟨∅, isCompact_empty, ?_⟩
    simp
  | inr hμ =>
    let r := μ Set.univ
    have hr : 0 < r := by simp [hμ.out]
    intro ε hε
    cases lt_or_ge ε r with
    | inl hεr =>
      have hεr' : r - ε < r := ENNReal.sub_lt_self (measure_ne_top μ _) hr.ne' hε.ne'
      obtain ⟨K, _, hK_compact, hKμ⟩ :=
        (MeasurableSet.univ : MeasurableSet (Set.univ : Set α)).exists_lt_isCompact hεr'
      refine ⟨K, hK_compact, fun μ' hμ' ↦ ?_⟩
      simp only [Set.mem_singleton_iff] at hμ'
      rw [hμ', measure_compl hK_compact.isClosed.measurableSet (measure_ne_top μ _),
        tsub_le_iff_right]
      rw [ENNReal.sub_lt_iff_lt_right (ne_top_of_lt hεr) hεr.le, add_comm] at hKμ
      exact hKμ.le
    | inr hεr =>
      refine ⟨∅, isCompact_empty, ?_⟩
      intro μ' hμ'
      simp only [Set.mem_singleton_iff] at hμ'
      rw [hμ', Set.compl_empty]
      exact hεr

end MeasureTheory
