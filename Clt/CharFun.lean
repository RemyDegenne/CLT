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
import Clt.Sinc

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

variable {E : Type*} [MeasurableSpace E] {μ : Measure E} {t : E}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [BorelSpace E] [SecondCountableTopology E]

/-- The characteristic function of a convolution of measures
is the product of the respective characteristic functions. -/
lemma charFun_conv (μ ν : Measure E) [IsFiniteMeasure μ] [IsFiniteMeasure ν] (t : E) :
    charFun (μ ∗ ν) t = charFun μ t * charFun ν t := by
  simp_rw [charFun_apply]
  -- todo: missing lemma `integral_conv`
  unfold Measure.conv
  rw [integral_map, integral_prod]
  · simp_rw [inner_add_left]
    push_cast
    simp_rw [add_mul, Complex.exp_add, integral_mul_left, integral_mul_right]
  · apply (integrable_const (1 : ℝ)).mono
    · exact Measurable.aestronglyMeasurable <| by fun_prop
    · simp
  · fun_prop
  · exact Measurable.aestronglyMeasurable <| by fun_prop

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

lemma integral_exp_Icc (r : ℝ) : ∫ t in -r..r, cexp (t * I) = 2 * Real.sin r :=
  calc ∫ t in -r..r, cexp (t * I)
  _ = (cexp (I * r) - cexp (I * (-r))) / I := by
    simp_rw [mul_comm _ I]
    rw [integral_exp_mul_complex]
    · simp
    · simp
  _ = 2 * Real.sin r := by
    simp only [mul_comm I, exp_mul_I, Complex.cos_neg, Complex.sin_neg, add_sub_add_left_eq_sub,
      div_I, ofReal_sin]
    rw [sub_mul, mul_assoc, mul_assoc, two_mul]
    simp

lemma integral_exp_Icc_eq_sinc (r : ℝ) :
    ∫ t in -r..r, cexp (t * I) = 2 * r * sinc r := by
  rw [integral_exp_Icc]
  by_cases hr : r = 0
  · simp [hr]
  rw [sinc_of_ne_zero hr]
  norm_cast
  field_simp
  ring

lemma integral_charFun_Icc {μ : Measure ℝ} [IsProbabilityMeasure μ] {r : ℝ} (hr : 0 < r) :
    ∫ t in -r..r, charFun μ t = 2 * r * ∫ x, sinc (r * x) ∂μ := by
  have h_int r : Integrable (Function.uncurry fun (x y : ℝ) ↦ cexp (x * y * I))
      ((volume.restrict (Set.Ioc (-r) r)).prod μ) := by
    -- integrable since bounded and the measure is finite
    rw [← integrable_norm_iff]
    swap; · exact Measurable.aestronglyMeasurable <| by fun_prop
    suffices (fun a => ‖Function.uncurry (fun (x y : ℝ) ↦ cexp (x * y * I)) a‖) = fun _ ↦ 1 by
      rw [this]
      fun_prop
    ext p
    rw [← Prod.mk.eta (p := p)]
    norm_cast
    simp only [Function.uncurry_apply_pair, norm_exp_ofReal_mul_I]
  calc ∫ t in -r..r, charFun μ t
  _ = ∫ x in -r..r, ∫ y, cexp (x * y * I) ∂μ := by simp_rw [charFun_apply_real]
  _ = ∫ y, ∫ x in Set.Ioc (-r) r, cexp (x * y * I) ∂volume ∂μ
      - ∫ y, ∫ x in Set.Ioc r (-r), cexp (x * y * I) ∂volume ∂μ := by
    rw [intervalIntegral]
    congr 1
    · rw [integral_integral_swap]
      exact h_int r
    · rw [integral_integral_swap]
      convert h_int (-r)
      simp
  _ = ∫ y, ∫ x in -r..r, cexp (x * y * I) ∂volume ∂μ:= by
    have h_le (y : ℝ) a : ‖∫ (x : ℝ) in Set.Ioc (-a) a, cexp (x * y * I)‖
        ≤ (ENNReal.ofReal (a + a)).toReal := by
      refine (norm_integral_le_integral_norm _).trans_eq ?_
      norm_cast
      simp_rw [norm_exp_ofReal_mul_I]
      simp
    rw [← integral_sub]
    · congr
    · refine Integrable.mono' (integrable_const (ENNReal.ofReal (r + r)).toReal) ?_
        (ae_of_all _ fun y ↦ h_le y r)
      refine StronglyMeasurable.aestronglyMeasurable ?_
      refine StronglyMeasurable.integral_prod_left (f := fun (x y : ℝ) ↦ cexp (x * y * I)) ?_
      exact Measurable.stronglyMeasurable (by fun_prop)
    · refine Integrable.mono' (integrable_const (ENNReal.ofReal (-r + -r)).toReal) ?_
        (ae_of_all _ fun y ↦ ?_)
      · refine StronglyMeasurable.aestronglyMeasurable ?_
        refine StronglyMeasurable.integral_prod_left (f := fun (x y : ℝ) ↦ cexp (x * y * I)) ?_
        exact Measurable.stronglyMeasurable (by fun_prop)
      · convert h_le y (-r) using 2
        simp
  _ = ∫ y, if r * y = 0 then 2 * (r : ℂ)
      else y⁻¹ * ∫ x in -(y * r)..y * r, cexp (x * I) ∂volume ∂μ := by
    congr with y
    by_cases hy : y = 0
    · simp [hy, two_mul]
    simp only [mul_eq_zero, hr.ne', hy, or_self, ↓reduceIte, ofReal_inv]
    have h := intervalIntegral.integral_comp_smul_deriv (E := ℂ) (a := -r) (b := r)
      (f := fun x ↦ y * x) (f' := fun _ ↦ y) (g := fun x ↦ cexp (x * I)) ?_ (by fun_prop)
      (by fun_prop)
    swap
    · intro x hx
      simp_rw [mul_comm y]
      exact hasDerivAt_mul_const _
    simp only [Function.comp_apply, ofReal_mul, real_smul, intervalIntegral.integral_const_mul,
      mul_neg] at h
    rw [← h, ← mul_assoc]
    norm_cast
    simp [mul_comm _ y, mul_inv_cancel₀ hy]
  _ = ∫ x, 2 * (r : ℂ) * sinc (r * x) ∂μ := by
    congr with y
    rw [integral_exp_Icc_eq_sinc]
    split_ifs with hry
    · simp [hry]
    have hy : y ≠ 0 := fun hy ↦ hry (by simp [hy])
    norm_cast
    field_simp
    ring_nf
  _ = 2 * r * ∫ x, sinc (r * x) ∂μ := by
    norm_cast
    rw [integral_complex_ofReal, ← integral_mul_left]

lemma measure_abs_ge_le_charFun {μ : Measure ℝ} [IsProbabilityMeasure μ] {r : ℝ} (hr : 0 < r) :
    (μ {x | r < |x|}).toReal
      ≤ 2⁻¹ * r * ‖∫ t in (-2 * r⁻¹)..(2 * r⁻¹), 1 - charFun μ t‖ := by
  calc (μ {x | r < |x|}).toReal
  _ = (μ {x | 2 < |2 * r⁻¹ * x|}).toReal := by
    congr with x
    simp only [Set.mem_setOf_eq, abs_mul, Nat.abs_ofNat]
    rw [abs_of_nonneg (a := r⁻¹) (by positivity), mul_assoc, ← inv_mul_lt_iff₀ (by positivity),
      inv_mul_cancel₀ (by positivity), lt_inv_mul_iff₀ (by positivity), mul_one]
  _ = ∫ x in {x | 2 < |2 * r⁻¹ * x|}, 1 ∂μ := by simp
  _ = 2 * ∫ x in {x | 2 < |2 * r⁻¹ * x|}, 2⁻¹ ∂μ := by
    rw [← integral_mul_left]
    congr with _
    rw [mul_inv_cancel₀ (by positivity)]
  _ ≤ 2 * ∫ x in {x | 2 < |2 * r⁻¹ * x|}, 1 - sinc (2 * r⁻¹ * x) ∂μ := by
    gcongr (2 : ℝ) * ?_
    refine setIntegral_mono_on ?_
      ((integrable_const _).sub (integrable_sinc_const_mul _)).integrableOn ?_ fun x hx ↦ ?_
    · exact Integrable.integrableOn <| by fun_prop
    · exact MeasurableSet.preimage measurableSet_Ioi (by fun_prop)
    · have hx_ne : 2 * r⁻¹ * x ≠ 0 := by
        intro hx0
        simp only [hx0, Set.mem_setOf_eq, mul_zero, abs_zero] at hx
        linarith
      rw [sinc_of_ne_zero hx_ne, le_sub_iff_add_le, ← le_sub_iff_add_le']
      norm_num
      rw [one_div]
      refine (sin_div_le_inv_abs _).trans ?_
      exact (inv_le_inv₀ (by positivity) (by positivity)).mpr (le_of_lt hx)
  _ ≤ 2 * ∫ x, 1 - sinc (2 * r⁻¹ * x) ∂μ := by
    gcongr
    refine setIntegral_le_integral ((integrable_const _).sub (integrable_sinc_const_mul _))
      <| ae_of_all _ fun x ↦ ?_
    simp only [Pi.zero_apply, sub_nonneg]
    exact sinc_le_one (2 * r⁻¹ * x)
  _ ≤ 2 * ‖∫ x, 1 - sinc (2 * r⁻¹ * x) ∂μ‖ := by
    gcongr
    exact Real.le_norm_self _
  _ = 2⁻¹ * r *
      ‖2 * (r : ℂ)⁻¹ + 2 * r⁻¹ - 2 * (2 * r⁻¹) * ∫ x, sinc (2 * r⁻¹ * x) ∂μ‖ := by
    norm_cast
    rw [← two_mul, mul_assoc 2, ← mul_sub, norm_mul, Real.norm_ofNat, ← mul_assoc,
      ← mul_one_sub, norm_mul, Real.norm_of_nonneg (r := 2 * r⁻¹) (by positivity), ← mul_assoc]
    congr
    · ring_nf
      rw [mul_inv_cancel₀ (by positivity), one_mul]
    · rw [integral_sub (integrable_const _) (integrable_sinc_const_mul _)]
      simp
  _ = 2⁻¹ * r * ‖∫ t in (-2 * r⁻¹)..(2 * r⁻¹), 1 - charFun μ t‖ := by
    rw [intervalIntegral.integral_sub intervalIntegrable_const intervalIntegrable_charFun, neg_mul,
      integral_charFun_Icc (by positivity)]
    simp

lemma measure_abs_inner_ge_le_charFun {μ : Measure E} [IsProbabilityMeasure μ] {a : E}
    {r : ℝ} (hr : 0 < r) :
    (μ {x | r < |⟪a, x⟫|}).toReal
      ≤ 2⁻¹ * r * ‖∫ t in -2 * r⁻¹..2 * r⁻¹, 1 - charFun μ (t • a)‖ := by
  have : IsProbabilityMeasure (μ.map (fun x ↦ ⟪a, x⟫)) := isProbabilityMeasure_map (by fun_prop)
  convert measure_abs_ge_le_charFun (μ := μ.map (fun x ↦ ⟪a, x⟫)) hr with x
  · rw [Measure.map_apply]
    · simp
    · fun_prop
    · exact MeasurableSet.preimage measurableSet_Ioi (by fun_prop)
  · simp_rw [charFun_apply, inner_smul_right]
    simp only [conj_trivial, ofReal_mul, RCLike.inner_apply]
    rw [integral_map]
    · simp_rw [real_inner_comm a]
    · fun_prop
    · exact Measurable.aestronglyMeasurable <| by fun_prop

lemma measure_Icc_le_charFun {μ : Measure ℝ} [IsProbabilityMeasure μ] {r : ℝ} (hr : 0 < r) :
    (μ (Set.Icc (-r) r)).toReal ≤ 2 * r * ∫ t in (- r⁻¹)..(r⁻¹), ‖charFun μ t‖ := by
  sorry

lemma abs_sub_charFun_le {μ : Measure ℝ} [IsProbabilityMeasure μ] {s t : ℝ} :
    ‖charFun μ s - charFun μ t‖ ≤ 2 * ∫ x, min (|(s - t) * x|) 1 ∂μ := by
  sorry

end bounds

end ProbabilityTheory
