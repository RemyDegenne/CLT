/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Probability.Distributions.Gaussian
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Clt.CharFun
import Clt.MomentGenerating

/-!
# Characteristic function in Banach spaces
-/

open Real Complex NormedSpace
open scoped ENNReal NNReal

lemma IsBoundedBilinearMap.symm {E F G 𝕜 : Type*} [NontriviallyNormedField 𝕜]
    [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]
    [SeminormedAddCommGroup G] [NormedSpace 𝕜 G]
    {f : E × F → G} (h : IsBoundedBilinearMap 𝕜 f) :
    IsBoundedBilinearMap 𝕜 (fun p ↦ f (p.2, p.1)) where
  add_left x₁ x₂ y := h.add_right _ _ _
  smul_left c x y := h.smul_right _ _ _
  add_right x y₁ y₂ := h.add_left _ _ _
  smul_right c x y := h.smul_left _ _ _
  bound := by
    obtain ⟨C, hC_pos, hC⟩ := h.bound
    exact ⟨C, hC_pos, fun x y ↦ (hC y x).trans_eq (by ring)⟩

lemma ContinuousLinearMap.comp_inl_add_comp_inr
    {E F : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    [SeminormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E × F →L[ℝ] ℝ) (v : E × F) :
    L.comp (.inl ℝ E F) v.1 + L.comp (.inr ℝ E F) v.2 = L v := by
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.inl_apply, ContinuousLinearMap.inr_apply, ← ContinuousLinearMap.map_add]
  simp

namespace BoundedContinuousFunction

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]

/-- The bounded continuous function `x ↦ exp (L x * I)`, for a continuous linear form `L`. -/
noncomputable
def probCharCLM (L : E →L[ℝ] ℝ) : E →ᵇ ℂ :=
  char continuous_probChar (L := isBoundedBilinearMap_apply.symm.toContinuousLinearMap.toLinearMap₂)
    isBoundedBilinearMap_apply.symm.continuous L

lemma probCharCLM_apply (L : E →L[ℝ] ℝ) (x : E) : probCharCLM L x = exp (L x * I) := rfl

@[simp]
lemma probCharCLM_zero : probCharCLM (0 : E →L[ℝ] ℝ) = 1 := by simp [probCharCLM]

end BoundedContinuousFunction

namespace MeasureTheory

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {mE : MeasurableSpace E}
  [NormedAddCommGroup F] [NormedSpace ℝ F] {mF : MeasurableSpace F}
  {μ : Measure E} {ν : Measure F}

/-- The characteristic function of a measure in a normed space, function from `E →L[ℝ] ℝ` to `ℂ`
with `charFunCLM μ L = ∫ v, exp (L v * I) ∂μ`. -/
noncomputable
def charFunCLM (μ : Measure E) (L : E →L[ℝ] ℝ) : ℂ :=
  ∫ v, BoundedContinuousFunction.probCharCLM L v ∂μ

lemma charFunCLM_apply (L : E →L[ℝ] ℝ) : charFunCLM μ L = ∫ v, exp (L v * I) ∂μ := rfl

lemma charFunCLM_prod [SFinite μ] [SFinite ν] (L : E × F →L[ℝ] ℝ) :
    charFunCLM (μ.prod ν) L
      = charFunCLM μ (L.comp (.inl ℝ E F)) * charFunCLM ν (L.comp (.inr ℝ E F)) := by
  let L₁ : E →L[ℝ] ℝ := L.comp (.inl ℝ E F)
  let L₂ : F →L[ℝ] ℝ := L.comp (.inr ℝ E F)
  simp_rw [charFunCLM_apply, ← L.comp_inl_add_comp_inr, ofReal_add, add_mul,
    Complex.exp_add]
  rw [integral_prod_mul (f := fun x ↦ cexp ((L₁ x * I))) (g := fun x ↦ cexp ((L₂ x * I)))]

lemma charFunCLM_eq_charFun_map_one [BorelSpace E] (L : E →L[ℝ] ℝ) :
    charFunCLM μ L = charFun (μ.map L) 1 := by
  rw [charFunCLM_apply]
  have : ∫ x, cexp (L x * I) ∂μ = ∫ x, cexp (x * I) ∂(μ.map L) := by
    rw [integral_map]
    · fun_prop
    · exact Measurable.aestronglyMeasurable <| by fun_prop
  rw [this, charFun_apply]
  simp

lemma charFun_map_eq_charFunCLM_smul [BorelSpace E] (L : E →L[ℝ] ℝ) (u : ℝ) :
    charFun (μ.map L) u = charFunCLM μ (u • L) := by
  rw [charFunCLM_apply]
  have : ∫ x, cexp ((u • L) x * I) ∂μ = ∫ x, cexp (u * x * I) ∂(μ.map L) := by
    rw [integral_map]
    · simp
    · fun_prop
    · exact Measurable.aestronglyMeasurable <| by fun_prop
  rw [this, charFun_apply]
  simp

lemma charFunCLM_map [BorelSpace E] [BorelSpace F] {μ : Measure E}
    (L : E →L[ℝ] F) (L' : F →L[ℝ] ℝ) :
    charFunCLM (μ.map L) L' = charFunCLM μ (L'.comp L) := by
  rw [charFunCLM_eq_charFun_map_one, charFunCLM_eq_charFun_map_one,
    Measure.map_map (by fun_prop) (by fun_prop)]
  simp

variable [CompleteSpace E] [BorelSpace E] [SecondCountableTopology E]

/-- If two finite measures have the same characteristic function, then they are equal. -/
theorem ext_of_charFunCLM {μ ν : Measure E} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : charFunCLM μ = charFunCLM ν) :
    μ = ν := by
  refine ext_of_integral_char_eq continuous_probChar probChar_ne_one
    ?_ ?_ (fun L ↦ funext_iff.mp h L)
  · intro v hv
    rw [ne_eq, LinearMap.ext_iff]
    simp only [ContinuousLinearMap.toLinearMap₂_apply, LinearMap.zero_apply, not_forall]
    change ∃ L : E →L[ℝ] ℝ, L v ≠ 0
    by_contra! h
    exact hv (eq_zero_of_forall_dual_eq_zero _ h)
  · exact isBoundedBilinearMap_apply.symm.continuous

end MeasureTheory
