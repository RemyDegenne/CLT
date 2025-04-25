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

namespace BoundedContinuousFunction

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable
def probCharCLM (L : E →L[ℝ] ℝ) : E →ᵇ ℂ :=
  char continuous_probChar (L := isBoundedBilinearMap_apply.symm.toContinuousLinearMap.toLinearMap₂)
    isBoundedBilinearMap_apply.symm.continuous L

lemma probCharCLM_apply (L : E →L[ℝ] ℝ) (x : E) : probCharCLM L x = exp (L x * I) := rfl

@[simp]
lemma probCharCLM_zero : probCharCLM (0 : E →L[ℝ] ℝ) = 1 := by simp [probCharCLM]

end BoundedContinuousFunction

section CharFun

namespace MeasureTheory

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {mE : MeasurableSpace E}
  [NormedAddCommGroup F] [NormedSpace ℝ F] {mF : MeasurableSpace F}
  {μ : Measure E} {ν : Measure F}

noncomputable
def charFunCLM (μ : Measure E) (L : E →L[ℝ] ℝ) : ℂ :=
  ∫ v, BoundedContinuousFunction.probCharCLM L v ∂μ

lemma charFunCLM_apply (L : E →L[ℝ] ℝ) : charFunCLM μ L = ∫ v, exp (L v * I) ∂μ := rfl

lemma charFunCLM_prod [SFinite μ] [SFinite ν] (L : E × F →L[ℝ] ℝ) :
    charFunCLM (μ.prod ν) L
      = charFunCLM μ (L.comp (.inl ℝ E F)) * charFunCLM ν (L.comp (.inr ℝ E F)) := by
  let L₁ : E →L[ℝ] ℝ := L.comp (.inl ℝ E F)
  let L₂ : F →L[ℝ] ℝ := L.comp (.inr ℝ E F)
  simp_rw [charFunCLM_apply]
  have h_eq_add v : L v = L₁ v.1 + L₂ v.2 := by
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.inl_apply, ContinuousLinearMap.inr_apply, ← ContinuousLinearMap.map_add]
    simp
  simp_rw [h_eq_add, ofReal_add, add_mul, Complex.exp_add]
  rw [integral_prod_mul (f := fun x ↦ cexp ((L₁ x * I))) (g := fun x ↦ cexp ((L₂ x * I)))]

variable [CompleteSpace E] [BorelSpace E] [SecondCountableTopology E]

lemma ext_of_charFunCLM {μ ν : Measure E}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (h : charFunCLM μ = charFunCLM ν) :
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

end CharFun
