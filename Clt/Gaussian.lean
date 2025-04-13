/-
Copyright (c) 2024 Thomas Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Zhu, Rémy Degenne
-/
import Mathlib.Probability.Distributions.Gaussian
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Clt.CharFun
import Clt.MomentGenerating

/-!
Properties of Gaussian distributions and its characteristic function.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Complex
open scoped NNReal Real ENNReal

namespace ProbabilityTheory

variable (μ : ℝ) (v : ℝ≥0) {t : ℝ}

theorem charFun_gaussianReal : charFun (gaussianReal μ v) t = exp (t * μ * I - v * t ^ 2 / 2) := by
  simp_rw [charFun_apply_real]
  unfold gaussianReal
  split_ifs with hv
  · simp only [RCLike.inner_apply, conj_trivial, real_smul, ofReal_mul, integral_dirac, hv,
      NNReal.coe_zero, ofReal_zero, zero_mul, zero_div, sub_zero]
  calc
    _ = ∫ x, (gaussianPDFReal μ v x).toNNReal • cexp (t * x * I) ∂ℙ :=
      integral_withDensity_eq_integral_smul (measurable_gaussianPDFReal μ v).real_toNNReal _
    _ = ∫ x, gaussianPDFReal μ v x * cexp (t * x * I) ∂ℙ := by
      congr with x
      rw [mul_comm (t : ℂ)]
      simp [NNReal.smul_def, Real.coe_toNNReal _ (gaussianPDFReal_nonneg μ v x)]
    _ = (√(2 * π * v))⁻¹
        * ∫ x : ℝ, cexp (-(2 * v)⁻¹ * x ^ 2 + (t * I + μ / v) * x + -μ ^ 2 / (2 * v)) ∂ℙ := by
      unfold gaussianPDFReal
      simp_rw [ofReal_mul, mul_assoc _ _ (exp _), integral_mul_left, ofReal_exp, ← exp_add]
      congr; ext x; congr 1
      push_cast
      ring
    _ = (√(2 * π * v))⁻¹ * (π / - -(2 * v)⁻¹) ^ (1 / 2 : ℂ)
        * cexp (-μ ^ 2 / (2 * v) - (t * I + μ / v) ^ 2 / (4 * -(2 * v)⁻¹)) := by
      rw [integral_cexp_quadratic (by simpa using pos_iff_ne_zero.mpr hv), ← mul_assoc]
    _ = 1 * cexp (-μ ^ 2 / (2 * v) - (t * I + μ / v) ^ 2 / (4 * -(2 * v)⁻¹)) := by
      congr 1
      field_simp [Real.sqrt_eq_rpow]
      rw [ofReal_cpow (by positivity)]
      push_cast
      ring_nf
    _ = _ := by
      rw [one_mul]
      congr 1
      have : (v : ℂ) ≠ 0 := by simpa
      field_simp
      ring_nf
      simp

lemma gaussianReal_map_prod_add {m₁ m₂ : ℝ} {v₁ v₂ : ℝ≥0} :
    ((gaussianReal m₁ v₁).prod (gaussianReal m₂ v₂)).map (fun p ↦ p.1 + p.2)
      = gaussianReal (m₁ + m₂) (v₁ + v₂) := by
  sorry

section Def

variable {E : Type*} [TopologicalSpace E] [AddCommMonoid E] [Module ℝ E] {mE : MeasurableSpace E}

class IsGaussian (μ : Measure E) : Prop where
  map_eq_gaussianReal : ∀ L : E →L[ℝ] ℝ, ∃ m v, μ.map L = gaussianReal m v

def _root_.MeasureTheory.Measure.meanMap (μ : Measure E) [IsGaussian μ] (L : E →L[ℝ] ℝ) : ℝ :=
  (IsGaussian.map_eq_gaussianReal (μ := μ) L).choose

def _root_.MeasureTheory.Measure.varMap (μ : Measure E) [IsGaussian μ] (L : E →L[ℝ] ℝ) :
    ℝ≥0 :=
  (IsGaussian.map_eq_gaussianReal (μ := μ) L).choose_spec.choose

lemma _root_.MeasureTheory.Measure.map_eq_gaussianReal (μ : Measure E) [IsGaussian μ]
    (L : E →L[ℝ] ℝ) :
    μ.map L = gaussianReal (μ.meanMap L) (μ.varMap L) :=
  (IsGaussian.map_eq_gaussianReal L).choose_spec.choose_spec

end Def

instance isGaussian_gaussianReal (m : ℝ) (v : ℝ≥0) : IsGaussian (gaussianReal m v) where
  map_eq_gaussianReal L := by
    have : (L : ℝ → ℝ) = fun x ↦ L 1 * x := by
      ext x
      have : x = x • 1 := by simp
      conv_lhs => rw [this, L.map_smul, smul_eq_mul, mul_comm]
    rw [this]
    exact ⟨L 1 * m, ⟨(L 1) ^ 2, sq_nonneg _⟩ * v, gaussianReal_map_const_mul _⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {mE : MeasurableSpace E} [BorelSpace E] [SecondCountableTopology E]

instance {μ : Measure E} [IsGaussian μ] : IsProbabilityMeasure μ where
  measure_univ := by
    let L : E →L[ℝ] ℝ := Nonempty.some inferInstance
    have : μ.map L Set.univ = 1 := by simp [μ.map_eq_gaussianReal L]
    simpa [Measure.map_apply (by fun_prop : Measurable L) .univ] using this

lemma isGaussian_map_prod_add {μ ν : Measure E} [IsGaussian μ] [IsGaussian ν] :
    IsGaussian ((μ.prod ν).map (fun p ↦ p.1 + p.2)) where
  map_eq_gaussianReal := by
    intro L
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    have : (L ∘ fun (p : E × E) ↦ p.1 + p.2)
        = (fun p : ℝ × ℝ ↦ p.1 + p.2) ∘ (Prod.map L L) := by ext; simp
    rw [this, ← Measure.map_map (by fun_prop) (by fun_prop)]
    refine ⟨μ.meanMap L + ν.meanMap L, μ.varMap L + ν.varMap L, ?_⟩
    rw [← Measure.map_prod_map, μ.map_eq_gaussianReal L, ν.map_eq_gaussianReal L,
      gaussianReal_map_prod_add]
    · fun_prop
    · fun_prop

lemma IsGaussian.memLp_continuousLinearMap (μ : Measure E) [IsGaussian μ] (L : E →L[ℝ] ℝ) :
    MemLp L 2 μ := by
  refine ⟨by fun_prop, ?_⟩
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by simp) (by simp)]
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_ofNat]
  change ∫⁻ a, (fun x ↦ ‖x‖ₑ ^ 2) (L a) ∂μ < ⊤
  rw [← lintegral_map (μ := μ) (f := fun x ↦ ‖x‖ₑ ^ 2) (by fun_prop) (by fun_prop : Measurable L),
    μ.map_eq_gaussianReal L]
  simp only [← ofReal_norm_eq_enorm, Real.norm_eq_abs]
  sorry

def dualToL2 (μ : Measure E) [IsGaussian μ] : (E →L[ℝ] ℝ) →L[ℝ] Lp ℝ 2 μ where
  toFun := fun L ↦ MemLp.toLp L (IsGaussian.memLp_continuousLinearMap μ L)
  map_add' u v := by push_cast; rw [MemLp.toLp_add]
  map_smul' c L := by push_cast; rw [MemLp.toLp_const_smul]; rfl
  cont := by
    refine continuous_iff_continuous_dist.mpr ?_
    simp only [dist_eq_norm]
    suffices Continuous fun (p : (E →L[ℝ] ℝ) × (E →L[ℝ] ℝ)) ↦
        ENNReal.toReal (eLpNorm (p.1 - p.2) 2 μ) by
      sorry
    rw [continuous_iff_continuousAt]
    intro p
    refine (ENNReal.continuousAt_toReal ?_).comp ?_
    · sorry
    simp_rw [eLpNorm_eq_lintegral_rpow_enorm (by simp : (2 : ℝ≥0∞) ≠ 0) (by simp : 2 ≠ ∞)]
    simp only [ContinuousLinearMap.coe_sub', Pi.sub_apply, ENNReal.toReal_ofNat, ENNReal.rpow_ofNat,
      one_div]
    sorry

def continuousBilinFormOfInnerL2 (μ : Measure E) : (Lp ℝ 2 μ) →L[ℝ] (Lp ℝ 2 μ) →L[ℝ] ℝ :=
  continuousBilinFormOfInner (E := Lp ℝ 2 μ)

def covarianceOperator (μ : Measure E) [IsGaussian μ] : (E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] ℝ :=
  ContinuousLinearMap.bilinearComp (continuousBilinFormOfInnerL2 μ) (dualToL2 μ) (dualToL2 μ)

end ProbabilityTheory
