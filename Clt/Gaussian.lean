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

open MeasureTheory ProbabilityTheory Complex NormedSpace
open scoped ENNReal NNReal Real Topology

namespace ProbabilityTheory

variable (μ : ℝ) (v : ℝ≥0) {t : ℝ}

-- `∗` notation not used because of ambiguous notation : `conv` vs `mconv`
lemma gaussianReal_conv_gaussianReal {m₁ m₂ : ℝ} {v₁ v₂ : ℝ≥0} :
    Measure.conv (gaussianReal m₁ v₁) (gaussianReal m₂ v₂) = gaussianReal (m₁ + m₂) (v₁ + v₂) := by
  refine Measure.ext_of_charFun ?_
  ext t
  rw [charFun_conv]
  simp_rw [charFun_gaussianReal]
  rw [← Complex.exp_add]
  simp only [ofReal_add, NNReal.coe_add]
  congr
  ring

lemma gaussianReal_map_prod_add {m₁ m₂ : ℝ} {v₁ v₂ : ℝ≥0} :
    ((gaussianReal m₁ v₁).prod (gaussianReal m₂ v₂)).map (fun p ↦ p.1 + p.2)
      = gaussianReal (m₁ + m₂) (v₁ + v₂) :=
  gaussianReal_conv_gaussianReal

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

lemma isGaussian_conv {μ ν : Measure E} [IsGaussian μ] [IsGaussian ν] :
    IsGaussian (μ ∗ ν) := isGaussian_map_prod_add




lemma integrable_exp_mul_gaussianReal (t : ℝ) :
    Integrable (fun x ↦ rexp (t * x)) (gaussianReal μ v) := by
  rw [← mgf_pos_iff, mgf_gaussianReal (μ := μ) (v := v) (by simp)]
  exact Real.exp_pos _

@[simp]
lemma integrableExpSet_id_gaussianReal : integrableExpSet id (gaussianReal μ v) = Set.univ := by
  ext
  simpa [integrableExpSet] using integrable_exp_mul_gaussianReal _ _ _

lemma memLp_id_gaussianReal (p : ℝ≥0) : MemLp id p (gaussianReal μ v) :=
  memLp_of_mem_interior_integrableExpSet (by simp) p

lemma integrable_pow_gaussianReal {n : ℕ} :
    Integrable (fun x ↦ |x| ^ n) (gaussianReal μ v) := by
  have h := (memLp_id_gaussianReal μ v n).integrable_norm_pow
  simp only [ne_eq, id_eq, Real.norm_eq_abs] at h
  by_cases hn : n = 0
  · simp [hn]
  · exact h hn

omit [SecondCountableTopology E] in
lemma IsGaussian.memLp_continuousLinearMap (μ : Measure E) [IsGaussian μ] (L : E →L[ℝ] ℝ) :
    MemLp L 2 μ := by
  suffices MemLp (id ∘ L) 2 μ from this
  rw [← memLp_map_measure_iff, μ.map_eq_gaussianReal L]
  · exact memLp_id_gaussianReal _ _ _
  · exact Measurable.aestronglyMeasurable <| by fun_prop
  · fun_prop

section CharFun

open BoundedContinuousFunction Real

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

open BoundedContinuousFunction

def charFunCLM {μ : Measure E} (L : E →L[ℝ] ℝ) : ℂ := ∫ v, probCharCLM L v ∂μ

end CharFun

section Fernique

theorem fernique (μ : Measure E) [IsGaussian μ] :
    ∃ C, 0 < C ∧ Integrable (fun x ↦ rexp (C * ‖x‖ ^ 2)) μ := by
  sorry

-- Corollary of Fernique's theorem
lemma IsGaussian.memL2_id (μ : Measure E) [IsGaussian μ] : MemLp id 2 μ := by
  sorry

end Fernique

section Covariance

/-- `MemLp.toLp` as a `LinearMap` from the continuous linear maps. -/
def ContinuousLinearMap.toLpₗ (μ : Measure E) [IsGaussian μ] :
    (E →L[ℝ] ℝ) →ₗ[ℝ] Lp ℝ 2 μ where
  toFun := fun L ↦ MemLp.toLp L (IsGaussian.memLp_continuousLinearMap μ L)
  map_add' u v := by push_cast; rw [MemLp.toLp_add]
  map_smul' c L := by push_cast; rw [MemLp.toLp_const_smul]; rfl

omit [SecondCountableTopology E] in
@[simp]
lemma ContinuousLinearMap.toLpₗ_apply {μ : Measure E} [IsGaussian μ] (L : E →L[ℝ] ℝ) :
    L.toLpₗ μ = MemLp.toLp L (IsGaussian.memLp_continuousLinearMap μ L) := rfl

lemma norm_toLpₗ_le (μ : Measure E) [IsGaussian μ] (L : E →L[ℝ] ℝ) :
    ‖L.toLpₗ μ‖ ≤ ‖L‖ * (eLpNorm id 2 μ).toReal := by
  suffices ‖L.toLpₗ μ‖ ≤ (‖L‖ₑ ^ 2 * ∫⁻ x, ‖x‖ₑ ^ 2 ∂μ).toReal ^ (2 : ℝ)⁻¹ by
    refine this.trans_eq ?_
    simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, toReal_enorm]
    rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_natCast_mul (by positivity),
      ENNReal.toReal_rpow]
    simp [eLpNorm_eq_lintegral_rpow_enorm (by simp : (2 : ℝ≥0∞) ≠ 0) (by simp : 2 ≠ ∞)]
  rw [ContinuousLinearMap.toLpₗ_apply, Lp.norm_toLp,
    eLpNorm_eq_lintegral_rpow_enorm (by simp : (2 : ℝ≥0∞) ≠ 0) (by simp : 2 ≠ ∞)]
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_ofNat, one_div]
  refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
  suffices ∫⁻ x, ‖L x‖ₑ ^ 2 ∂μ ≤ ‖L‖ₑ ^ 2 * ∫⁻ x, ‖x‖ₑ ^ 2 ∂μ by
    rw [← ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity)]
    gcongr
    rwa [ENNReal.ofReal_toReal]
    refine ENNReal.mul_ne_top (by simp) ?_
    have h := (IsGaussian.memL2_id μ).eLpNorm_ne_top
    rw [eLpNorm_eq_lintegral_rpow_enorm (by simp : (2 : ℝ≥0∞) ≠ 0) (by simp : 2 ≠ ∞)] at h
    simpa using h
  calc ∫⁻ x, ‖L x‖ₑ ^ 2 ∂μ
  _ ≤ ∫⁻ x, ‖L‖ₑ ^ 2 * ‖x‖ₑ ^ 2 ∂μ := by
    refine lintegral_mono fun x ↦ ?_
    rw [← mul_pow]
    gcongr
    simp_rw [← ofReal_norm]
    rw [← ENNReal.ofReal_mul (by positivity)]
    gcongr
    exact L.le_opNorm x
  _ = ‖L‖ₑ ^ 2 * ∫⁻ x, ‖x‖ₑ ^ 2 ∂μ := by rw [lintegral_const_mul]; fun_prop

/-- `MemLp.toLp` as a `ContinuousLinearMap` from the continuous linear maps. -/
def ContinuousLinearMap.toLp (μ : Measure E) [IsGaussian μ] : (E →L[ℝ] ℝ) →L[ℝ] Lp ℝ 2 μ where
  toLinearMap := ContinuousLinearMap.toLpₗ μ
  cont := by
    refine LinearMap.continuous_of_locally_bounded _ fun s hs ↦ ?_
    rw [image_isVonNBounded_iff]
    simp_rw [isVonNBounded_iff'] at hs
    obtain ⟨r, hxr⟩ := hs
    refine ⟨r * (eLpNorm id 2 μ).toReal, fun L hLs ↦ ?_⟩
    specialize hxr L hLs
    refine (norm_toLpₗ_le μ L).trans ?_
    gcongr

@[simp]
lemma ContinuousLinearMap.toLp_apply {μ : Measure E} [IsGaussian μ] (L : E →L[ℝ] ℝ) :
    L.toLp μ = MemLp.toLp L (IsGaussian.memLp_continuousLinearMap μ L) := rfl

/-- Covariance operator of a Gaussian measure. -/
def covarianceOperator (μ : Measure E) [IsGaussian μ] : (E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] ℝ :=
  ContinuousLinearMap.bilinearComp (continuousBilinFormOfInner (E := Lp ℝ 2 μ))
    (ContinuousLinearMap.toLp μ) (ContinuousLinearMap.toLp μ)

lemma covarianceOperator_apply {μ : Measure E} [IsGaussian μ] (L₁ L₂ : E →L[ℝ] ℝ) :
    covarianceOperator μ L₁ L₂ = ∫ x, L₁ x * L₂ x ∂μ := by
  sorry

end Covariance

end ProbabilityTheory
