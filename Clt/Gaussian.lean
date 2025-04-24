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

section Aux

lemma rpow_toReal_eLpNorm {E F : Type*} {mE : MeasurableSpace E} {μ : Measure E}
    [NormedAddCommGroup F] {f : E → F} {p : ℝ}
    (hf : MemLp f (ENNReal.ofReal p) μ) (hp : 0 < p) :
    (eLpNorm f (ENNReal.ofReal p) μ).toReal ^ p = ∫ x, ‖f x‖ ^ p ∂μ := by
  rw [eLpNorm_eq_lintegral_rpow_enorm (by simp [hp]) (by simp)]
  simp only [one_div]
  have : (ENNReal.ofReal p).toReal = p := ENNReal.toReal_ofReal (by positivity)
  simp_rw [this]
  rw [ENNReal.toReal_rpow, ← ENNReal.rpow_mul, inv_mul_cancel₀ hp.ne', ENNReal.rpow_one]
  simp_rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp.le]
  rw [← ofReal_integral_eq_lintegral_ofReal, ENNReal.toReal_ofReal (by positivity)]
  · convert MemLp.integrable_norm_rpow hf (by simp [hp]) (by simp)
    exact this.symm
  · exact ae_of_all _ fun x ↦ by positivity

lemma pow_toReal_eLpNorm {E F : Type*} {mE : MeasurableSpace E} {μ : Measure E}
    [NormedAddCommGroup F] {f : E → F} {n : ℕ}
    (hf : MemLp f n μ) (hn : n ≠ 0) :
    (eLpNorm f n μ).toReal ^ n = ∫ x, ‖f x‖ ^ n ∂μ := by
  have h_Lp : MemLp f (ENNReal.ofReal n) μ := by convert hf; simp
  have h := rpow_toReal_eLpNorm h_Lp (by positivity)
  simpa using h

end Aux

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

instance {x : E} : IsGaussian (Measure.dirac x) where
  map_eq_gaussianReal L := by
    refine ⟨L x, 0, ?_⟩
    simp only [gaussianReal_zero_var]
    rw [Measure.map_dirac (by fun_prop)]

instance {μ : Measure E} [IsGaussian μ] : IsProbabilityMeasure μ where
  measure_univ := by
    let L : E →L[ℝ] ℝ := Nonempty.some inferInstance
    have : μ.map L Set.univ = 1 := by simp [μ.map_eq_gaussianReal L]
    simpa [Measure.map_apply (by fun_prop : Measurable L) .univ] using this

@[simp]
lemma meanMap_dirac (L : E →L[ℝ] ℝ) (x : E) :
    (Measure.dirac x).meanMap L = L x := by
  have h := Measure.map_eq_gaussianReal (Measure.dirac 0) L
  rw [Measure.map_dirac (by fun_prop), ← gaussianReal_zero_var] at h
  sorry

@[simp]
lemma varMap_dirac (L : E →L[ℝ] ℝ) (x : E) :
    (Measure.dirac x).varMap L = 0 := by
  have h := Measure.map_eq_gaussianReal (Measure.dirac 0) L
  rw [Measure.map_dirac (by fun_prop), ← gaussianReal_zero_var] at h
  sorry

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
lemma IsGaussian.memLp_continuousLinearMap (μ : Measure E) [IsGaussian μ] (L : E →L[ℝ] ℝ)
    (p : ℝ≥0∞) (hp : p ≠ ∞) :
    MemLp L p μ := by
  suffices MemLp (id ∘ L) p μ from this
  rw [← memLp_map_measure_iff, μ.map_eq_gaussianReal L]
  · convert memLp_id_gaussianReal _ _ p.toNNReal
    simp [hp]
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

def charFunCLM (μ : Measure E) (L : E →L[ℝ] ℝ) : ℂ := ∫ v, probCharCLM L v ∂μ

lemma ext_of_charFunCLM [CompleteSpace E] {μ ν : Measure E}
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

end CharFun

section Centered

def IsCentered (μ : Measure E) [IsGaussian μ] : Prop := ∀ L : E →L[ℝ] ℝ, μ.meanMap L = 0

lemma isCentered_dirac_zero : IsCentered (Measure.dirac (0 : E)) := by intro L; simp

end Centered

section IsDegenerate

def IsDegenerate (μ : Measure E) [IsGaussian μ] : Prop :=
  ∃ L : E →L[ℝ] ℝ, L ≠ 0 ∧ μ.varMap L = 0

lemma isDegenerate_dirac (x : E) : IsDegenerate (Measure.dirac x) := by
  obtain ⟨L, hL⟩ : ∃ L : E →L[ℝ] ℝ, L ≠ 0 := by
    sorry
  exact ⟨L, hL, by simp⟩

end IsDegenerate

section Rotation



end Rotation

section ToLpₗ

variable {p : ℝ≥0∞}

/-- `MemLp.toLp` as a `LinearMap` from the continuous linear maps. -/
def ContinuousLinearMap.toLpₗ (μ : Measure E) [IsGaussian μ] (p : ℝ≥0∞) (hp : p ≠ ∞) :
    (E →L[ℝ] ℝ) →ₗ[ℝ] Lp ℝ p μ where
  toFun := fun L ↦ MemLp.toLp L (IsGaussian.memLp_continuousLinearMap μ L p hp)
  map_add' u v := by push_cast; rw [MemLp.toLp_add]
  map_smul' c L := by push_cast; rw [MemLp.toLp_const_smul]; rfl

omit [SecondCountableTopology E] in
@[simp]
lemma ContinuousLinearMap.toLpₗ_apply {μ : Measure E} [IsGaussian μ] (L : E →L[ℝ] ℝ)
    (hp : p ≠ ∞) :
    L.toLpₗ μ p hp = MemLp.toLp L (IsGaussian.memLp_continuousLinearMap μ L p hp) := rfl

end ToLpₗ

section Fernique

theorem fernique (μ : Measure E) [IsGaussian μ] :
    ∃ C, 0 < C ∧ Integrable (fun x ↦ rexp (C * ‖x‖ ^ 2)) μ := by
  sorry

-- Corollary of Fernique's theorem
lemma IsGaussian.memLp_id (μ : Measure E) [IsGaussian μ] (p : ℝ≥0∞) (hp : p ≠ ∞) :
    MemLp id p μ := by
  sorry

end Fernique

section ToLp

variable {p : ℝ≥0∞}

lemma norm_toLpₗ_le (μ : Measure E) [IsGaussian μ] (L : E →L[ℝ] ℝ) (hp : p ≠ 0) (hp_top : p ≠ ∞) :
    ‖L.toLpₗ μ p hp_top‖ ≤ ‖L‖ * (eLpNorm id p μ).toReal := by
  have h0 : 0 < p.toReal := by simp [ENNReal.toReal_pos_iff, pos_iff_ne_zero, hp, hp_top.lt_top]
  suffices ‖L.toLpₗ μ p hp_top‖
      ≤ (‖L‖ₑ ^ p.toReal * ∫⁻ x, ‖x‖ₑ ^ p.toReal ∂μ).toReal ^ p.toReal⁻¹ by
    refine this.trans_eq ?_
    simp only [ENNReal.toReal_mul]
    rw [← ENNReal.toReal_rpow, Real.mul_rpow (by positivity) (by positivity),
      ← Real.rpow_mul (by positivity), mul_inv_cancel₀ h0.ne', Real.rpow_one, toReal_enorm]
    rw [eLpNorm_eq_lintegral_rpow_enorm (by simp [hp]) hp_top, ENNReal.toReal_rpow]
    simp
  rw [ContinuousLinearMap.toLpₗ_apply, Lp.norm_toLp,
    eLpNorm_eq_lintegral_rpow_enorm (by simp [hp]) hp_top]
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_ofNat, one_div]
  refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
  suffices ∫⁻ x, ‖L x‖ₑ ^ p.toReal ∂μ ≤ ‖L‖ₑ ^ p.toReal * ∫⁻ x, ‖x‖ₑ ^ p.toReal ∂μ by
    rw [← ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity)]
    gcongr
    rwa [ENNReal.ofReal_toReal]
    refine ENNReal.mul_ne_top (by simp) ?_
    have h := (IsGaussian.memLp_id μ p hp_top).eLpNorm_ne_top
    rw [eLpNorm_eq_lintegral_rpow_enorm (by simp [hp]) hp_top] at h
    simpa [h0] using h
  calc ∫⁻ x, ‖L x‖ₑ ^ p.toReal ∂μ
  _ ≤ ∫⁻ x, ‖L‖ₑ ^ p.toReal * ‖x‖ₑ ^ p.toReal ∂μ := by
    refine lintegral_mono fun x ↦ ?_
    rw [← ENNReal.mul_rpow_of_nonneg]
    swap; · positivity
    gcongr
    simp_rw [← ofReal_norm]
    rw [← ENNReal.ofReal_mul (by positivity)]
    gcongr
    exact L.le_opNorm x
  _ = ‖L‖ₑ ^ p.toReal * ∫⁻ x, ‖x‖ₑ ^ p.toReal ∂μ := by rw [lintegral_const_mul]; fun_prop

/-- `MemLp.toLp` as a `ContinuousLinearMap` from the continuous linear maps. -/
def ContinuousLinearMap.toLp (μ : Measure E) [IsGaussian μ] (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (hp : p ≠ ∞) :
    (E →L[ℝ] ℝ) →L[ℝ] Lp ℝ p μ where
  toLinearMap := ContinuousLinearMap.toLpₗ μ p hp
  cont := by
    refine LinearMap.continuous_of_locally_bounded _ fun s hs ↦ ?_
    rw [image_isVonNBounded_iff]
    simp_rw [isVonNBounded_iff'] at hs
    obtain ⟨r, hxr⟩ := hs
    refine ⟨r * (eLpNorm id p μ).toReal, fun L hLs ↦ ?_⟩
    specialize hxr L hLs
    have hp_ne : p ≠ 0 := by
      have : 1 ≤ p := Fact.out
      positivity
    refine (norm_toLpₗ_le μ L hp_ne hp).trans ?_
    gcongr

@[simp]
lemma ContinuousLinearMap.toLp_apply {μ : Measure E} [IsGaussian μ] (L : E →L[ℝ] ℝ)
    [Fact (1 ≤ p)] (hp : p ≠ ∞) :
    L.toLp μ p hp = MemLp.toLp L (IsGaussian.memLp_continuousLinearMap μ L p hp) := rfl

end ToLp

section Mean

def meanOperator (μ : Measure E) [IsGaussian μ] : (E →L[ℝ] ℝ) →L[ℝ] ℝ :=
  (L1.integralCLM (μ := μ)).comp (ContinuousLinearMap.toLp μ 1 (by simp))

lemma meanOperator_apply {μ : Measure E} [IsGaussian μ] (L : E →L[ℝ] ℝ) :
    meanOperator μ L = ∫ x, L x ∂μ := by
  simp only [meanOperator, ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearMap.toLp_apply]
  rw [← L1.integral_eq, L1.integral_eq_integral]
  exact integral_congr_ae (MemLp.coeFn_toLp _)

theorem exists_mean (μ : Measure E) [IsGaussian μ] :
    ∃ m : E, ∀ L : E →L[ℝ] ℝ, meanOperator μ L = L m := by
  sorry

end Mean

section Covariance

-- todo: this is the right def only for centered gaussian measures
/-- Covariance operator of a Gaussian measure. -/
def covarianceOperator (μ : Measure E) [IsGaussian μ] : (E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] ℝ :=
  ContinuousLinearMap.bilinearComp (continuousBilinFormOfInner (E := Lp ℝ 2 μ))
    (ContinuousLinearMap.toLp μ 2 (by simp)) (ContinuousLinearMap.toLp μ 2 (by simp))

lemma covarianceOperator_apply {μ : Measure E} [IsGaussian μ] (L₁ L₂ : E →L[ℝ] ℝ) :
    covarianceOperator μ L₁ L₂ = ∫ x, L₁ x * L₂ x ∂μ := by
  have : Fact (1 ≤ 2) := ⟨by simp⟩
  simp only [covarianceOperator, ContinuousLinearMap.bilinearComp_apply,
    ContinuousLinearMap.toLp_apply,
    continuousBilinFormOfInner_apply, L2.inner_def,
    RCLike.inner_apply, conj_trivial]
  refine integral_congr_ae ?_
  filter_upwards [MemLp.coeFn_toLp (IsGaussian.memLp_continuousLinearMap μ L₁ 2 (by simp)),
    MemLp.coeFn_toLp (IsGaussian.memLp_continuousLinearMap μ L₂ 2 (by simp))] with x hxL₁ hxL₂
  rw [hxL₁, hxL₂, mul_comm]

lemma norm_covarianceOperator_le {μ : Measure E} [IsGaussian μ] (L₁ L₂ : E →L[ℝ] ℝ) :
    ‖covarianceOperator μ L₁ L₂‖ ≤ ‖L₁‖ * ‖L₂‖ * ∫ x, ‖x‖ ^ 2 ∂μ := by
  calc ‖covarianceOperator μ L₁ L₂‖
  _ = ‖∫ x, L₁ x * L₂ x ∂μ‖ := by rw [covarianceOperator_apply]
  _ ≤ ∫ x, ‖L₁ x‖ * ‖L₂ x‖ ∂μ := (norm_integral_le_integral_norm _).trans (by simp)
  _ ≤ ∫ x, ‖L₁‖ * ‖x‖ * ‖L₂‖ * ‖x‖ ∂μ := by
    refine integral_mono_ae ?_ ?_ (ae_of_all _ fun x ↦ ?_)
    · simp_rw [← norm_mul]
      exact (MemLp.integrable_mul (IsGaussian.memLp_continuousLinearMap μ L₁ 2 (by simp))
        (IsGaussian.memLp_continuousLinearMap μ L₂ 2 (by simp))).norm
    · simp_rw [mul_assoc]
      refine Integrable.const_mul ?_ _
      simp_rw [← mul_assoc, mul_comm _ (‖L₂‖), mul_assoc, ← pow_two]
      refine Integrable.const_mul ?_ _
      exact (IsGaussian.memLp_id μ 2 (by simp)).integrable_norm_pow (by simp)
    · simp only
      rw [mul_assoc]
      gcongr
      · exact ContinuousLinearMap.le_opNorm L₁ x
      · exact ContinuousLinearMap.le_opNorm L₂ x
  _ = ‖L₁‖ * ‖L₂‖ * ∫ x, ‖x‖ ^ 2 ∂μ := by
    rw [← integral_mul_left]
    congr with x
    ring

lemma norm_covarianceOperator_le' {μ : Measure E} [IsGaussian μ] (L₁ L₂ : E →L[ℝ] ℝ) :
    ‖covarianceOperator μ L₁ L₂‖ ≤ ‖L₁‖ * ‖L₂‖ * (eLpNorm id 2 μ).toReal ^ 2 := by
  calc ‖covarianceOperator μ L₁ L₂‖
  _ ≤ ‖L₁‖ * ‖L₂‖ * ∫ x, ‖x‖ ^ 2 ∂μ := norm_covarianceOperator_le _ _
  _ = ‖L₁‖ * ‖L₂‖ * (eLpNorm id 2 μ).toReal ^ 2 := by
    congr
    have h := pow_toReal_eLpNorm (IsGaussian.memLp_id μ 2 (by simp)) (by simp)
    simpa only [ENNReal.ofReal_ofNat, Real.rpow_two, id_eq] using h.symm

end Covariance

end ProbabilityTheory
