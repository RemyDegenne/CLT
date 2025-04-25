/-
Copyright (c) 2024 Thomas Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Zhu, Rémy Degenne
-/
import Mathlib.Probability.Distributions.Gaussian
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Clt.CharFunCLM
import Clt.MomentGenerating

/-!
Properties of Gaussian distributions and its characteristic function.
-/

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

@[simp]
lemma variance_dirac {E : Type*} {mE : MeasurableSpace E} [MeasurableSingletonClass E]
    (X : E → ℝ) (x : E) :
    Var[X ; Measure.dirac x] = 0 := by
  rw [variance_eq_integral]
  · simp
  · exact aemeasurable_dirac

lemma variance_id_map {E : Type*} {mE : MeasurableSpace E} {μ : Measure E}
    {f : E → ℝ} (hf : AEMeasurable f μ) :
    Var[id ; μ.map f] = Var[f ; μ] := by
  rw [variance_eq_integral measurable_id.aemeasurable, integral_map hf]
  swap; · exact Measurable.aestronglyMeasurable <| by fun_prop
  simp only [id_eq]
  rw [variance_eq_integral hf]
  congr with x
  congr
  rw [integral_map hf]
  exact Measurable.aestronglyMeasurable <| by fun_prop

end Aux

namespace ProbabilityTheory

section GaussianReal

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

theorem mgf_id_gaussianReal {μ : ℝ} {v : ℝ≥0} :
    mgf (fun x ↦ x) (gaussianReal μ v) = fun t ↦ rexp (μ * t + v * t ^ 2 / 2) := by
  ext t
  suffices (mgf id (gaussianReal μ v) t : ℂ) = rexp (μ * t + ↑v * t ^ 2 / 2) from mod_cast this
  rw [← complexMGF_ofReal, complexMGF_id_gaussianReal, mul_comm μ]
  norm_cast

lemma integrable_exp_mul_gaussianReal (t : ℝ) :
    Integrable (fun x ↦ rexp (t * x)) (gaussianReal μ v) := by
  rw [← mgf_pos_iff, mgf_gaussianReal (μ := μ) (v := v) (by simp)]
  exact Real.exp_pos _

@[simp]
lemma integrableExpSet_id_gaussianReal : integrableExpSet id (gaussianReal μ v) = Set.univ := by
  ext
  simpa [integrableExpSet] using integrable_exp_mul_gaussianReal _ _ _

@[simp]
lemma integrableExpSet_id_gaussianReal' :
    integrableExpSet (fun x ↦ x) (gaussianReal μ v) = Set.univ :=
  integrableExpSet_id_gaussianReal _ _

@[simp]
lemma integral_id_gaussianReal :
    ∫ x, x ∂gaussianReal μ v = μ := by
  rw [← deriv_mgf_zero, mgf_id_gaussianReal]
  · rw [_root_.deriv_exp (by fun_prop)]
    simp only [mul_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div,
      add_zero, Real.exp_zero, one_mul]
    rw [deriv_add (by fun_prop) (by fun_prop)]
    simp only [deriv_div_const, differentiableAt_const, differentiableAt_id', DifferentiableAt.pow,
      deriv_mul, deriv_const', ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
      deriv_pow'', Nat.cast_ofNat, Nat.add_one_sub_one, pow_one, deriv_id'', mul_one, add_zero,
      zero_div]
    change deriv (fun x ↦ μ * x) 0 = μ
    rw [deriv_mul (by fun_prop) (by fun_prop)]
    simp
  · simp

@[simp]
lemma variance_id_gaussianReal : Var[fun x ↦ x ; gaussianReal μ v] = v := by
  rw [variance_eq_integral measurable_id'.aemeasurable]
  simp only [integral_id_gaussianReal]
  calc ∫ ω, (ω - μ) ^ 2 ∂gaussianReal μ v
  _ = ∫ ω, ω ^ 2 ∂(gaussianReal μ v).map (fun x ↦ x + -μ) := by
    rw [integral_map]
    · simp [sub_eq_add_neg]
    · fun_prop
    · refine Measurable.aestronglyMeasurable <| by fun_prop
  _ = ∫ ω, ω ^ 2 ∂(gaussianReal 0 v) := by simp [gaussianReal_map_add_const]
  _ = iteratedDeriv 2 (mgf (fun x ↦ x) (gaussianReal 0 v)) 0 := by
    rw [iteratedDeriv_mgf_zero] <;> simp
  _ = v := by
    simp_rw [mgf_id_gaussianReal, zero_mul, zero_add]
    rw [iteratedDeriv_succ, iteratedDeriv_one]
    have : deriv (fun t ↦ rexp (v * t ^ 2 / 2)) = fun t ↦ v * t * rexp (v * t ^ 2 / 2) := by
      ext t
      rw [_root_.deriv_exp (by fun_prop)]
      simp only [deriv_div_const, differentiableAt_const, differentiableAt_id',
        DifferentiableAt.pow, deriv_mul, deriv_const', zero_mul, deriv_pow'', Nat.cast_ofNat,
        Nat.add_one_sub_one, pow_one, deriv_id'', mul_one, zero_add]
      ring
    rw [this, deriv_mul (by fun_prop) (by fun_prop)]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, zero_div,
      Real.exp_zero, mul_one, zero_mul, add_zero]
    change deriv (fun x : ℝ ↦ v * x) 0 = v
    rw [deriv_mul (by fun_prop) (by fun_prop)]
    simp

@[simp]
lemma variance_id_gaussianReal' : Var[id ; gaussianReal μ v] = v :=
  variance_id_gaussianReal _ _

lemma memLp_id_gaussianReal (p : ℝ≥0) : MemLp id p (gaussianReal μ v) :=
  memLp_of_mem_interior_integrableExpSet (by simp) p

lemma integrable_pow_gaussianReal {n : ℕ} :
    Integrable (fun x ↦ |x| ^ n) (gaussianReal μ v) := by
  have h := (memLp_id_gaussianReal μ v n).integrable_norm_pow
  simp only [ne_eq, id_eq, Real.norm_eq_abs] at h
  by_cases hn : n = 0
  · simp [hn]
  · exact h hn

lemma gaussianReal_map_linearMap (L : ℝ →ₗ[ℝ] ℝ) :
    (gaussianReal μ v).map L = gaussianReal (L μ) ((L 1 ^ 2).toNNReal * v) := by
  have : (L : ℝ → ℝ) = fun x ↦ L 1 * x := by
    ext x
    have : x = x • 1 := by simp
    conv_lhs => rw [this, L.map_smul, smul_eq_mul, mul_comm]
  rw [this, gaussianReal_map_const_mul]
  congr
  simp only [mul_one, left_eq_sup]
  positivity

lemma gaussianReal_map_continuousLinearMap (L : ℝ →L[ℝ] ℝ) :
    (gaussianReal μ v).map L = gaussianReal (L μ) ((L 1 ^ 2).toNNReal * v) :=
  gaussianReal_map_linearMap _ _ L

@[simp]
lemma integral_linearMap_gaussianReal (L : ℝ →ₗ[ℝ] ℝ) :
    ∫ x, L x ∂(gaussianReal μ v) = L μ := by
  have : ∫ x, L x ∂(gaussianReal μ v) = ∫ x, x ∂((gaussianReal μ v).map L) := by
    rw [integral_map (φ := L) (by fun_prop)]
    exact measurable_id.aestronglyMeasurable
  simp [this, gaussianReal_map_linearMap]

@[simp]
lemma integral_continuousLinearMap_gaussianReal (L : ℝ →L[ℝ] ℝ) :
    ∫ x, L x ∂(gaussianReal μ v) = L μ := integral_linearMap_gaussianReal _ _ L

@[simp]
lemma variance_linearMap_gaussianReal (L : ℝ →ₗ[ℝ] ℝ) :
    Var[L ; gaussianReal μ v] = (L 1 ^ 2).toNNReal * v := by
  rw [← variance_id_map, gaussianReal_map_linearMap, variance_id_gaussianReal']
  · simp only [NNReal.coe_mul, Real.coe_toNNReal']
  · fun_prop

@[simp]
lemma variance_continuousLinearMap_gaussianReal (L : ℝ →L[ℝ] ℝ) :
    Var[L ; gaussianReal μ v] = (L 1 ^ 2).toNNReal * v :=
  variance_linearMap_gaussianReal _ _ L

end GaussianReal

/-- A measure is Gaussian if its map by every continuous linear form is a real Gaussian measure. -/
class IsGaussian {E : Type*} [TopologicalSpace E] [AddCommMonoid E] [Module ℝ E]
  {mE : MeasurableSpace E} (μ : Measure E) : Prop where
  map_eq_gaussianReal (L : E →L[ℝ] ℝ) : μ.map L = gaussianReal (μ[L]) (Var[L ; μ]).toNNReal

instance isGaussian_gaussianReal (m : ℝ) (v : ℝ≥0) : IsGaussian (gaussianReal m v) where
  map_eq_gaussianReal L := by
    rw [gaussianReal_map_continuousLinearMap]
    simp only [integral_continuousLinearMap_gaussianReal, variance_continuousLinearMap_gaussianReal,
      Real.coe_toNNReal']
    congr
    rw [Real.toNNReal_mul (by positivity), Real.toNNReal_coe]
    congr
    simp only [left_eq_sup]
    positivity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {mE : MeasurableSpace E} [BorelSpace E]

instance {x : E} : IsGaussian (Measure.dirac x) where
  map_eq_gaussianReal L := by rw [Measure.map_dirac (by fun_prop)]; simp

/-- A Gaussian measure is a probability measure. -/
instance {μ : Measure E} [IsGaussian μ] : IsProbabilityMeasure μ where
  measure_univ := by
    let L : E →L[ℝ] ℝ := Nonempty.some inferInstance
    have : μ.map L Set.univ = 1 := by simp [IsGaussian.map_eq_gaussianReal L]
    simpa [Measure.map_apply (by fun_prop : Measurable L) .univ] using this

lemma IsGaussian.memLp_continuousLinearMap (μ : Measure E) [IsGaussian μ] (L : E →L[ℝ] ℝ)
    (p : ℝ≥0∞) (hp : p ≠ ∞) :
    MemLp L p μ := by
  suffices MemLp (id ∘ L) p μ from this
  rw [← memLp_map_measure_iff, IsGaussian.map_eq_gaussianReal L]
  · convert memLp_id_gaussianReal _ _ p.toNNReal
    simp [hp]
  · exact Measurable.aestronglyMeasurable <| by fun_prop
  · fun_prop

lemma isGaussian_map_prod_add [SecondCountableTopology E]
    {μ ν : Measure E} [IsGaussian μ] [IsGaussian ν] :
    IsGaussian ((μ.prod ν).map (fun p ↦ p.1 + p.2)) where
  map_eq_gaussianReal := by
    intro L
    have h1 : ((μ.prod ν).map (fun p ↦ p.1 + p.2)).map L
        = ((μ.map L).prod (ν.map L)).map (fun p ↦ p.1 + p.2) := by
      rw [Measure.map_map (by fun_prop) (by fun_prop)]
      have : (L ∘ fun (p : E × E) ↦ p.1 + p.2)
          = (fun p : ℝ × ℝ ↦ p.1 + p.2) ∘ (Prod.map L L) := by ext; simp
      rw [this, ← Measure.map_map (by fun_prop) (by fun_prop),
        ← Measure.map_prod_map]
      · fun_prop
      · fun_prop
    have : ∫ x, L x ∂((μ.prod ν).map (fun p ↦ p.1 + p.2))
          = ∫ x, x ∂(((μ.map L).prod (ν.map L)).map (fun p ↦ p.1 + p.2)) := by
        rw [← h1, integral_map (φ := L)]
        · fun_prop
        · exact measurable_id.aestronglyMeasurable
    rw [h1, this, ← variance_id_map (by fun_prop), h1, IsGaussian.map_eq_gaussianReal L,
      IsGaussian.map_eq_gaussianReal L, gaussianReal_map_prod_add]
    congr
    · simp
    · simp [variance_nonneg]

lemma isGaussian_conv [SecondCountableTopology E] {μ ν : Measure E} [IsGaussian μ] [IsGaussian ν] :
    IsGaussian (μ ∗ ν) := isGaussian_map_prod_add

section Centered

def IsCentered (μ : Measure E) [IsGaussian μ] : Prop := ∀ L : E →L[ℝ] ℝ, ∫ x, L x ∂μ = 0

lemma isCentered_dirac_zero : IsCentered (Measure.dirac (0 : E)) := by intro L; simp

end Centered

section IsDegenerate

def IsDegenerate (μ : Measure E) [IsGaussian μ] : Prop :=
  ∃ L : E →L[ℝ] ℝ, L ≠ 0 ∧ Var[L ; μ] = 0

lemma isDegenerate_dirac (x : E) : IsDegenerate (Measure.dirac x) := by
  obtain ⟨L, hL⟩ : ∃ L : E →L[ℝ] ℝ, L ≠ 0 := by
    sorry
  exact ⟨L, hL, by simp⟩

end IsDegenerate

section CharFunCLM

lemma IsGaussian.charFunCLM_eq {μ : Measure E} [IsGaussian μ] (L : E →L[ℝ] ℝ) :
    charFunCLM μ L = cexp (μ[L] * I - Var[L ; μ] / 2) := by
  calc charFunCLM μ L
  _ = charFun (μ.map L) 1 := by rw [charFunCLM_eq_charFun_map_one]
  _ = charFun (gaussianReal (μ[L]) (Var[L ; μ]).toNNReal) 1 := by
    rw [IsGaussian.map_eq_gaussianReal L]
  _ = cexp (μ[L] * I - Var[L ; μ] / 2) := by
    rw [charFun_gaussianReal]
    simp only [ofReal_one, one_mul, Real.coe_toNNReal', one_pow, mul_one]
    congr
    · rw [integral_complex_ofReal]
    · simp only [sup_eq_left]
      exact variance_nonneg _ _

theorem isGaussian_iff_charFunCLM_eq {μ : Measure E} [IsFiniteMeasure μ] :
    IsGaussian μ ↔ ∀ L : E →L[ℝ] ℝ, charFunCLM μ L = cexp (μ[L] * I - Var[L ; μ] / 2) := by
  refine ⟨fun h ↦ h.charFunCLM_eq, fun h ↦ ⟨fun L ↦ ?_⟩⟩
  refine Measure.ext_of_charFun ?_
  ext u
  rw [charFun_map_eq_charFunCLM_smul L u, h (u • L), charFun_gaussianReal]
  simp only [ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul, ofReal_mul,
    Real.coe_toNNReal']
  congr
  · rw [integral_mul_left, integral_complex_ofReal]
  · rw [max_eq_left (variance_nonneg _ _), mul_comm, ← ofReal_pow, ← ofReal_mul, ← variance_mul]
    congr

alias ⟨_, isGaussian_of_charFunCLM_eq⟩ := isGaussian_iff_charFunCLM_eq

end CharFunCLM

section Rotation

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {mF : MeasurableSpace F} [BorelSpace F]

instance [SecondCountableTopology E] {μ : Measure E} [IsGaussian μ] {ν : Measure F} [IsGaussian ν] :
    IsGaussian (μ.prod ν) := by
  refine isGaussian_of_charFunCLM_eq fun L ↦ ?_
  rw [charFunCLM_prod]
  sorry

-- TODO: invariance by rotation, using charFunCLM

end Rotation

section ToLpₗ

variable {p : ℝ≥0∞}

/-- `MemLp.toLp` as a `LinearMap` from the continuous linear maps. -/
def ContinuousLinearMap.toLpₗ (μ : Measure E) [IsGaussian μ] (p : ℝ≥0∞) (hp : p ≠ ∞) :
    (E →L[ℝ] ℝ) →ₗ[ℝ] Lp ℝ p μ where
  toFun := fun L ↦ MemLp.toLp L (IsGaussian.memLp_continuousLinearMap μ L p hp)
  map_add' u v := by push_cast; rw [MemLp.toLp_add]
  map_smul' c L := by push_cast; rw [MemLp.toLp_const_smul]; rfl

@[simp]
lemma ContinuousLinearMap.toLpₗ_apply {μ : Measure E} [IsGaussian μ] (L : E →L[ℝ] ℝ)
    (hp : p ≠ ∞) :
    L.toLpₗ μ p hp = MemLp.toLp L (IsGaussian.memLp_continuousLinearMap μ L p hp) := rfl

end ToLpₗ

section Fernique

/-- **Fernique's theorem** -/
theorem IsGaussian.exists_integrable_exp_sq (μ : Measure E) [IsGaussian μ] :
    ∃ C, 0 < C ∧ Integrable (fun x ↦ rexp (C * ‖x‖ ^ 2)) μ := by
  sorry

lemma IsGaussian.memLp_id [SecondCountableTopology E]
    (μ : Measure E) [IsGaussian μ] (p : ℝ≥0∞) (hp : p ≠ ∞) :
    MemLp id p μ := by
  suffices MemLp (fun x ↦ ‖x‖ ^ 2) (p / 2) μ by
    rw [← memLp_norm_rpow_iff (q := 2) _ (by simp) (by simp)]
    · simpa using this
    · exact Measurable.aestronglyMeasurable <| by fun_prop
  lift p to ℝ≥0 using hp
  convert memLp_of_mem_interior_integrableExpSet ?_ (p / 2)
  · simp
  obtain ⟨C, hC_pos, hC⟩ := exists_integrable_exp_sq μ
  have hC_neg : Integrable (fun x ↦ rexp (-C * ‖x‖ ^ 2)) μ := by -- `-C` could be any negative
    refine integrable_of_le_of_le (g₁ := 0) (g₂ := 1) ?_ ?_ ?_
      (integrable_const _) (integrable_const _)
    · exact Measurable.aestronglyMeasurable <| by fun_prop
    · exact ae_of_all _ fun _ ↦ by positivity
    · refine ae_of_all _ fun x ↦ ?_
      simp only [neg_mul, Pi.one_apply, Real.exp_le_one_iff, Left.neg_nonpos_iff]
      positivity
  have h_subset : Set.Ioo (-C) C ⊆ interior (integrableExpSet (fun x ↦ ‖x‖ ^ 2) μ) := by
    rw [IsOpen.subset_interior_iff isOpen_Ioo]
    exact fun x hx ↦ integrable_exp_mul_of_le_of_le hC_neg hC hx.1.le hx.2.le
  exact h_subset ⟨by simp [hC_pos], hC_pos⟩

end Fernique

section ToLp

variable {p : ℝ≥0∞} [SecondCountableTopology E]

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

lemma IsGaussian.integral_continuousLinearMap [SecondCountableTopology E] [CompleteSpace E]
    {μ : Measure E} [IsGaussian μ] (L : E →L[ℝ] ℝ) :
    μ[L] = L (∫ x, x ∂μ) := by
  have h_Lp := IsGaussian.memLp_id μ 1 (by simp)
  have h := L.integral_comp_L1_comm (h_Lp.toLp id)
  refine (trans ?_ h).trans ?_
  · refine integral_congr_ae ?_
    filter_upwards [MemLp.coeFn_toLp h_Lp] with x hx
    rw [hx, id_eq]
  · congr 1
    refine integral_congr_ae ?_
    filter_upwards [MemLp.coeFn_toLp h_Lp] with x hx
    rw [hx, id_eq]

end Mean

section Covariance

variable [SecondCountableTopology E]

-- todo: this is the right def only for centered gaussian measures
/-- Covariance operator of a Gaussian measure. -/
noncomputable
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
