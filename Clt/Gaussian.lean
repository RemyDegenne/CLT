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
open scoped ENNReal NNReal Real

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

lemma memLp_id_gaussianReal (p : ℝ≥0) : MemLp id p (gaussianReal μ v) := by
  refine memLp_of_mem_interior_integrableExpSet ?_ _
  suffices integrableExpSet id (gaussianReal μ v) = Set.univ by simp [this]
  ext x
  simp only [integrableExpSet, id_eq, Set.mem_setOf_eq, Set.mem_univ, iff_true]
  exact integrable_exp_mul_gaussianReal _ _ _

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
