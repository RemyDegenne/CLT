/-
Copyright (c) 2024 Thomas Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Zhu, Rémy Degenne
-/
import Clt.CharFun

/-!
Properties of real Gaussian distributions
-/

open MeasureTheory ProbabilityTheory Complex NormedSpace
open scoped ENNReal NNReal Real Topology

section Aux

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

lemma noAtoms_gaussianReal (h : v ≠ 0) : NoAtoms (gaussianReal μ v) := by
  sorry

end ProbabilityTheory
