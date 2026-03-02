/-
Copyright (c) 2024 Thomas Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Zhu, Rémy Degenne
-/
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Clt.CharFun

/-!
The characteristic function is moment generating.

Still depends on: Peano form of Taylor's theorem (TODO: is there code for X)
-/

section Taylor

open Set
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem taylor_isLittleO_univ {f : ℝ → E} {x₀ : ℝ} {n : ℕ} (hf : ContDiff ℝ n f) :
    (fun x ↦ f x - taylorWithinEval f n univ x₀ x) =o[𝓝 x₀] fun x ↦ (x - x₀) ^ n := by
  suffices (fun x ↦ f x - taylorWithinEval f n univ x₀ x) =o[𝓝[univ] x₀] fun x ↦ (x - x₀) ^ n by
    simpa
  refine taylor_isLittleO (s := univ) convex_univ (mem_univ _) ?_
  simpa [contDiffOn_univ] using hf

end Taylor

open MeasureTheory ProbabilityTheory Complex
open scoped Nat Real NNReal ENNReal Topology RealInnerProductSpace

section ForMathlib

lemma integrable_norm_rpow_antitone {α} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ]
    {E} [NormedAddCommGroup E] {f : α → E} (hf : AEStronglyMeasurable f μ)
    {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hpq : p ≤ q)
    (hint : Integrable (fun x ↦ ‖f x‖ ^ q) μ) :
    Integrable (fun x ↦ ‖f x‖ ^ p) μ := by
  rcases hp.eq_or_lt with (rfl | hp)
  · simp
  rcases hq.eq_or_lt with (rfl | hq)
  · exact (hp.not_ge hpq).elim
  revert hint
  convert fun h ↦ MemLp.mono_exponent h (ENNReal.ofReal_le_ofReal hpq) using 1
  · rw [← integrable_norm_rpow_iff hf, ENNReal.toReal_ofReal hq.le] <;> simp_all
  · rw [← integrable_norm_rpow_iff hf, ENNReal.toReal_ofReal hp.le] <;> simp_all
  · infer_instance

lemma integrable_norm_pow_antitone {α} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ]
    {E} [NormedAddCommGroup E] {f : α → E} (hf : AEStronglyMeasurable f μ)
    {p q : ℕ} (hpq : p ≤ q)
    (hint : Integrable (fun x ↦ ‖f x‖ ^ q) μ) :
    Integrable (fun x ↦ ‖f x‖ ^ p) μ := by
  revert hint
  replace hpq : (p : ℝ) ≤ q := by simpa
  convert integrable_norm_rpow_antitone μ hf
    p.cast_nonneg q.cast_nonneg hpq <;> rw [Real.rpow_natCast]

end ForMathlib

section InnerProductSpace

/-!
The `n`th derivative of `charFun μ`.
The proof uses results on iterated derivatives of the Fourier transform.
-/


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  {μ : Measure E} [IsProbabilityMeasure μ]

set_option backward.isDefEq.respectTransparency false
@[fun_prop]
theorem contDiff_charFun
    {n : ℕ} (hint : Integrable (‖·‖ ^ n) μ) :
    ContDiff ℝ n (charFun μ) := by
  have hint' (k : ℕ) (hk : k ≤ (n : ℕ∞)) : Integrable (fun x ↦ ‖x‖ ^ k * ‖(1 : E → ℂ) x‖) μ := by
    simp only [Pi.one_apply, norm_one, mul_one]
    rw [Nat.cast_le] at hk
    exact integrable_norm_pow_antitone μ aestronglyMeasurable_id hk hint
  simp_rw [funext charFun_eq_fourierIntegral']
  refine (VectorFourier.contDiff_fourierIntegral (L := innerSL ℝ) hint').comp ?_
  exact contDiff_const_smul _

@[fun_prop]
lemma continuous_charFun : Continuous (charFun μ) := by
  rw [← contDiff_zero (𝕜 := ℝ)]
  refine contDiff_charFun ?_
  suffices Integrable (fun _ ↦ (1 : ℝ)) μ by convert this
  fun_prop

end InnerProductSpace

variable {μ : Measure ℝ} [IsProbabilityMeasure μ]

set_option backward.isDefEq.respectTransparency false
open VectorFourier in
theorem iteratedDeriv_charFun {n : ℕ} {t : ℝ} (hint : Integrable (|·| ^ n) μ) :
    iteratedDeriv n (charFun μ) t = I ^ n * ∫ x, x ^ n * exp (t * x * I) ∂μ := by
  have h : innerₗ ℝ = (ContinuousLinearMap.mul ℝ ℝ).toLinearMap₁₂ := by ext; rfl
  have hint' (k : ℕ) (hk : k ≤ (n : ℕ∞)) : Integrable (fun x ↦ ‖x‖ ^ k * ‖(1 : ℝ → ℂ) x‖) μ := by
    simp only [Pi.one_apply, norm_one, mul_one]
    rw [Nat.cast_le] at hk
    exact integrable_norm_pow_antitone μ aestronglyMeasurable_id hk hint
  simp_rw [funext charFun_eq_fourierIntegral', smul_eq_mul]
  rw [iteratedDeriv_comp_const_smul]
  · dsimp only
    simp only [mul_inv_rev, neg_mul]
    rw [h, iteratedDeriv, iteratedFDeriv_fourierIntegral _ hint']
    · rw [fourierIntegral_continuousMultilinearMap_apply]
      · unfold fourierIntegral Real.fourierChar Circle.exp
        simp only [ContinuousMap.coe_mk, ofReal_mul, ofReal_ofNat,
          ContinuousLinearMap.toLinearMap₁₂_apply, ContinuousLinearMap.mul_apply', mul_neg, neg_neg,
          AddChar.coe_mk, ofReal_inv, fourierPowSMulRight_apply, mul_one, Finset.prod_const,
          Finset.card_univ, Fintype.card_fin, Pi.one_apply, real_smul, ofReal_pow, smul_eq_mul,
          Circle.smul_def, ofReal_neg]
        simp_rw [mul_left_comm (exp _), integral_const_mul]
        calc (-((↑π)⁻¹ * 2⁻¹)) ^ n
          * ((-(2 * ↑π * I)) ^ n * ∫ a, cexp (2 * ↑π * (↑a * ((↑π)⁻¹ * 2⁻¹ * ↑t)) * I) * ↑a ^ n ∂μ)
        _ = I ^ n * ∫ a, cexp (2 * ↑π * (↑a * ((↑π)⁻¹ * 2⁻¹ * ↑t)) * I) * ↑a ^ n ∂μ := by
          rw [← mul_assoc]
          congr
          rw [← mul_pow]
          ring_nf
          -- `⊢ ↑π ^ n * (↑π)⁻¹ ^ n * I ^ n = I ^ n`
          rw [inv_pow, mul_inv_cancel₀, one_mul]
          norm_cast
          positivity
        _ = I ^ n * ∫ x, ↑x ^ n * cexp (↑t * ↑x * I) ∂μ := by
          simp_rw [mul_comm ((_ : ℂ) ^ n)]
          congr with x
          congr 2
          ring_nf
          congr 2
          -- `⊢ ↑π * ↑x * (↑π)⁻¹ = ↑x`
          rw [mul_comm, ← mul_assoc, inv_mul_cancel₀, one_mul]
          norm_cast
          positivity
      · exact Real.continuous_fourierChar
      · apply integrable_fourierPowSMulRight
        · simpa
        · exact aestronglyMeasurable_one
    · exact aestronglyMeasurable_one
    · rfl
  · rw [h]
    exact contDiff_fourierIntegral _ hint'

theorem iteratedDeriv_charFun_zero {n : ℕ} (hint : Integrable (|·| ^ n) μ) :
    iteratedDeriv n (charFun μ) 0 = I ^ n * ∫ x, x ^ n ∂μ := by
  simp only [iteratedDeriv_charFun hint, ofReal_zero, zero_mul, exp_zero, mul_one,
    mul_eq_mul_left_iff, pow_eq_zero_iff', I_ne_zero, ne_eq, false_and, or_false]
  norm_cast
  -- maybe this should have been done by norm_cast?
  exact integral_ofReal

lemma taylorWithinEval_charFun_zero {n : ℕ} (hint : Integrable (|·| ^ n) μ) (t : ℝ):
    taylorWithinEval (charFun μ) n Set.univ 0 t
      = ∑ k ∈ Finset.range (n + 1), (k ! : ℂ)⁻¹ * (t * I) ^ k * ∫ x, x ^ k ∂μ := by
  simp_rw [taylor_within_apply, sub_zero, RCLike.real_smul_eq_coe_mul]
  refine Finset.sum_congr rfl fun k hkn ↦ ?_
  push_cast
  have hint' : Integrable (fun x ↦ |x| ^ k) μ :=
    integrable_norm_pow_antitone μ aestronglyMeasurable_id (Finset.mem_range_succ_iff.mp hkn) hint
  rw [iteratedDerivWithin,
    iteratedFDerivWithin_eq_iteratedFDeriv uniqueDiffOn_univ _ (Set.mem_univ _),
    ← iteratedDeriv, iteratedDeriv_charFun_zero hint']
  · simp [mul_pow, mul_comm, mul_assoc, mul_left_comm]
  · exact (contDiff_charFun hint').contDiffAt

theorem taylor_charFun {n : ℕ} (hint : Integrable (|·| ^ n) μ) :
    (fun t ↦ charFun μ t - ∑ k ∈ Finset.range (n + 1), (k ! : ℝ)⁻¹ * (t * I) ^ k * ∫ x, x ^ k ∂μ)
      =o[𝓝 0] fun t ↦ t ^ n := by
  have : (fun x ↦ charFun μ x - taylorWithinEval (charFun μ) n Set.univ 0 x)
      =o[𝓝 0] fun x ↦ x ^ n :=by
    convert taylor_isLittleO_univ (contDiff_charFun hint)
    simp_rw [sub_zero]
  convert this with t
  push_cast
  exact (taylorWithinEval_charFun_zero hint t).symm
