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

variable {E} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Peano's form of Taylor's theorem (c/f formulations in Mathlib.Analysis.Calculus.Taylor)
The general form should have some more general `hf` (using `ContDiff*`).
The resulting form might be different from this one below.
-/
theorem taylor_mean_remainder_peano {f : ℝ → E}
    {x₀ : ℝ} {n : ℕ} (hf : ContDiff ℝ n f) :
    (fun x ↦ f x - taylorWithinEval f n univ x₀ x) =o[𝓝 x₀] fun x ↦ (x - x₀) ^ n := by
  sorry

end Taylor

open MeasureTheory ProbabilityTheory Complex
open scoped Nat Real NNReal ENNReal Topology

section ForMathlib

theorem memℒp_iff_integrable_norm_rpow {α} [MeasurableSpace α] (μ : Measure α)
    {E} [NormedAddCommGroup E] {f : α → E} (hf : AEStronglyMeasurable f μ)
    (p : ℝ≥0∞) (p_zero : p ≠ 0) (p_top : p ≠ ∞) :
    Memℒp f p μ ↔ Integrable (fun x ↦ ‖f x‖ ^ p.toReal) μ := by
  rw [← memℒp_one_iff_integrable, ← memℒp_norm_rpow_iff hf p_zero p_top,
    ENNReal.div_self p_zero p_top]

lemma integrable_norm_rpow_antitone {α} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ]
    {E} [NormedAddCommGroup E] {f : α → E} (hf : AEStronglyMeasurable f μ)
    {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hpq : p ≤ q)
    (hint : Integrable (fun x ↦ ‖f x‖ ^ q) μ) :
    Integrable (fun x ↦ ‖f x‖ ^ p) μ := by
  rcases hp.eq_or_lt with (rfl | hp)
  · simp
  rcases hq.eq_or_lt with (rfl | hq)
  · exact (hp.not_le hpq).elim
  revert hint
  convert fun h ↦ Memℒp.mono_exponent h (ENNReal.ofReal_le_ofReal hpq) using 1
  · rw [memℒp_iff_integrable_norm_rpow μ hf, ENNReal.toReal_ofReal hq.le] <;> simp_all
  · rw [memℒp_iff_integrable_norm_rpow μ hf, ENNReal.toReal_ofReal hp.le] <;> simp_all
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

theorem iteratedDerivWithin_eq_iteratedDeriv
    {𝕜 : Type u} [NontriviallyNormedField 𝕜]
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {s : Set 𝕜} {f : 𝕜 → E} {x : 𝕜} {n : ℕ}
    (hs : UniqueDiffOn 𝕜 s) (h : ContDiffAt 𝕜 (↑n) f x) (hx : x ∈ s) :
    iteratedDerivWithin n f s x = iteratedDeriv n f x := by
  unfold iteratedDerivWithin iteratedDeriv
  rw [iteratedFDerivWithin_eq_iteratedFDeriv hs h hx]

end ForMathlib

variable {μ : Measure ℝ} [IsProbabilityMeasure μ]

/-!
The `n`th derivative of `charFun μ`.
The proof uses results on iterated derivatives of the Fourier transform.
-/

theorem contDiff_charFun {n : ℕ} (hint : Integrable (|·| ^ n) μ) :
    ContDiff ℝ n (charFun μ) := by
  have h : sesqFormOfInner = (ContinuousLinearMap.mul ℝ ℝ).toLinearMap₂ := by ext; rfl
  have hint' (k : ℕ) (hk : k ≤ (n : ℕ∞)) : Integrable (fun x ↦ ‖x‖ ^ k * ‖(1 : ℝ → ℂ) x‖) μ := by
    simp only [Pi.one_apply, norm_one, mul_one]
    rw [Nat.cast_le] at hk
    exact integrable_norm_pow_antitone μ aestronglyMeasurable_id hk hint
  simp_rw [funext (charFun_eq_fourierIntegral' μ)]
  rw [h]
  apply (VectorFourier.contDiff_fourierIntegral _ hint').comp
  apply contDiff_const_smul

open VectorFourier in
theorem iteratedDeriv_charFun {n : ℕ} {t : ℝ} (hint : Integrable (|·| ^ n) μ) :
    iteratedDeriv n (charFun μ) t = I ^ n * ∫ x, x ^ n * exp (t * x * I) ∂μ := by
  have h : sesqFormOfInner = (ContinuousLinearMap.mul ℝ ℝ).toLinearMap₂ := by ext; rfl
  have hint' (k : ℕ) (hk : k ≤ (n : ℕ∞)) : Integrable (fun x ↦ ‖x‖ ^ k * ‖(1 : ℝ → ℂ) x‖) μ := by
    simp only [Pi.one_apply, norm_one, mul_one]
    rw [Nat.cast_le] at hk
    exact integrable_norm_pow_antitone μ aestronglyMeasurable_id hk hint
  simp_rw [funext (charFun_eq_fourierIntegral' μ), smul_eq_mul]
  sorry
  -- todo: fix the proof below
  -- rw [iteratedDeriv_const_smul]
  -- · dsimp only
  --   rw [h, iteratedDeriv, iteratedFDeriv_fourierIntegral _ hint']
  --   · rw [fourierIntegral_continuousMultilinearMap_apply]
  --     · unfold fourierIntegral Real.fourierChar Circle.exp
  --       simp only [ContinuousMap.coe_mk, ofReal_mul, ofReal_ofNat, neg_mul,
  --         ContinuousLinearMap.toLinearMap₂_apply, ContinuousLinearMap.mul_apply', mul_neg, neg_neg,
  --         AddChar.coe_mk, ofReal_inv, fourierPowSMulRight_apply, mul_one, Finset.prod_const,
  --         Finset.card_univ, Fintype.card_fin, Pi.one_apply, real_smul, ofReal_pow, smul_eq_mul,
  --         Circle.smul_def, ofReal_neg]
  --       simp_rw [mul_left_comm (exp _), integral_mul_left]
  --       have : (2 : ℂ) * π ≠ 0 := by simp [Real.pi_ne_zero]
  --       field_simp
  --       ring_nf
  --       rw [mul_assoc]
  --       congr
  --       · ext; congr 2; ring
  --       · rw [← mul_pow]; norm_num
  --     · exact Real.continuous_fourierChar
  --     · apply integrable_fourierPowSMulRight
  --       · simpa
  --       · exact aestronglyMeasurable_one
  --   · exact aestronglyMeasurable_one
  --   · rfl
  -- · rw [h]
  --   apply contDiff_fourierIntegral _ hint'

theorem iteratedDeriv_charFun_zero {n : ℕ} (hint : Integrable (|·| ^ n) μ) :
    iteratedDeriv n (charFun μ) 0 = I ^ n * ∫ x, x ^ n ∂μ := by
  simp [iteratedDeriv_charFun hint]
  norm_cast
  -- maybe this should have been done by norm_cast?
  exact integral_ofReal

theorem taylor_charFun {n : ℕ} (hint : Integrable (|·| ^ n) μ) :
    (fun t ↦ charFun μ t - ∑ k ∈ Finset.range (n + 1), (k ! : ℝ)⁻¹ * (t * I) ^ k * ∫ x, x ^ k ∂μ) =o[𝓝 0] fun t ↦ t ^ n := by
  have := taylor_mean_remainder_peano (x₀ := 0) (contDiff_charFun hint)
  simp_rw [sub_zero] at this
  convert this with t
  simp_rw [taylor_within_apply, sub_zero, RCLike.real_smul_eq_coe_mul]
  apply Finset.sum_congr rfl
  intro k hkn
  push_cast
  have hint' : Integrable (fun x ↦ |x| ^ k) μ :=
    integrable_norm_pow_antitone μ aestronglyMeasurable_id
      (Finset.mem_range_succ_iff.mp hkn) hint
  rw [iteratedDerivWithin, iteratedFDerivWithin_eq_iteratedFDeriv, ← iteratedDeriv, iteratedDeriv_charFun_zero]
  · simp [mul_pow, mul_comm, mul_assoc, mul_left_comm]
  · exact hint'
  · exact uniqueDiffOn_univ
  · exact (contDiff_charFun hint').contDiffAt
  · trivial
