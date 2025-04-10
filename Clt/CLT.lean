/-
Copyright (c) 2024 Thomas Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Zhu, Rémy Degenne
-/
import Mathlib.Probability.IdentDistrib
import Clt.Gaussian
import Clt.Inversion
import Clt.MomentGenerating

/-!
The Central Limit Theorem
-/

noncomputable section

open MeasureTheory ProbabilityTheory Complex Filter
open scoped Real Topology

/-- `(1 + t/n + o(1/n)) ^ n → exp t` for `t ∈ ℂ`. -/
lemma tendsto_one_plus_div_cpow_cexp {f : ℕ → ℂ} (t : ℂ)
    (hf : (fun n ↦ f n - (1 + t / n)) =o[atTop] fun n ↦ 1 / (n : ℝ)) :
    Tendsto (fun n ↦ f n ^ n) atTop (𝓝 (exp t)) := by
  let g n := f n - 1
  have fg (n) : f n = 1 + g n := by ring
  simp_rw [fg, add_sub_add_left_eq_sub] at hf ⊢

  have hgO : g =O[atTop] fun n ↦ 1 / (n : ℝ) := by
    convert hf.isBigO.add (f₂ := fun n : ℕ ↦ t / n) _ using 1
    · simp
    apply Asymptotics.isBigO_of_le' (c := ‖t‖)
    field_simp
  have hg2 : ∀ᶠ n in atTop, ‖g n‖ ≤ 1 / 2 := by
    have hg := hgO.trans_tendsto tendsto_one_div_atTop_nhds_zero_nat
    rw [tendsto_zero_iff_norm_tendsto_zero] at hg
    apply hg.eventually_le_const
    norm_num
  have hf0 : ∀ᶠ n in atTop, 1 + g n ≠ 0 := by
    filter_upwards [hg2] with n hg2 hg0
    rw [← add_eq_zero_iff_neg_eq.mp hg0] at hg2
    norm_num at hg2

  suffices Tendsto (fun n ↦ n * log (1 + g n)) atTop (𝓝 t) by
    apply ((continuous_exp.tendsto _).comp this).congr'
    filter_upwards [hf0] with n h0
    dsimp
    rw [exp_nat_mul, exp_log h0]

  apply Tendsto.congr_dist (f₁ := fun n ↦ n * logTaylor 2 (g n))
  · apply Tendsto.congr' (f₁ := fun n ↦ n * g n - n * (t / n) + t)
    · filter_upwards [eventually_ne_atTop 0] with n h0
      rw [mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr h0)]
      simp [h0, logTaylor_succ, logTaylor_zero]
    · simpa [mul_sub] using hf.tendsto_inv_smul_nhds_zero.add_const t
  · apply Asymptotics.IsBigO.trans_tendsto _ tendsto_one_div_atTop_nhds_zero_nat
    simp_rw [dist_eq, ← mul_sub, norm_mul, norm_natCast]
    rw [Asymptotics.isBigO_mul_iff_isBigO_div
      ((eventually_ne_atTop 0).mono (fun n h0 ↦ Nat.cast_ne_zero.mpr h0))]
    trans fun n ↦ ‖g n‖ ^ 2
    · rw [Asymptotics.isBigO_iff]
      use 1
      filter_upwards [hg2] with n hg2
      have hg1 : ‖g n‖ < 1 := hg2.trans_lt (by norm_num)
      rw [norm_norm, norm_sub_rev]
      apply (norm_log_sub_logTaylor_le 1 hg1).trans
      norm_num only [Nat.reduceAdd, Nat.cast_one, norm_pow, norm_norm, one_mul]
      rw [div_le_iff₀ (by norm_num)]
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      rw [inv_le_comm₀ (sub_pos_of_lt hg1) two_pos]
      linear_combination hg2
    · simp_rw [← norm_pow, Asymptotics.isBigO_norm_left, pow_two]
      simpa using hgO.mul hgO

lemma tendsto_sqrt_atTop : Tendsto (√·) atTop atTop := by
  simp_rw [Real.sqrt_eq_rpow]
  exact tendsto_rpow_atTop (by norm_num)

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {X : ℕ → Ω → ℝ}

abbrev stdGaussian : ProbabilityMeasure ℝ :=
  ⟨gaussianReal 0 1, inferInstance⟩

abbrev invSqrtMulSum {Ω} (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  (√n)⁻¹ * ∑ i : Fin n, X i ω

lemma map_invSqrtMulSum (μ : Measure Ω) {X : ℕ → Ω → ℝ} (hX : ∀ n, Measurable (X n)) (n : ℕ) :
    μ.map (invSqrtMulSum X n)
      = ((μ.map (fun ω (i : Fin n) ↦ X i ω)).map (fun x ↦ ∑ i, x i)).map ((√n)⁻¹ * ·) := by
  rw [Measure.map_map, Measure.map_map]
  · rfl
  all_goals { fun_prop }

lemma measurable_invSqrtMulSum (n) (hX : ∀ n, Measurable (X n)) :
    Measurable (invSqrtMulSum X n) := by fun_prop

lemma aemeasurable_invSqrtMulSum {μ : Measure Ω} (n) (hX : ∀ n, Measurable (X n)) :
    AEMeasurable (invSqrtMulSum X n) μ := by fun_prop

theorem central_limit (hX : ∀ n, Measurable (X n))
    {P : ProbabilityMeasure Ω} (h0 : P[X 0] = 0) (h1 : P[X 0 ^ 2] = 1)
    (hindep : iIndepFun X P) (hident : ∀ (i : ℕ), IdentDistrib (X i) (X 0) P P) :
    Tendsto (fun n : ℕ => P.map (aemeasurable_invSqrtMulSum n hX)) atTop (𝓝 stdGaussian) := by
  refine ProbabilityMeasure.tendsto_iff_tendsto_charFun.mpr fun t ↦ ?_
  rw [stdGaussian, ProbabilityMeasure.coe_mk, charFun_gaussianReal]

  -- convert to independence over Fin n
  have indep_fin (n : ℕ) : iIndepFun (fun i : Fin n ↦ X i) P := by
    rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
    intro S s hs
    convert hindep.measure_inter_preimage_eq_mul (S.map Fin.valEmbedding)
      (sets := fun i ↦ if h : i < n then s ⟨i, h⟩ else ∅) ?_
    · simp
    · simp
    · simpa
  have pi_fin (n : ℕ) := (iIndepFun_iff_map_fun_eq_pi_map fun i : Fin n ↦ (hX i).aemeasurable).mp
    (indep_fin n)
  have map_eq (n : ℕ) := (hident n).map_eq

  -- use existing results to rewrite the charFun
  simp_rw [ProbabilityMeasure.toMeasure_map, ofReal_zero, mul_zero, zero_mul, NNReal.coe_one,
    ofReal_one, one_mul, zero_sub, map_invSqrtMulSum P.toMeasure hX, charFun_map_mul,
    pi_fin, map_eq, charFun_map_sum_pi_const]

  -- apply tendsto_one_plus_div_cpow_cexp; suffices to show the base is (1 - t ^ 2 / 2n + o(1 / n))
  norm_cast
  rw [ofReal_exp]
  apply tendsto_one_plus_div_cpow_cexp

  -- rewrite h0 and h1 as pushforward
  erw [← integral_map (hX 0).aemeasurable aestronglyMeasurable_id] at h0
  erw [← integral_map (hX 0).aemeasurable (aestronglyMeasurable_id.pow 2)] at h1
  dsimp only [Pi.pow_apply, id_eq] at h0 h1

  -- derive the required littleO result
  have hint : Integrable (|·| ^ 2) (P.toMeasure.map (X 0)) := by
    simp_rw [_root_.sq_abs]
    apply Integrable.of_integral_ne_zero
    rw [h1]
    norm_num
  have : IsProbabilityMeasure (P.toMeasure.map (X 0)) :=
    isProbabilityMeasure_map (hX 0).aemeasurable
  have t_mul_inv_sqrt := Tendsto.const_mul t <| tendsto_inv_atTop_zero.comp <|
    tendsto_sqrt_atTop.comp <| tendsto_natCast_atTop_atTop
  rw [mul_zero] at t_mul_inv_sqrt
  have littleO : _ =o[atTop] fun k ↦ _ := (taylor_charFun hint).comp_tendsto t_mul_inv_sqrt
  simp only [Nat.reduceAdd, ofReal_inv, ofReal_natCast, mul_pow, Finset.sum_range_succ,
    Finset.range_one, Finset.sum_singleton, Nat.factorial_zero, Nat.cast_one, inv_one, pow_zero,
    mul_one, integral_const, measure_univ, ENNReal.toReal_one, smul_eq_mul, ofReal_one,
    Nat.factorial_one, pow_one, one_mul, Nat.factorial_two, Nat.cast_ofNat, I_sq, mul_neg, neg_mul,
    Function.comp_apply, inv_pow, Nat.cast_nonneg, Real.sq_sqrt] at littleO

  -- littleO is what we wanted
  convert littleO.of_const_mul_right with n
  · -- simp? says
    simp only [ofReal_neg, ofReal_div, ofReal_pow, ofReal_ofNat, Function.comp_apply, ofReal_mul,
      ofReal_inv]
    rw [h0, h1]
    simp [mul_pow, mul_comm, ← ofReal_pow]
    ring
  · ext; apply one_div

end ProbabilityTheory
