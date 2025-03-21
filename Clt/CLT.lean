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

-- #check tendsto_one_plus_div_pow_exp
/-- `(1 + t/n + o(1/n)) ^ n → exp t`. -/
lemma tendsto_one_plus_div_pow_exp' {f : ℕ → ℂ} (t : ℝ)
    (hf : (fun n ↦ f n - (1 + t / n)) =o[atTop] fun n ↦ 1 / (n : ℝ)) :
    Tendsto (fun n ↦ f n ^ n) atTop (𝓝 (exp t)) := by
  sorry

lemma tendsto_sqrt_atTop : Tendsto (√·) atTop atTop := by
  simp_rw [Real.sqrt_eq_rpow]
  exact tendsto_rpow_atTop (by norm_num)

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {X : ℕ → Ω → ℝ}

/-- From PFR -/
theorem iIndepFun_iff_pi_map_eq_map {Ω : Type u_1} {_mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} {ι : Type*} {β : ι → Type*} [Fintype ι]
    (f : ∀ x : ι, Ω → β x) [m : ∀ x : ι, MeasurableSpace (β x)]
    [IsProbabilityMeasure μ] (hf : ∀ (x : ι), Measurable (f x)) :
    iIndepFun f μ ↔ Measure.pi (fun i ↦ μ.map (f i)) = μ.map (fun ω i ↦ f i ω) := by
  sorry

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
    Measurable (invSqrtMulSum X n) :=
  (Finset.measurable_sum _ fun _ _ ↦ (hX _)).const_mul _

lemma aemeasurable_invSqrtMulSum {μ : Measure Ω} (n) (hX : ∀ n, Measurable (X n)) :
    AEMeasurable (invSqrtMulSum X n) μ :=
  (measurable_invSqrtMulSum n hX).aemeasurable

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
  have pi_fin (n : ℕ) := (iIndepFun_iff_pi_map_eq_map _ fun i : Fin n ↦ hX i).mp (indep_fin n)
  have map_eq (n : ℕ) := (hident n).map_eq

  -- use existing results to rewrite the charFun
  simp_rw [ProbabilityMeasure.toMeasure_map, ofReal_zero, mul_zero, zero_mul, NNReal.coe_one,
    ofReal_one, one_mul, zero_sub, map_invSqrtMulSum P.toMeasure hX, charFun_map_mul,
    ← pi_fin, map_eq, charFun_map_sum_pi_const]

  -- apply tendsto_one_plus_div_pow_exp'; suffices to show the base is (1 - t ^ 2 / 2n + o(1 / n))
  norm_cast
  rw [ofReal_exp]
  apply tendsto_one_plus_div_pow_exp'

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
    mul_one, integral_const, measure_univ, ENNReal.one_toReal, smul_eq_mul, ofReal_one,
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
