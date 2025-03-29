/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Clt.CharFun

/-!
# Tightness and characteristic functions

-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace

lemma tendsto_iSup_of_tendsto_limsup {u : ℕ → ℝ → ℝ≥0∞}
    (h_all : ∀ n, Tendsto (u n) atTop (𝓝 0))
    (h_tendsto : Tendsto (fun r : ℝ ↦ limsup (fun n ↦ u n r) atTop) atTop (𝓝 0))
    (h_anti : ∀ n, Antitone (u n)) :
    Tendsto (fun r : ℝ ↦ ⨆ n, u n r) atTop (𝓝 0) := by
  simp_rw [ENNReal.tendsto_atTop_zero] at h_tendsto h_all ⊢
  intro ε hε
  by_cases hε_top : ε = ∞
  · refine ⟨0, fun _ _ ↦ by simp [hε_top]⟩
  simp only [gt_iff_lt, ge_iff_le] at h_tendsto h_all hε
  obtain ⟨r, h⟩ := h_tendsto (ε / 2) (ENNReal.half_pos hε.ne')
  have h' x (hx : r ≤ x) y (hy : ε / 2 < y) : ∀ᶠ n in atTop, u n x < y := by
    specialize h x hx
    rw [limsup_le_iff] at h
    exact h y hy
  replace h' : ∀ x, r ≤ x → ∀ᶠ n in atTop, u n x < ε :=
    fun x hx ↦ h' x hx ε (ENNReal.half_lt_self hε.ne' hε_top)
  simp only [eventually_atTop, ge_iff_le] at h'
  obtain ⟨N, h⟩ := h' r le_rfl
  replace h_all : ∀ ε > 0, ∀ n, ∃ N, ∀ n_1 ≥ N, u n n_1 ≤ ε := fun ε hε n ↦ h_all n ε hε
  choose rs hrs using h_all ε hε
  refine ⟨r ⊔ ⨆ n : Finset.range N, rs n, fun v hv ↦ ?_⟩
  simp only [Set.mem_setOf_eq, iSup_exists, iSup_le_iff, forall_apply_eq_imp_iff]
  intro n
  by_cases hn : n < N
  · refine hrs n v ?_
    calc rs n
    _ = rs (⟨n, by simp [hn]⟩ : Finset.range N) := rfl
    _ ≤ ⨆ n : Finset.range N, rs n := by
      refine le_ciSup (f := fun (x : Finset.range N) ↦ rs x) ?_ (⟨n, by simp [hn]⟩ : Finset.range N)
      exact Finite.bddAbove_range _
    _ ≤ r ⊔ ⨆ n : Finset.range N, rs n := le_max_right _ _
    _ ≤ v := hv
  · have hn_le : N ≤ n := not_lt.mp hn
    specialize h n hn_le
    refine (h_anti n ?_).trans h.le
    calc r
    _ ≤ r ⊔ ⨆ n : Finset.range N, rs n := le_max_left _ _
    _ ≤ v := hv

lemma iSup_set_seq {E : Type*} {_ : MeasurableSpace E} (μ : ℕ → Measure E) {s : Set E} :
    ⨆ μ' ∈ {μ n | n}, μ' s = ⨆ n, μ n s := by
  apply le_antisymm
  · simp only [Set.mem_setOf_eq, iSup_exists, iSup_le_iff, forall_apply_eq_imp_iff]
    intro n
    exact le_iSup (fun i ↦ μ i s) n
  · simp only [Set.mem_setOf_eq, iSup_exists, iSup_le_iff]
    intro n
    calc μ n s
    _ ≤ ⨆ i, ⨆ (_ : μ i = μ n), μ i s := le_biSup (fun i ↦ μ i s) rfl
    _ = ⨆ i, ⨆ (_ : μ i = μ n), μ n s := by
      convert rfl using 4 with m hm
      rw [hm]
    _ ≤ ⨆ μ', ⨆ i, ⨆ (_ : μ i = μ'), μ' s :=
      le_iSup (fun μ' ↦ ⨆ i, ⨆ (_ : μ i = μ'), μ' s) (μ n)

lemma isTightMeasureSet_singleton {α : Type*} {mα : MeasurableSpace α}
  [PseudoEMetricSpace α] [CompleteSpace α] [SecondCountableTopology α] [BorelSpace α]
  {μ : Measure α} [IsFiniteMeasure μ] :
    IsTightMeasureSet {μ} :=
  isTightMeasureSet_singleton_of_innerRegularWRT
    (innerRegular_isCompact_isClosed_measurableSet_of_finite _)

variable {E : Type*} {mE : MeasurableSpace E} [NormedAddCommGroup E]

lemma norm_le_mul_iSup_abs_inner {ι : Type*} [Fintype ι]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (x : E) :
    ‖x‖ ≤ √(Fintype.card ι) * ⨆ i, |⟪b i, x⟫| := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · have : x = 0 := Subsingleton.elim x 0
    simp [this]
  have h_rank : (0 : ℝ) < Fintype.card ι := by
    simp only [← Module.finrank_eq_card_basis b.toBasis, Nat.cast_pos, Module.finrank_pos_iff]
    infer_instance
  have : Nonempty ι := by simpa [Fintype.card_pos_iff] using h_rank
  calc ‖x‖
  _ = √(∑ i, ⟪b i, x⟫ ^ 2) := by
    simp_rw [norm_eq_sqrt_real_inner, ← OrthonormalBasis.sum_inner_mul_inner b x x,
      real_inner_comm _ x, ← pow_two]
  _ = √(∑ i, |⟪b i, x⟫| ^ 2) := by simp
  _ ≤ √(∑ _ : ι, (⨆ j, |⟪b j, x⟫|) ^ 2) := by
    gcongr with i
    exact le_ciSup (f := fun j ↦ |⟪b j, x⟫|) (by simp) i
  _ = √(Fintype.card ι) * ⨆ i, |⟪b i, x⟫| := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.cast_nonneg, Real.sqrt_mul]
    congr
    rw [Real.sqrt_sq]
    exact le_ciSup_of_le (by simp) (Nonempty.some this) (by positivity)

section FiniteDimensional

lemma isTightMeasureSet_of_tendsto_limsup_measure_norm_gt [BorelSpace E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {μ : ℕ → Measure E} [∀ i, IsFiniteMeasure (μ i)]
    (h : Tendsto (fun r : ℝ ↦ limsup (fun n ↦ μ n {x | r < ‖x‖}) atTop) atTop (𝓝 0)) :
    IsTightMeasureSet {μ n | n} := by
  refine isTightMeasureSet_of_tendsto_measure_norm_gt ?_
  convert tendsto_iSup_of_tendsto_limsup (fun n ↦ ?_) h fun n u v huv ↦ ?_ with y
  · exact iSup_set_seq μ
  · have h_tight : IsTightMeasureSet {μ n} :=
      isTightMeasureSet_singleton_of_innerRegularWRT
        (innerRegular_isCompact_isClosed_measurableSet_of_finite (μ n))
    rw [isTightMeasureSet_iff_tendsto_measure_norm_gt] at h_tight
    simpa using h_tight
  · refine measure_mono fun x hx ↦ ?_
    simp only [Set.mem_setOf_eq] at hx ⊢
    exact huv.trans_lt hx

lemma isTightMeasureSet_iff_tendsto_limsup_measure_norm_gt [BorelSpace E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {μ : ℕ → Measure E} [∀ i, IsFiniteMeasure (μ i)] :
    IsTightMeasureSet {μ n | n}
      ↔ Tendsto (fun r : ℝ ↦ limsup (fun n ↦ μ n {x | r < ‖x‖}) atTop) atTop (𝓝 0) := by
  refine ⟨fun h ↦ ?_, isTightMeasureSet_of_tendsto_limsup_measure_norm_gt⟩
  have h_sup := tendsto_measure_norm_gt_of_isTightMeasureSet h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h_sup (fun _ ↦ zero_le') ?_
  intro r
  simp_rw [iSup_set_seq]
  exact limsup_le_iSup

variable {ι : Type*} [Fintype ι]

lemma isTightMeasureSet_of_forall_basis_tendsto [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {S : Set (Measure E)} (b : OrthonormalBasis ι ℝ E)
    (h : ∀ i, Tendsto (fun r : ℝ ↦ ⨆ μ ∈ S, μ {x | r < |⟪b i, x⟫|}) atTop (𝓝 0)) :
    IsTightMeasureSet S := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · simp only [IsTightMeasureSet, cocompact_eq_bot, smallSets_bot]
    convert tendsto_pure_nhds (a := ∅) _
    simp
  have h_rank : (0 : ℝ) < Fintype.card ι := by
    simp only [← Module.finrank_eq_card_basis b.toBasis, Nat.cast_pos, Module.finrank_pos_iff]
    infer_instance
  have : Nonempty ι := by simpa [Fintype.card_pos_iff] using h_rank
  refine isTightMeasureSet_of_tendsto_measure_norm_gt ?_
  have h_le : (fun r ↦ ⨆ μ ∈ S, μ {x | r < ‖x‖})
      ≤ fun r ↦ ∑ i, ⨆ μ ∈ S, μ {x | r / √(Fintype.card ι) < |⟪b i, x⟫|} := by
    intro r
    calc ⨆ μ ∈ S, μ {x | r < ‖x‖}
    _ ≤ ⨆ μ ∈ S, μ (⋃ i, {x : E | r / √(Fintype.card ι) < |⟪b i, x⟫|}) := by
      gcongr with μ hμS
      intro x hx
      simp only [Set.mem_setOf_eq, Set.mem_iUnion] at hx ⊢
      have hx' : r < √(Fintype.card ι) * ⨆ i, |⟪b i, x⟫| :=
        hx.trans_le (norm_le_mul_iSup_abs_inner b x)
      rw [← div_lt_iff₀' (by positivity)] at hx'
      by_contra! h_le
      exact lt_irrefl (r / √(Fintype.card ι)) (hx'.trans_le (ciSup_le h_le))
    _ ≤ ⨆ μ ∈ S, ∑ i, μ {x : E | r / √(Fintype.card ι) < |⟪b i, x⟫|} := by
      gcongr with μ hμS
      exact measure_iUnion_fintype_le μ _
    _ ≤ ∑ i, ⨆ μ ∈ S, μ {x | r / √(Fintype.card ι) < |⟪b i, x⟫|} := by
      refine iSup_le fun μ ↦ (iSup_le fun hμS ↦ ?_)
      gcongr with i
      exact le_biSup (fun μ ↦ μ {x | r / √(Fintype.card ι) < |⟪b i, x⟫|}) hμS
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ (fun _ ↦ zero_le') h_le
  have : ∑ i : ι, (0 : ℝ≥0∞) = 0 := by simp
  rw [← this]
  refine tendsto_finset_sum Finset.univ fun i _ ↦ ?_
  refine (h i).comp ?_
  exact Tendsto.atTop_div_const (by positivity) tendsto_id

lemma isTightMeasureSet_iff_forall_basis_tendsto [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {S : Set (Measure E)} (b : OrthonormalBasis ι ℝ E) :
    IsTightMeasureSet S
      ↔ ∀ i, Tendsto (fun r : ℝ ↦ ⨆ μ ∈ S, μ {x | r < |⟪b i, x⟫|}) atTop (𝓝 0) := by
  refine ⟨fun h i ↦ ?_, isTightMeasureSet_of_forall_basis_tendsto b⟩
  rw [isTightMeasureSet_iff_tendsto_measure_norm_gt] at h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun _ ↦ zero_le') ?_
  intro r
  have h_le (μ : Measure E) : μ {x | r < |⟪b i, x⟫|} ≤ μ {x | r < ‖x‖} := by
    refine measure_mono fun x hx ↦ ?_
    simp only [Set.mem_setOf_eq] at hx ⊢
    refine hx.trans_le ?_
    refine (abs_real_inner_le_norm _ _).trans ?_
    simp
  simp only [iSup_le_iff]
  intro μ hμS
  refine le_iSup_of_le (i := μ) ?_
  simp only [hμS, iSup_pos]
  exact h_le μ

lemma isTightMeasureSet_of_forall_basis_tendsto_limsup [BorelSpace E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {μ : ℕ → Measure E} [∀ i, IsFiniteMeasure (μ i)]
    (b : OrthonormalBasis ι ℝ E)
    (h : ∀ i, Tendsto (fun r : ℝ ↦ limsup (fun n ↦ μ n {x | r < |⟪b i, x⟫|}) atTop) atTop (𝓝 0)) :
    IsTightMeasureSet {μ n | n} := by
  refine isTightMeasureSet_of_forall_basis_tendsto b fun i ↦ ?_
  convert tendsto_iSup_of_tendsto_limsup (fun n ↦ ?_) (h i) fun n u v huv ↦ ?_ with y
  · apply le_antisymm
    · simp only [Set.mem_setOf_eq, iSup_exists, iSup_le_iff, forall_apply_eq_imp_iff]
      exact fun n ↦ le_iSup (fun j ↦ μ j {x | y < |⟪b i, x⟫|}) n
    · simp only [Set.mem_setOf_eq, iSup_exists, iSup_le_iff]
      intro n
      calc μ n {x | y < |⟪b i, x⟫|}
      _ ≤ ⨆ j, ⨆ (_ : μ j = μ n), μ j {x | y < |⟪b i, x⟫|} :=
          le_biSup (fun j ↦ μ j {x | y < |⟪b i, x⟫|}) rfl
      _ = ⨆ j, ⨆ (_ : μ j = μ n), μ n {x | y < |⟪b i, x⟫|} := by
        convert rfl using 4 with m hm
        rw [hm]
      _ ≤ ⨆ μ', ⨆ j, ⨆ (_ : μ j = μ'), μ' {x | y < |⟪b i, x⟫|} :=
        le_iSup (fun μ' ↦ ⨆ j, ⨆ (_ : μ j = μ'), μ' {x | y < |⟪b i, x⟫|}) (μ n)
  · have h_tight : IsTightMeasureSet {(μ n).map (fun x ↦ ⟪b i, x⟫)} :=
      isTightMeasureSet_singleton
    rw [isTightMeasureSet_iff_tendsto_measure_norm_gt] at h_tight
    have h_map r : (μ n).map (fun x ↦ inner ((b) i) x) {x | r < |x|}
        = μ n {x | r < |⟪b i, x⟫|} := by
      rw [Measure.map_apply (by fun_prop)]
      · simp
      · exact MeasurableSet.preimage measurableSet_Ioi (by fun_prop)
    simpa [h_map] using h_tight
  · exact measure_mono fun x hx ↦ huv.trans_lt hx

lemma isTightMeasureSet_iff_forall_basis_tendsto_limsup [BorelSpace E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {μ : ℕ → Measure E} [∀ i, IsFiniteMeasure (μ i)] (b : OrthonormalBasis ι ℝ E) :
    IsTightMeasureSet {μ n | n}
      ↔ ∀ i, Tendsto (fun r : ℝ ↦ limsup (fun n ↦ μ n {x | r < |⟪b i, x⟫|}) atTop) atTop (𝓝 0) := by
  refine ⟨fun h i ↦ ?_, isTightMeasureSet_of_forall_basis_tendsto_limsup b⟩
  rw [isTightMeasureSet_iff_forall_basis_tendsto b] at h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (h i) (fun _ ↦ zero_le') ?_
  intro r
  simp_rw [iSup_set_seq]
  exact limsup_le_iSup

/-- Let $(\mu_n)_{n \in \mathbb{N}}$ be measures on $\mathbb{R}^d$ with characteristic functions
$(\hat{\mu}_n)$. If $\hat{\mu}_n$ converges pointwise to a function $f$ which is continuous at 0,
then $(\mu_n)$ is tight. -/
lemma isTightMeasureSet_of_tendsto_charFun [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [BorelSpace E]
    {μ : ℕ → Measure E} [∀ i, IsProbabilityMeasure (μ i)]
    {f : E → ℂ} (hf : ContinuousAt f 0) (hf_meas : Measurable f)
    (h : ∀ t, Tendsto (fun n ↦ charFun (μ n) t) atTop (𝓝 (f t))) :
    IsTightMeasureSet {μ i | i} := by
  refine isTightMeasureSet_of_forall_basis_tendsto_limsup (stdOrthonormalBasis ℝ E) fun i ↦ ?_
  have h_le n r := measure_abs_inner_ge_le_charFun (μ := μ n)
    (a := stdOrthonormalBasis ℝ E i) (r := r)
  suffices Tendsto (fun (r : ℝ) ↦
        limsup (fun n ↦ (μ n {x | r < |⟪stdOrthonormalBasis ℝ E i, x⟫|}).toReal) atTop)
      atTop (𝓝 0) by
    have h_ofReal r : limsup (fun n ↦ μ n {x | r < |⟪stdOrthonormalBasis ℝ E i, x⟫|}) atTop
        = ENNReal.ofReal
          (limsup (fun n ↦ (μ n {x | r < |⟪stdOrthonormalBasis ℝ E i, x⟫|}).toReal) atTop) := by
      rw [ENNReal.limsup_toReal_eq (b := 1)]
      · rw [ENNReal.ofReal_toReal]
        refine ne_of_lt ?_
        calc limsup (fun n ↦ (μ n) {x | r < |⟪stdOrthonormalBasis ℝ E i, x⟫|}) atTop
        _ ≤ 1 := by
          refine limsup_le_of_le ?_ ?_
          · exact IsCoboundedUnder.of_frequently_ge <| .of_forall fun _ ↦ zero_le'
          · exact .of_forall fun _ ↦ prob_le_one
        _ < ⊤ := by simp
      · simp
      · exact .of_forall fun _ ↦ prob_le_one
    simp_rw [h_ofReal]
    rw [← ENNReal.ofReal_zero]
    exact ENNReal.tendsto_ofReal this
  have h_le_4 n r (hr : 0 < r) :
      2⁻¹ * r * ‖∫ t in -2 * r⁻¹..2 * r⁻¹,
        1 - charFun (μ n) (t • stdOrthonormalBasis ℝ E i)‖ ≤ 4 := by
    have hr' : -(2 * r⁻¹) ≤ 2 * r⁻¹ := by rw [neg_le_self_iff]; positivity
    calc 2⁻¹ * r * ‖∫ t in -2 * r⁻¹..2 * r⁻¹, 1 - charFun (μ n) (t • stdOrthonormalBasis ℝ E i)‖
    _ ≤ 2⁻¹ * r
        * ∫ t in -(2 * r⁻¹)..2 * r⁻¹, ‖1 - charFun (μ n) (t • stdOrthonormalBasis ℝ E i)‖ := by
      simp only [neg_mul, intervalIntegrable_const]
      gcongr
      rw [intervalIntegral.integral_of_le hr', intervalIntegral.integral_of_le hr']
      exact norm_integral_le_integral_norm _
    _ ≤ 2⁻¹ * r * ∫ t in -(2 * r⁻¹)..2 * r⁻¹, 2 := by
      gcongr
      rw [intervalIntegral.integral_of_le hr', intervalIntegral.integral_of_le hr']
      refine integral_mono_of_nonneg ?_ (by fun_prop) ?_
      · exact ae_of_all _ fun _ ↦ by positivity
      · refine ae_of_all _ fun x ↦ norm_one_sub_charFun_le_two
    _ ≤ 4 := by
      simp only [neg_mul, intervalIntegral.integral_const, sub_neg_eq_add, smul_eq_mul]
      ring_nf
      rw [mul_inv_cancel₀ hr.ne', one_mul]
  -- We introduce an upper bound for the limsup.
  -- This is where we use the fact that `charFun (μ n)` converges to `f`.
  have h_limsup_le r (hr : 0 < r) :
      limsup (fun n ↦ (μ n {x | r < |⟪stdOrthonormalBasis ℝ E i, x⟫|}).toReal) atTop
        ≤ 2⁻¹ * r * ‖∫ t in -2 * r⁻¹..2 * r⁻¹, 1 - f (t • stdOrthonormalBasis ℝ E i)‖ := by
    calc limsup (fun n ↦ (μ n {x | r < |⟪stdOrthonormalBasis ℝ E i, x⟫|}).toReal) atTop
    _ ≤ limsup (fun n ↦ 2⁻¹ * r
        * ‖∫ t in -2 * r⁻¹..2 * r⁻¹, 1 - charFun (μ n) (t • stdOrthonormalBasis ℝ E i)‖) atTop := by
      refine limsup_le_limsup (.of_forall fun n ↦ h_le n r hr) ?_ ?_
      · exact IsCoboundedUnder.of_frequently_ge <| .of_forall fun _ ↦ ENNReal.toReal_nonneg
      · refine ⟨4, ?_⟩
        simp only [eventually_map, eventually_atTop, ge_iff_le]
        exact ⟨0, fun n _ ↦ h_le_4 n r hr⟩
    _ = 2⁻¹ * r * ‖∫ t in -2 * r⁻¹..2 * r⁻¹, 1 - f (t • stdOrthonormalBasis ℝ E i)‖ := by
      refine ((Tendsto.norm ?_).const_mul _).limsup_eq
      simp only [neg_mul, intervalIntegrable_const]
      have hr' : -(2 * r⁻¹) ≤ 2 * r⁻¹ := by rw [neg_le_self_iff]; positivity
      simp_rw [intervalIntegral.integral_of_le hr']
      refine tendsto_integral_of_dominated_convergence (fun _ ↦ 2) ?_ (by fun_prop) ?_ ?_
      · exact fun _ ↦ Measurable.aestronglyMeasurable <| by fun_prop
      · exact fun _ ↦ ae_of_all _ fun _ ↦ norm_one_sub_charFun_le_two
      · exact ae_of_all _ fun x ↦ tendsto_const_nhds.sub (h _)
  -- It suffices to show that the upper bound tends to 0.
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (h := fun r ↦ 2⁻¹ * r * ‖∫ t in -2 * r⁻¹..2 * r⁻¹, 1 - f (t • stdOrthonormalBasis ℝ E i)‖)
    ?_ ?_ ?_
  rotate_left
  · filter_upwards [eventually_gt_atTop 0] with r hr
    refine le_limsup_of_le ?_ fun u hu ↦ ?_
    · refine ⟨4, ?_⟩
      simp only [eventually_map, eventually_atTop, ge_iff_le]
      exact ⟨0, fun n _ ↦ (h_le n r hr).trans (h_le_4 n r hr)⟩
    · exact ENNReal.toReal_nonneg.trans hu.exists.choose_spec
  · filter_upwards [eventually_gt_atTop 0] with r hr using h_limsup_le r hr
  -- We now show that the upper bound tends to 0.
  -- This will follow from the fact that `f` is continuous at `0`.
  -- `⊢ Tendsto (fun r ↦ 2⁻¹ * r * ‖∫ t in -2 * r⁻¹..2 * r⁻¹,`
  --    `1 - f (t • stdOrthonormalBasis ℝ E i)‖) atTop (𝓝 0)`
  have hf_tendsto := hf.tendsto
  rw [Metric.tendsto_nhds_nhds] at hf_tendsto
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hf0 : f 0 = 1 := by symm; simpa using h 0
  simp only [gt_iff_lt, dist_eq_norm_sub', zero_sub, norm_neg, hf0] at hf_tendsto
  simp only [ge_iff_le, neg_mul, intervalIntegrable_const, dist_zero_right, norm_mul, norm_inv,
    Real.norm_ofNat, Real.norm_eq_abs, norm_norm]
  simp_rw [abs_of_nonneg (norm_nonneg _)]
  obtain ⟨δ, hδ, hδ_lt⟩ : ∃ δ, 0 < δ ∧ ∀ ⦃x : E⦄, ‖x‖ < δ → ‖1 - f x‖ < ε / 4 :=
    hf_tendsto (ε / 4) (by positivity)
  refine ⟨4 * δ⁻¹, fun r hrδ ↦ ?_⟩
  have hr : 0 < r := lt_of_lt_of_le (by positivity) hrδ
  have hr' : -(2 * r⁻¹) ≤ 2 * r⁻¹ := by rw [neg_le_self_iff]; positivity
  have h_le_Ioc x (hx : x ∈ Set.Ioc (-(2 * r⁻¹)) (2 * r⁻¹)) :
      ‖1 - f (x • stdOrthonormalBasis ℝ E i)‖ ≤ ε / 4 := by
    refine (hδ_lt ?_).le
    simp only [norm_smul, Real.norm_eq_abs, OrthonormalBasis.norm_eq_one, mul_one]
    calc |x|
    _ ≤ 2 * r⁻¹ := by
      rw [abs_le]
      rw [Set.mem_Ioc] at hx
      exact ⟨hx.1.le, hx.2⟩
    _ < δ := by
      rw [← lt_div_iff₀' (by positivity), inv_lt_comm₀ hr (by positivity)]
      refine lt_of_lt_of_le ?_ hrδ
      ring_nf
      gcongr
      norm_num
  rw [abs_of_nonneg hr.le]
  calc 2⁻¹ * r * ‖∫ t in -(2 * r⁻¹)..2 * r⁻¹, 1 - f (t • stdOrthonormalBasis ℝ E i)‖
  _ ≤ 2⁻¹ * r * ∫ t in -(2 * r⁻¹)..2 * r⁻¹, ‖1 - f (t • stdOrthonormalBasis ℝ E i)‖ := by
    gcongr
    rw [intervalIntegral.integral_of_le hr', intervalIntegral.integral_of_le hr']
    exact norm_integral_le_integral_norm _
  _ ≤ 2⁻¹ * r * ∫ t in -(2 * r⁻¹)..2 * r⁻¹, ε / 4 := by
    gcongr
    rw [intervalIntegral.integral_of_le hr', intervalIntegral.integral_of_le hr']
    refine integral_mono_ae ?_ (by fun_prop) ?_
    · refine Integrable.mono' (integrable_const (ε / 4)) ?_ ?_
      · exact Measurable.aestronglyMeasurable <| by fun_prop
      · simp_rw [norm_norm]
        exact ae_restrict_of_forall_mem measurableSet_Ioc h_le_Ioc
    · exact ae_restrict_of_forall_mem measurableSet_Ioc h_le_Ioc
  _ = ε / 2 := by
    simp only [intervalIntegral.integral_div, intervalIntegral.integral_const, sub_neg_eq_add,
      smul_eq_mul]
    ring_nf
    rw [mul_inv_cancel₀ hr.ne', one_mul]
  _ < ε := by simp [hε]

end FiniteDimensional

variable {ι : Type*} [InnerProductSpace ℝ E] {μ : ι → Measure E} [∀ i, IsProbabilityMeasure (μ i)]

section EquicontinuousAt

lemma equicontinuousAt_charFun_zero_of_isTightMeasureSet (hμ : IsTightMeasureSet {μ i | i}) :
    EquicontinuousAt (fun i ↦ charFun (μ i)) 0 := by
  sorry

lemma isTightMeasureSet_of_equicontinuousAt_charFun
    (hμ : EquicontinuousAt (fun i ↦ charFun (μ i)) 0) :
    IsTightMeasureSet {μ i | i} := by
  sorry

lemma isTightMeasureSet_iff_equicontinuousAt_charFun :
    IsTightMeasureSet {μ i | i} ↔ EquicontinuousAt (fun i ↦ charFun (μ i)) 0 :=
  ⟨equicontinuousAt_charFun_zero_of_isTightMeasureSet,
    isTightMeasureSet_of_equicontinuousAt_charFun⟩

end EquicontinuousAt
