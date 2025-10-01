/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Miyahara Kō, Lawrence Wu
-/
import Mathlib.MeasureTheory.Measure.Tight
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.Topology.MetricSpace.Sequences
import Mathlib.Order.Monotone.Union

open MeasureTheory Filter Topology TopologicalSpace Set EMetric
open scoped NNReal ENNReal

/-- **Prokhorov's theorem** -/
theorem isTightMeasureSet_iff_isCompact_closure
  {E : Type*} {mE : MeasurableSpace E} [MetricSpace E] [CompleteSpace E]
  [SecondCountableTopology E] [BorelSpace E] {S : Set (ProbabilityMeasure E)} :
    IsTightMeasureSet {((μ : ProbabilityMeasure E) : Measure E) | μ ∈ S}
      ↔ IsCompact (closure S) := by
  sorry -- do not work on this. Somebody claimed it.

lemma isCompact_closure_of_isTightMeasureSet
    {E : Type*} {mE : MeasurableSpace E} [MetricSpace E] [BorelSpace E]
    [SecondCountableTopology E] {S : Set (ProbabilityMeasure E)}
    (hS : IsTightMeasureSet {((μ : ProbabilityMeasure E) : Measure E) | μ ∈ S}) :
    IsCompact (closure S) := by
  suffices hPc : ∀ ⦃P : ℕ → ProbabilityMeasure E⦄, (∀ n, P n ∈ S) →
      ∃ P', ∃ N : ℕ → ℕ, StrictMono N ∧ Tendsto (P ∘ N) atTop (𝓝 P') by
    let := pseudoMetrizableSpacePseudoMetric (ProbabilityMeasure E)
    apply IsSeqCompact.isCompact
    intro P hPS
    have hP' (n : ℕ) : ∃ P' ∈ S, dist (P n) P' < 1 / (n + 1) :=
      Metric.mem_closure_iff.mp (hPS n) _ (by positivity)
    choose P' hP'S hP'P using hP'
    obtain ⟨P'', N, hN, hP''N⟩ := hPc hP'S
    refine ⟨P'', mem_closure_of_tendsto hP''N (by simp_all), N, hN, ?_⟩
    rw [tendsto_iff_dist_tendsto_zero] at *
    apply squeeze_zero (fun _ => dist_nonneg) (fun n => dist_triangle _ _ _)
    simpa using (squeeze_zero (fun _ => dist_nonneg) (fun n => le_of_lt (hP'P (N n)))
      (tendsto_one_div_add_atTop_nhds_zero_nat.comp hN.tendsto_atTop)).add hP''N
  intro P hP
  obtain ⟨u, hum, hult1, hut1⟩ := exists_seq_strictMono_tendsto' (show (0 : ℝ≥0) < 1 by norm_num)
  replace hult1 n := (hult1 n).right
  have hK (k : ℕ) : ∃ (K : Set E), IsCompact K ∧ (∀ n, u k ≤ P n K) := by
    rw [IsTightMeasureSet_iff_exists_isCompact_measure_compl_le] at hS
    specialize hS (1 - u k) (by rw [tsub_pos_iff_lt]; exact_mod_cast hult1 k)
    obtain ⟨K, hKc, hKm⟩ := hS
    use K, hKc
    intro n
    specialize hKm (P n) (by simpa [ProbabilityMeasure.toMeasure_injective.eq_iff] using hP n)
    rw [prob_compl_eq_one_sub hKc.measurableSet,
      ENNReal.sub_le_sub_iff_left (mod_cast (hult1 k).le) ENNReal.one_ne_top,
      ← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure] at hKm
    assumption_mod_cast
  replace hK : ∃ (K : ℕ → Set E),
      Monotone K ∧ (∀ n, IsCompact (K n)) ∧ (∀ n k, u n ≤ P k (K n)) := by
    choose K hKc hKP using hK
    use fun n => ⋃ m ≤ n, K m
    use monotone_nat_of_le_succ (fun n => by simp [biUnion_le_succ])
    use by
      intro n
      change IsCompact (⋃ m ∈ Iic n, K m)
      exact (finite_Iic n).isCompact_biUnion (fun m _ => hKc m)
    intro n k
    apply (hKP n k).trans
    apply ProbabilityMeasure.apply_mono
    exact subset_iUnion₂ (s := fun m (_ : m ≤ n) => K m) n le_rfl
  obtain ⟨K, hKm, hKc, hKP⟩ := hK
  have h𝓐 : ∃ (𝓐 : Set (Set E)), 𝓐.Countable ∧ (∀ A ∈ 𝓐, IsOpen A) ∧
      ∀ (G : Set E), IsOpen G → ∀ x ∈ (⋃ n, K n) ∩ G, ∃ A ∈ 𝓐, x ∈ A ∧ closure A ⊆ G := by
    obtain ⟨D, hD1, hD2⟩ := IsSeparable.iUnion (fun n => (hKc n).isSeparable)
    let 𝓐 := (fun p : E × ℚ ↦ Metric.ball p.1 p.2) '' D ×ˢ {q | 0 < q}
    refine ⟨𝓐, (hD1.prod (Set.to_countable _)).image _, ⟨by rintro _ ⟨_, _, rfl⟩; simp, ?_⟩⟩
    intro G hG x ⟨hxM, hxG⟩
    obtain ⟨ε, hε0, hεG⟩ : ∃ ε > 0, Metric.ball x ε ⊆ G := Metric.isOpen_iff.1 hG x hxG
    obtain ⟨q, hq_pos, hq_lt⟩ : ∃ q : ℚ, 0 < q ∧ q < ε / 2 :=
      mod_cast exists_rat_btwn (half_pos hε0)
    obtain ⟨c, hcD, hcb⟩ : ∃ c ∈ D, dist x c < q := by
      simp [Metric.mem_closure_iff.mp (hD2 hxM) q (mod_cast hq_pos)]
    refine ⟨_, ⟨⟨c, q⟩, ⟨hcD, hq_pos⟩, rfl⟩, by simpa, ?_⟩
    intro y hy
    have h_dist : dist y c ≤ q := by
      rw [Metric.mem_closure_iff] at hy
      refine le_of_forall_pos_le_add fun δ δ_pos => ?_
      obtain ⟨b, hb, hb'⟩ := hy δ δ_pos
      linarith [dist_triangle y b c, Metric.mem_ball.mp hb]
    exact hεG (Metric.mem_ball.mpr <| by linarith [dist_triangle_right y x c])
  obtain ⟨𝓐, h𝓐c, h𝓐o, h𝓐G⟩ := h𝓐
  let 𝓗 : Set (Set E) :=
    (fun P : Set (Set E × ℕ) => ⋃ p ∈ P, closure p.1 ∩ K p.2) ''
      {P : Set (Set E × ℕ) | P.Finite ∧ P ⊆ 𝓐 ×ˢ univ}
  have h𝓗H : 𝓗.Countable := Set.Countable.image
    (countable_setOf_finite_subset (h𝓐c.prod countable_univ)) _
  have h𝓗e : ∅ ∈ 𝓗 := by simp only [mem_image, 𝓗]; use ∅; simp
  replace h𝓗H := h𝓗H.exists_eq_range (nonempty_of_mem h𝓗e)
  obtain ⟨H, hH⟩ := h𝓗H
  have h𝓗c {H} (hH : H ∈ 𝓗) : IsCompact H := by
    simp only [𝓗, mem_image, mem_setOf] at hH
    obtain ⟨P, ⟨hPf, -⟩, rfl⟩ := hH
    exact hPf.isCompact_biUnion fun p hpP => (hKc p.2).inter_left isClosed_closure
  have h𝓗u {H₁} (hH₁ : H₁ ∈ 𝓗) {H₂} (hH₂ : H₂ ∈ 𝓗) : H₁ ∪ H₂ ∈ 𝓗 := by
    simp only [𝓗, mem_image, mem_setOf] at hH₁ hH₂ ⊢
    obtain ⟨P₁, ⟨hP₁f, hP₁𝓐⟩, rfl⟩ := hH₁
    obtain ⟨P₂, ⟨hP₂f, hP₂𝓐⟩, rfl⟩ := hH₂
    use P₁ ∪ P₂, ⟨hP₁f.union hP₂f, union_subset hP₁𝓐 hP₂𝓐⟩
    apply biUnion_union
  have h𝓗K (n) : K n ∈ 𝓗 := by
    have hK𝓐 : K n ⊆ ⋃ A ∈ 𝓐, A := by
      intro x hxK
      obtain ⟨A, hA𝓐, hxA, -⟩ := h𝓐G univ isOpen_univ x (by rw [inter_univ, mem_iUnion]; exists n)
      rw [mem_iUnion₂]
      exists A, hA𝓐
    obtain ⟨𝓐', h𝓐'𝓐, h𝓐'f, h𝓐'K⟩ := (hKc n).elim_finite_subcover_image h𝓐o hK𝓐
    simp only [mem_image, mem_setOf_eq, 𝓗]
    use 𝓐' ×ˢ {n}, ⟨h𝓐'f.prod (finite_singleton n), prod_mono h𝓐'𝓐 (subset_univ _)⟩
    simp only [biUnion_prod', biUnion_singleton, ← iUnion₂_inter, inter_eq_right]
    exact h𝓐'K.trans (iUnion₂_mono fun A hA => subset_closure)
  obtain ⟨N, hNφ, hNm, hNα⟩ :
      ∃ (N : ℕ → ℕ → ℕ), (Antitone (fun n => range (N n))) ∧
        (∀ n, StrictMono (N n)) ∧ ∀ n, ∃ α, Tendsto (fun k => P (N n k) (H n)) atTop (𝓝 α) := by
    have hφ n (N' : ℕ → ℕ) (hN' : StrictMono N') : ∃ (φ : ℕ → ℕ), StrictMono φ ∧
        ∃ α, Tendsto (fun k => P (N' (φ k)) (H n)) atTop (𝓝 α) := by
      obtain ⟨α, -, φ, hφm, hφα⟩ := tendsto_subseq_of_bounded (Metric.isBounded_Icc (0 : ℝ≥0) 1)
        (x := fun k => P (N' k) (H n)) (by simp)
      exact ⟨φ, hφm, α, hφα⟩
    choose! φ hφm hφα using hφ
    let N : ℕ → ℕ → ℕ := Nat.rec (φ 0 id) (fun n iN => iN ∘ (φ (n + 1) iN))
    have hN0 : N 0 = φ 0 id := rfl
    have hNs n : N (n + 1) = N n ∘ φ (n + 1) (N n) := rfl
    have hNm n : StrictMono (N n) := by
      induction n with
      | zero => exact hφm _ _ strictMono_id
      | succ n hn => exact hn.comp <| hφm _ _ hn
    refine ⟨N, ?hNf, hNm,
      Nat.recAux (hφα 0 id strictMono_id) (fun n hn => hφα (n + 1) (N n) (hNm n))⟩
    apply antitone_nat_of_succ_le
    intro n
    rw [hNs, range_comp]
    apply image_subset_range
  let N' n := N n n
  have hN'm : StrictMono N' := by
    intro m n hmn
    calc N m m
      _ < N m n := hNm m hmn
      _ ≤ N n n := by
        specialize hNφ hmn.le
        conv at hNφ => equals ∀ n', ∃ m', N m m' = N n n' => simp [subset_def]
        choose φ hφ using hNφ
        have hφm : StrictMono φ := by
          intro m₁ m₂ hm₁m₂; rwa [← (hNm m).lt_iff_lt, hφ, hφ, (hNm n).lt_iff_lt]
        rw [← hφ, (hNm m).le_iff_le]
        exact hφm.id_le n
  have hN'α : ∀ H ∈ 𝓗, ∃ α, Tendsto (fun n => P (N' n) H) atTop (𝓝 α) := by
    rw [hH, forall_mem_range]
    intro n
    peel hNα n with α hα
    conv at hNφ =>
      equals ∀ ⦃n m⦄, n ≤ m → ∀ m', ∃ n', N n n' = N m m' => simp [Antitone, subset_def]
    replace hNφ m (hnm : n ≤ m) := hNφ hnm m
    choose! φ' hφ' using hNφ
    let φ := (Ici n).piecewise φ' id
    have hφm : StrictMono φ := by
      have hφm₁ : StrictMonoOn φ (Ici n) := by
        intro m₁ (hm₁ : n ≤ m₁) m₂ (hm₂ : n ≤ m₂) hm₁m₂
        conv => equals φ' m₁ < φ' m₂ => simp [φ, hm₁, hm₂]
        rw [← (hNm n).lt_iff_lt, hφ' _ hm₁, hφ' _ hm₂]
        exact hN'm.imp hm₁m₂
      have hφm₂ : StrictMonoOn φ (Iic n) := by
        apply strictMonoOn_id.congr
        intro m (hm : m ≤ n)
        rw [le_iff_lt_or_eq] at hm
        obtain (hm | rfl) := hm
        case inl => simp [φ, hm]
        conv => equals m = φ' m => simp [φ]
        rw [← (hNm m).injective.eq_iff, hφ' m le_rfl]
      have hφ' := hφm₂.union hφm₁ isGreatest_Iic isLeast_Ici
      rwa [Iic_union_Ici, strictMonoOn_univ] at hφ'
    apply hα.comp hφm.tendsto_atTop |>.congr'
    rw [EventuallyEq, eventually_atTop]
    exact ⟨n, fun m hm => by simp [φ, hm, hφ', N']⟩
  choose! α hα using hN'α
  have hαm {H₁} (hH₁ : H₁ ∈ 𝓗) {H₂} (hH₂ : H₂ ∈ 𝓗) (hH₁H₂ : H₁ ⊆ H₂) : α H₁ ≤ α H₂ := by
    apply le_of_tendsto_of_tendsto' (hα H₁ hH₁) (hα H₂ hH₂)
    intro n
    exact ProbabilityMeasure.apply_mono _ hH₁H₂
  have hαu {H₁} (hH₁ : H₁ ∈ 𝓗) {H₂} (hH₂ : H₂ ∈ 𝓗) : α (H₁ ∪ H₂) ≤ α H₁ + α H₂ := by
    apply le_of_tendsto_of_tendsto' (hα _ (h𝓗u hH₁ hH₂)) ((hα H₁ hH₁).add (hα H₂ hH₂))
    intro n
    exact ProbabilityMeasure.apply_union_le _
  have hαud {H₁} (hH₁ : H₁ ∈ 𝓗) {H₂} (hH₂ : H₂ ∈ 𝓗) (hHd : Disjoint H₁ H₂) :
      α (H₁ ∪ H₂) = α H₁ + α H₂ := by
    apply tendsto_nhds_unique (hα _ (h𝓗u hH₁ hH₂))
    apply ((hα H₁ hH₁).add (hα H₂ hH₂)).congr
    intro n
    rw [← ENNReal.coe_inj]
    simp only [ENNReal.coe_add, ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure,
      measure_union hHd (h𝓗c hH₂).measurableSet]
  have hαK n : u n ≤ α (K n) := ge_of_tendsto' (hα (K n) (h𝓗K n)) fun k => hKP n (N' k)
  have hαb {H} (hH : H ∈ 𝓗) : α H ≤ 1 := by
    apply le_of_tendsto' (hα _ hH)
    intro n
    exact ProbabilityMeasure.apply_le_one _ _
  have hαe : α ∅ = 0 := by apply tendsto_nhds_unique (hα _ h𝓗e); simp
  have hαbd G : BddAbove (range (fun Hs : ↥{H : Set E | H ⊆ G ∧ H ∈ 𝓗} => α ↑Hs)) := by
    simp only [bddAbove_def, forall_mem_range]; exact ⟨1, fun Hs => hαb Hs.prop.right⟩
  haveI : ∀ (G : Set E), Nonempty ↥{H | H ⊆ G ∧ H ∈ 𝓗} := fun _ => ⟨⟨∅, empty_subset _, h𝓗e⟩⟩
  let β (G : Set E) := ⨆ Hs : ↥{H | H ⊆ G ∧ H ∈ 𝓗}, α ↑Hs
  have hβe : β ∅ = 0 := by
    rw [← NNReal.bot_eq_zero, eq_bot_iff]; unfold β; apply ciSup_le; simp [hαe]
  have hβb {G : Set E} (hG : IsOpen G) : β G ≤ 1 := by
    conv_lhs => simp only [β]
    apply ciSup_le
    simp only [Subtype.forall, and_imp, mem_setOf]
    intro H hHG hH𝓗
    exact hαb hH𝓗
  have hβm {M₁ M₂} (hM : M₁ ⊆ M₂) : β M₁ ≤ β M₂ :=
    ciSup_mono' (hαbd _) (by
      simp only [coe_setOf, mem_setOf_eq, Subtype.exists, exists_prop, Subtype.forall, and_imp]
      exact fun H hHM₁ hH𝓗 => ⟨H, ⟨hHM₁.trans hM, hH𝓗⟩, le_rfl⟩)
  suffices ∃ (P' : ProbabilityMeasure E), ∀ G, IsOpen G → P' G = β G by
    obtain ⟨P', hP'⟩ := this
    use P', N', hN'm
    apply tendsto_of_forall_isOpen_le_liminf_nat
    intro G hG
    simp only [hP' G hG, Function.comp_apply, β]
    apply ciSup_le
    simp only [Subtype.forall, and_imp, mem_setOf]
    intro H hHG hH𝓗
    rw [← hα H hH𝓗 |>.liminf_eq]
    refine liminf_le_liminf ?_ (by isBoundedDefault)
      (isCoboundedUnder_ge_of_le _ (x := 1) (by intro; bound))
    simp [ProbabilityMeasure.apply_mono _ hHG]
  have h𝓗o {F : Set E} (hF : IsClosed F) {G : Set E} (hG : IsOpen G) (hFG : F ⊆ G)
      (hF𝓗 : ∃ H ∈ 𝓗, F ⊆ H) : ∃ H₀ ∈ 𝓗, F ⊆ H₀ ∧ H₀ ⊆ G := by
    obtain ⟨H, hH𝓗, hFH⟩ := hF𝓗
    simp only [𝓗, mem_image, mem_setOf] at hH𝓗
    obtain ⟨P, ⟨hPf, hP𝓐⟩, rfl⟩ := hH𝓗
    obtain (rfl | hPn) := eq_empty_or_nonempty P
    case inl => (conv at hFH => equals F = ∅ => simp); subst hFH; use ∅
    let i₀ := hPf.toFinset.sup Prod.snd
    have hKi₀ : ⋃ p ∈ P, K p.2 = K i₀ := by
      conv_rhs => change K (hPf.toFinset.sup (id ∘ Prod.snd))
      rw [Finset.comp_sup_eq_sup_comp_of_nonempty hKm (by simp [hPn]), Finset.sup_eq_iSup]
      simp
    have hFKi₀ : F ⊆ K i₀ := by
      rw [← hKi₀]; exact hFH.trans (iUnion₂_mono fun p hp => inter_subset_right)
    have hFc : IsCompact F :=  (hKc i₀).of_isClosed_subset hF hFKi₀
    have hFA' x (hxF : x ∈ F) : ∃ A' ∈ 𝓐, x ∈ A' ∧ closure A' ⊆ G :=
      h𝓐G G hG x (by simp only [mem_inter_iff, mem_iUnion]; exact ⟨⟨i₀, hFKi₀ hxF⟩, hFG hxF⟩)
    choose! A' hA'𝓐 hA'x hA'G using hFA'
    obtain ⟨F', hF'F, hF'f, hF'F₂⟩ : ∃ F' ⊆ F, F'.Finite ∧ F ⊆ ⋃ x ∈ F', A' x :=
      hFc.elim_finite_subcover_image (fun x hx => h𝓐o _ (hA'𝓐 _ hx))
        (fun x hx => mem_iUnion₂_of_mem hx (hA'x x hx))
    use (⋃ x ∈ F', closure (A' x)) ∩ K i₀
    use by
      simp only [𝓗, mem_image, mem_setOf]
      exact ⟨(A' '' F') ×ˢ {i₀}, ⟨hF'f.image A' |>.prod (finite_singleton _),
        Set.prod_mono (image_subset_iff.mpr <| hF'F.trans hA'𝓐) (subset_univ _)⟩,
        by simp only [biUnion_prod', biUnion_singleton, biUnion_image, iUnion₂_inter]⟩
    use subset_inter (hF'F₂.trans <| iUnion₂_mono fun A' hA' => subset_closure) hFKi₀
    calc _
      _ ⊆ ⋃ x ∈ F', closure (A' x) := inter_subset_left
      _ ⊆ _ := iUnion₂_subset fun x hx => hA'G _ (hF'F hx)
  have hβa {G₁ : Set E} (hG₁ : IsOpen G₁) {G₂ : Set E} (hG₂ : IsOpen G₂) :
      β (G₁ ∪ G₂) ≤ β G₁ + β G₂ := by
    conv_lhs => simp only [β]
    apply ciSup_le
    simp only [Subtype.forall, and_imp, mem_setOf]
    intro H hHG hH𝓗
    let F₁ := H ∩ {x | infEdist x G₂ᶜ ≤ infEdist x G₁ᶜ}
    let F₂ := H ∩ {x | infEdist x G₁ᶜ ≤ infEdist x G₂ᶜ}
    have hHF : H = F₁ ∪ F₂ := by ext x; simp [F₁, F₂, ← and_or_left, le_total]
    have hF₁G₁ : F₁ ⊆ G₁ := by
      rw [← compl_subset_compl]
      intro x hx
      conv => equals x ∈ H → x ∈ G₂ =>
        simp [F₁, infEdist_zero_of_mem hx, ← mem_iff_infEdist_zero_of_closed hG₂.isClosed_compl]
      exact fun hxH => mem_union .. |>.mp (hHG hxH) |>.resolve_left hx
    have hF₂G₂ : F₂ ⊆ G₂ := by
      rw [← compl_subset_compl]
      intro x hx
      conv => equals x ∈ H → x ∈ G₁ =>
        simp [F₂, infEdist_zero_of_mem hx, ← mem_iff_infEdist_zero_of_closed hG₁.isClosed_compl]
      exact fun hxH => mem_union .. |>.mp (hHG hxH) |>.resolve_right hx
    have hF₁c : IsClosed F₁ :=
      (h𝓗c hH𝓗).isClosed.inter (isClosed_le continuous_infEdist continuous_infEdist)
    have hF₂c : IsClosed F₂ :=
      (h𝓗c hH𝓗).isClosed.inter (isClosed_le continuous_infEdist continuous_infEdist)
    obtain ⟨H₁, hH₁𝓗, hF₁H₁, hH₁G₁⟩ := h𝓗o hF₁c hG₁ hF₁G₁ ⟨H, hH𝓗, by simp [hHF]⟩
    obtain ⟨H₂, hH₂𝓗, hF₂H₂, hH₂G₂⟩ := h𝓗o hF₂c hG₂ hF₂G₂ ⟨H, hH𝓗, by simp [hHF]⟩
    calc _
      _ ≤ α (H₁ ∪ H₂) := hαm hH𝓗 (h𝓗u hH₁𝓗 hH₂𝓗) (by rw [hHF]; exact union_subset_union hF₁H₁ hF₂H₂)
      _ ≤ α H₁ + α H₂ := hαu hH₁𝓗 hH₂𝓗
      _ ≤ _ :=
        add_le_add (le_ciSup (hαbd G₁) ⟨H₁, hH₁G₁, hH₁𝓗⟩) (le_ciSup (hαbd G₂) ⟨H₂, hH₂G₂, hH₂𝓗⟩)
  replace hβa (I : Finset ℕ) {G : ℕ → Set E} (hG : ∀ n, IsOpen (G n)) :
      β (⋃ n ∈ I, G n) ≤ ∑ n ∈ I, β (G n) := by
    induction I using Finset.induction with
    | empty => simp [hβe]
    | insert n I hnI hnIi =>
      rw [Finset.set_biUnion_insert, Finset.sum_insert hnI]
      calc _
        _ ≤ β (G n) + β (⋃ x ∈ I, G x) := hβa (hG n) (isOpen_biUnion fun n _ => hG n)
        _ ≤ _ := add_le_add_left hnIi _
  replace hβa {G : ℕ → Set E} (hG : ∀ n, IsOpen (G n)) :
      (↑(β (⋃ n, G n)) : ℝ≥0∞) ≤ ∑' n, ↑(β (G n)) := by
    conv_lhs => simp only [β, ENNReal.coe_iSup (hαbd _)]
    apply ciSup_le
    simp only [Subtype.forall, and_imp, mem_setOf]
    intro H hHG hH𝓗
    obtain ⟨I, hIH⟩ := (h𝓗c hH𝓗).elim_finite_subcover _ hG hHG
    calc (↑(α H) : ℝ≥0∞)
      _ ≤ ↑(β (⋃ n ∈ I, G n)) := mod_cast le_ciSup (hαbd _) ⟨H, hIH, hH𝓗⟩
      _ ≤ ∑ n ∈ I, ↑(β (G n)) := mod_cast hβa _ hG
      _ ≤ _ := ENNReal.sum_le_tsum _
  haveI : ∀ (M : Set E), Nonempty ↥{G | M ⊆ G ∧ IsOpen G} :=
    fun _ => ⟨⟨univ, subset_univ _, isOpen_univ⟩⟩
  let γ (M : Set E) := ⨅ Gs : ↥{G | M ⊆ G ∧ IsOpen G}, β ↑Gs
  have hγm {M₁ M₂} (hM : M₁ ⊆ M₂) : γ M₁ ≤ γ M₂ := by
    apply le_ciInf
    simp only [Subtype.forall, and_imp, mem_setOf]
    intro G hM₂G hGo
    exact ciInf_le' (fun Gs : ↥{G : Set E | M₁ ⊆ G ∧ IsOpen G} => β ↑Gs) ⟨G, hM.trans hM₂G, hGo⟩
  have hγo {G} (hG : IsOpen G) : γ G = β G :=
    le_antisymm
      (ciInf_le' (fun Gs : ↥{G' : Set E | G ⊆ G' ∧ IsOpen G'} => β ↑Gs) ⟨G, subset_rfl, hG⟩)
      (by
        apply le_ciInf
        simp only [Subtype.forall, and_imp, mem_setOf]
        exact fun G₂ hGG₂ hG₂o => hβm hGG₂)
  have hγb (M) : γ M ≤ 1 :=
    (ciInf_le' (fun Gs : ↥{G' : Set E | M ⊆ G' ∧ IsOpen G'} => β ↑Gs)
      ⟨univ, subset_univ _, isOpen_univ⟩).trans (hβb isOpen_univ)
  let γμ : OuterMeasure E :=
    { measureOf M := ↑(γ M)
      empty := by
        rw [ENNReal.coe_eq_zero, ← NNReal.bot_eq_zero, eq_bot_iff, NNReal.bot_eq_zero]
        convert ciInf_le' (fun Gs : ↥{G : Set E | ∅ ⊆ G ∧ IsOpen G} => β ↑Gs)
          ⟨∅, empty_subset _, isOpen_empty⟩
        simp only [hβe]
      mono {M₁ M₂} hM₁M₂ := ENNReal.coe_le_coe_of_le (hγm hM₁M₂)
      iUnion_nat M hMp := by
        apply le_of_forall_pos_le_add
        intro ε hεp
        obtain ⟨ε', hε'p, hε'ε⟩ := ENNReal.exists_pos_sum_of_countable hεp.ne' ℕ
        have hG n : ∃ (G : Set E), IsOpen G ∧ M n ⊆ G ∧ β G < γ (M n) + ε' n := by
          have hG := exists_lt_of_ciInf_lt
            (lt_add_of_pos_right (⨅ Gs : ↥{G | M n ⊆ G ∧ IsOpen G}, β ↑Gs) (hε'p n))
          simp only [coe_setOf, mem_setOf_eq, Subtype.exists, exists_prop] at hG
          obtain ⟨G, ⟨hMG, hGo⟩, hGβ⟩ := hG
          exists G
        choose G hGo hMG hGβ using hG
        calc (↑(γ (⋃ n, M n)) : ℝ≥0∞)
          _ ≤ ↑(β (⋃ n, G n)) :=
            mod_cast ciInf_le' (fun Gs : ↥{G : Set E | ⋃ n, M n ⊆ G ∧ IsOpen G} => β ↑Gs)
              ⟨⋃ n, G n, iUnion_mono hMG, isOpen_iUnion hGo⟩
          _ ≤ ∑' n, ↑(β (G n)) := hβa hGo
          _ ≤ ∑' n, ↑(γ (M n) + ε' n) := ENNReal.tsum_le_tsum (fun n => mod_cast (hGβ n).le)
          _ ≤ ∑' n, ↑(γ (M n)) + ε := by
            simp only [ENNReal.coe_add, ENNReal.tsum_add]; exact add_le_add_left hε'ε.le _ }
  have hγμa (M : Set E) : γμ M = ↑(γ M) := rfl
  have hγGF {G : Set E} (hG : IsOpen G) {F : Set E} (hF : IsClosed F) :
      γ (G ∩ F) + γ (G \ F) ≤ β G := by
    apply le_of_forall_pos_le_add
    intro ε hεp
    have hH (F') : ∃ H₃ ∈ 𝓗, H₃ ⊆ G \ F' ∧ β (G \ F') ≤ α H₃ + ε / 2 := by
      obtain (hGF' | hGF') := eq_zero_or_pos (β (G \ F'))
      case inl => exact ⟨∅, h𝓗e, empty_subset _, by rw [hGF']; exact zero_le _⟩
      have hH₃ := exists_lt_of_lt_ciSup (tsub_lt_self hGF' (half_pos hεp))
      simp only [coe_setOf, mem_setOf_eq, Subtype.exists, exists_prop] at hH₃
      obtain ⟨H₃, ⟨hH₃G'F, hH₃𝓗⟩, hH₃α⟩ := hH₃
      exact ⟨H₃, hH₃𝓗, hH₃G'F, tsub_le_iff_right.mp hH₃α.le⟩
    obtain ⟨H₃, hH₃𝓗, hH₃GF, hH₃α⟩ := hH F
    obtain ⟨H₄, hH₄𝓗, hH₄GH₃, hH₄α⟩ := hH H₃
    calc γ (G ∩ F) + γ (G \ F)
      _ ≤ β (G \ H₃) + β (G \ F) :=
        add_le_add
          (ciInf_le' (fun Gs : ↥{G' : Set E | G ∩ F ⊆ G' ∧ IsOpen G'} => β ↑Gs)
            ⟨G \ H₃, subset_diff.mpr
              ⟨inter_subset_left, (subset_diff.mp hH₃GF).right.symm.mono_left
                inter_subset_right⟩, hG.sdiff (h𝓗c hH₃𝓗).isClosed⟩)
          (ciInf_le' (fun Gs : ↥{G' : Set E | G \ F ⊆ G' ∧ IsOpen G'} => β ↑Gs)
            ⟨G \ F, subset_rfl, hG.sdiff hF⟩)
      _ ≤ α H₃ + α H₄ + ε := by convert add_le_add hH₄α hH₃α using 1; ring
      _ = α (H₃ ∪ H₄) + ε := by rw [hαud hH₃𝓗 hH₄𝓗 (subset_diff.mp hH₄GH₃).right.symm]
      _ ≤ _ := add_le_add_right
        (le_ciSup (hαbd G)
          ⟨H₃ ∪ H₄, union_subset (hH₃GF.trans diff_subset) (hH₄GH₃.trans diff_subset),
            h𝓗u hH₃𝓗 hH₄𝓗⟩) _
  have hγc {F : Set E} (hF : IsClosed F) : γμ.IsCaratheodory F := by
    simp only [OuterMeasure.isCaratheodory_iff_le', hγμa, ← ENNReal.coe_add, ENNReal.coe_le_coe]
    intro L
    conv_rhs => unfold γ
    apply le_ciInf
    simp only [coe_setOf, mem_setOf_eq, Subtype.forall, and_imp]
    intro G hLG hGo
    exact (add_le_add (hγm (inter_subset_inter_left _ hLG))
      (hγm (diff_subset_diff_left hLG))).trans (hγGF hGo hF)
  let P : ProbabilityMeasure E := ⟨γμ.toMeasure (by
    borelize E
    rw [borel_eq_generateFrom_isClosed, MeasurableSpace.generateFrom_le_iff]
    exact fun L hL => hγc hL), ⟨by
    rw [toMeasure_apply _ _ MeasurableSet.univ, hγμa, ENNReal.coe_eq_one, ← (hγb univ).ge_iff_eq,
      hγo isOpen_univ, ← hut1.limsup_eq]
    refine limsup_le_of_le (by isBoundedDefault) (Eventually.of_forall fun n => ?_)
    exact (hαK n).trans (le_ciSup (hαbd univ) ⟨K n, subset_univ _, h𝓗K n⟩)⟩⟩
  use P
  intro G hG
  simp [P, hγμa, hG.measurableSet, hγo hG]
