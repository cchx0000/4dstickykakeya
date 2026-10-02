import Theorems.Thm_StickyKakeya4_packing_reference_source

open Filter MeasureTheory Set Metric
open scoped ENNReal

namespace StickyKakeya4.SubpowerReferenceNets

open PositiveCellRegularization PackingReferenceSource

/-!
One source and one reference sequence with every positive power slack.
A countable mixture of summable cell budgets is pruned only once. Consequently
its lower bounds hold simultaneously on the returned source, rather than on
separately chosen sources depending on the exponent. They are not assertions
about arbitrary subsequent restrictions.
-/

/-- Any countable family of finite total cell weights has one positive
restriction on which every family has a positive uniform threshold factor.
This combines all families before pruning, so its quantifier order is
`exists B, forall k, exists c`. -/
theorem exists_simultaneous_positive_restriction
    {X ι : Type*} [MeasurableSpace X] [Countable ι]
    (μ : Measure X) [IsFiniteMeasure μ] (hμ : 0 < μ Set.univ)
    (F : ι → Set X) (hF : ∀ i, MeasurableSet (F i))
    (w : ℕ → ι → ENNReal) (hw : ∀ k, (∑' i, w k i) ≠ ⊤) :
    ∃ B : Set X, MeasurableSet B ∧ μ Bᶜ < μ Set.univ / 2 ∧ 0 < μ B ∧
      ∀ k, ∃ c : ENNReal, 0 < c ∧ c ≤ 1 ∧
        ∀ i, (μ.restrict B) (F i) = 0 ∨ c * w k i ≤ (μ.restrict B) (F i) := by
  classical
  have hchoose (k : ℕ) : ∃ q : ENNReal, 0 < q ∧ q ≤ 1 ∧
      q * (∑' i, w k i) ≤ (1 / 2 : ENNReal) ^ k := by
    have htarget : (1 / 2 : ENNReal) ^ k ≠ 0 := pow_ne_zero _ (by norm_num)
    obtain ⟨q, hq, hqsmall⟩ := ENNReal.exists_pos_mul_lt (hw k) htarget
    refine ⟨min q 1, lt_min hq (by norm_num), min_le_right _ _, ?_⟩
    exact (mul_le_mul' (min_le_left _ _) le_rfl).trans hqsmall.le
  choose q hq hqone hqbudget using hchoose
  let W : ι → ENNReal := fun i => ∑' k, q k * w k i
  have hW : (∑' i, W i) ≠ ⊤ := by
    have hgeom : (∑' k : ℕ, (1 / 2 : ENNReal) ^ k) ≠ ⊤ :=
      (tsum_geometric_lt_top.mpr (by norm_num)).ne
    apply ne_top_of_le_ne_top hgeom
    calc
      (∑' i, W i) = ∑' k, q k * (∑' i, w k i) := by
        dsimp [W]
        rw [ENNReal.tsum_comm]
        congr 1
        funext k
        exact ENNReal.tsum_mul_left
      _ ≤ ∑' k : ℕ, (1 / 2 : ENNReal) ^ k := ENNReal.tsum_le_tsum hqbudget
  obtain ⟨c, hc, hc1, B, hB, hloss, hpos, hcells⟩ :=
    exists_positive_restriction_of_finite_weight μ F W hF hμ hW
  refine ⟨B, hB, hloss, hpos, fun k => ⟨c * q k, ?_, ?_, ?_⟩⟩
  · exact ENNReal.mul_pos hc.ne' (hq k).ne'
  · exact (mul_le_mul' hc1 (hqone k)).trans (by simp)
  · intro i
    rcases hcells i with hz | hge
    · exact Or.inl hz
    · right
      calc
        c * q k * w k i = c * (q k * w k i) := mul_assoc _ _ _
        _ ≤ c * W i := mul_le_mul' le_rfl (ENNReal.le_tsum k)
        _ ≤ (μ.restrict B) (F i) := hge

/-- Simultaneous subpower lower cell masses. The upper-cardinality hypothesis
allows arbitrary positive slack, and a single positive source enjoys all the
corresponding lower mass bounds. -/
theorem exists_subpower_positive_restriction
    {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (hμ : 0 < μ Set.univ)
    (β : ℕ → Type*) [∀ n, Fintype (β n)]
    (F : ∀ n, β n → Set X) (hF : ∀ n i, MeasurableSet (F n i))
    (d : ℝ)
    (hcard : ∀ ε : ℝ, 0 < ε → ∃ C : ENNReal, C ≠ ⊤ ∧
      ∀ n, (Fintype.card (β n) : ENNReal) ≤
        C * (dyadicScale n) ^ (-(d + ε))) :
    ∃ B : Set X, MeasurableSet B ∧ μ Bᶜ < μ Set.univ / 2 ∧ 0 < μ B ∧
      ∀ ε : ℝ, 0 < ε → ∃ c : ENNReal, 0 < c ∧ c ≤ 1 ∧
        ∀ n i, (μ.restrict B) (F n i) = 0 ∨
          c * (dyadicScale n) ^ (d + ε) ≤ (μ.restrict B) (F n i) := by
  let δ : ℕ → ℝ := fun k => 1 / (k + 1 : ℝ)
  have hδ (k : ℕ) : 0 < δ k := by dsimp [δ]; positivity
  have hw (k : ℕ) : (∑' p : Sigma β, (dyadicScale p.1) ^ (d + δ k)) ≠ ⊤ := by
    obtain ⟨C, hC, hCbound⟩ := hcard (δ k / 2) (by positivity)
    have h := multiscale_weight_ne_top β C hC (d + δ k / 2)
      (δ k / 2) (by positivity) hCbound
    simpa only [show d + δ k / 2 + δ k / 2 = d + δ k by ring] using h
  obtain ⟨B, hB, hloss, hpos, hcells⟩ :=
    exists_simultaneous_positive_restriction μ hμ (fun p : Sigma β => F p.1 p.2)
      (fun p => hF p.1 p.2) (fun k p => (dyadicScale p.1) ^ (d + δ k)) hw
  refine ⟨B, hB, hloss, hpos, ?_⟩
  intro ε hε
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
  obtain ⟨c, hc, hc1, hcBound⟩ := hcells k
  refine ⟨c, hc, hc1, ?_⟩
  intro n i
  rcases hcBound ⟨n, i⟩ with hz | hge
  · exact Or.inl hz
  · right
    exact (mul_le_mul' le_rfl
      (ENNReal.rpow_le_rpow_of_exponent_ge (dyadicScale_le_one n)
        (show d + δ k ≤ d + ε by dsimp [δ]; linarith))).trans hge

/-- Construct the fixed geometric references against the covering number
itself, rather than against one selected power bound. Thus the same sequence
inherits every exponent estimate. One simultaneous pruning then supplies all
positive lower-mass slacks on one positive source. -/
theorem exists_dyadic_subpower_reference_source
    {X Y : Type*} [MeasurableSpace X] [PseudoMetricSpace Y]
    [MeasurableSpace Y] [BorelSpace Y]
    (μ : Measure X) [IsFiniteMeasure μ] (hμ : 0 < μ Set.univ)
    (f : X → Y) (hf : Measurable f)
    (S : Set Y) (hS : MeasurableSet S) (hsupport : μ (f ⁻¹' S)ᶜ = 0)
    (d : ℝ) (hd : 0 ≤ d)
    (hcover : ∀ ε : ℝ, 0 < ε → ∃ C : ENNReal, C ≠ ⊤ ∧ ∀ n,
      coveringNumber S (dyadicRadius n / 4) ≤
        C * (dyadicScale n) ^ (-(d + ε))) :
    ∃ B : Set X, MeasurableSet B ∧ B ⊆ f ⁻¹' S ∧
      μ Bᶜ < μ Set.univ / 2 ∧ 0 < μ B ∧
      ∃ nets : ℕ → Finset Y,
        (∀ n, (∀ y ∈ nets n, y ∈ S) ∧
          (∀ y ∈ nets n, ∀ z ∈ nets n, y ≠ z →
            dyadicRadius n / 2 ≤ dist y z) ∧
          coversAtRadius (f '' B) (dyadicRadius n) (nets n)) ∧
        ∀ ε : ℝ, 0 < ε → ∃ c D : ENNReal,
          0 < c ∧ c ≤ 1 ∧ D ≠ ⊤ ∧ ∀ n,
            ((nets n).card : ENNReal) ≤ D * (dyadicScale n) ^ (-(d + ε)) ∧
            ∀ y ∈ nets n, c * (dyadicScale n) ^ (d + ε) ≤
              (Measure.map f (μ.restrict B)) (Metric.ball y (dyadicRadius n)) := by
  classical
  have hscale0 (n : ℕ) : dyadicScale n ≠ 0 := pow_ne_zero _ (by norm_num)
  have hscaleTop (n : ℕ) : dyadicScale n ≠ ⊤ := ENNReal.pow_ne_top (by norm_num)
  have hcoverTop (n : ℕ) : coveringNumber S (dyadicRadius n / 4) ≠ ⊤ := by
    obtain ⟨C, hC, hCbound⟩ := hcover 1 (by norm_num)
    exact ne_top_of_le_ne_top (ENNReal.mul_ne_top hC
      (ENNReal.rpow_ne_top_of_ne_zero (hscale0 n) (hscaleTop n))) (hCbound n)
  obtain ⟨original, horiginal⟩ :=
    coveringNumber_bounds_extract_supported_separated_nets S dyadicRadius
      (fun n => coveringNumber S (dyadicRadius n / 4)) dyadicRadius_pos hcoverTop
      (fun _ => le_rfl)
  have hcard : ∀ ε : ℝ, 0 < ε → ∃ D : ENNReal, D ≠ ⊤ ∧ ∀ n,
      ((original n).card : ENNReal) ≤ D * (dyadicScale n) ^ (-(d + ε)) := by
    intro ε hε
    obtain ⟨C, hC, hCbound⟩ := hcover ε hε
    refine ⟨C + 1, by simpa using hC, ?_⟩
    intro n
    have hone : (1 : ENNReal) ≤ (dyadicScale n) ^ (-(d + ε)) := by
      simpa using ENNReal.rpow_le_rpow_of_exponent_ge (dyadicScale_le_one n)
        (show -(d + ε) ≤ (0 : ℝ) by linarith)
    calc
      ((original n).card : ENNReal) ≤ coveringNumber S (dyadicRadius n / 4) + 1 :=
        (horiginal n).2.2.2.le
      _ ≤ C * (dyadicScale n) ^ (-(d + ε)) + (dyadicScale n) ^ (-(d + ε)) :=
        add_le_add (hCbound n) hone
      _ = (C + 1) * (dyadicScale n) ^ (-(d + ε)) := by rw [add_mul, one_mul]
  let β : ℕ → Type _ := fun n => {y // y ∈ original n}
  let F : ∀ n, β n → Set X := fun n y => f ⁻¹' Metric.ball y (dyadicRadius n)
  have hF (n : ℕ) (y : β n) : MeasurableSet (F n y) :=
    measurableSet_ball.preimage hf
  have hcardβ : ∀ ε : ℝ, 0 < ε → ∃ D : ENNReal, D ≠ ⊤ ∧ ∀ n,
      (Fintype.card (β n) : ENNReal) ≤ D * (dyadicScale n) ^ (-(d + ε)) := by
    simpa [β] using hcard
  obtain ⟨B₀, hB₀, hloss₀, hpos₀, hcells₀⟩ :=
    exists_subpower_positive_restriction μ hμ β F hF d hcardβ
  let B₁ : Set X := B₀ ∩ f ⁻¹' S
  have hB₁ : MeasurableSet B₁ := hB₀.inter (hS.preimage hf)
  have hB₁ae : B₁ =ᵐ[μ] B₀ := inter_ae_eq_left_of_ae_eq_univ (ae_eq_univ.mpr hsupport)
  obtain ⟨B, hBB₁, hB, hBae₁, _hrestrict, hoccupied⟩ :=
    exists_clean_restriction μ B₁ hB₁ (fun p : Sigma β => F p.1 p.2)
      (fun p => hF p.1 p.2)
  have hBae : B =ᵐ[μ] B₀ := hBae₁.trans hB₁ae
  have hrestrict₀ : μ.restrict B = μ.restrict B₀ := Measure.restrict_congr_set hBae
  have hloss : μ Bᶜ < μ Set.univ / 2 := by
    rw [measure_congr hBae.compl]
    exact hloss₀
  have hpos : 0 < μ B := by rwa [measure_congr hBae]
  let nets : ℕ → Finset Y := fun n => (original n).filter fun y =>
    0 < (μ.restrict B) (f ⁻¹' Metric.ball y (dyadicRadius n))
  refine ⟨B, hB, fun x hx => (hBB₁ hx).2, hloss, hpos, nets, ?_, ?_⟩
  · intro n
    refine ⟨?_, ?_, ?_⟩
    · intro y hy
      exact (horiginal n).1 y (Finset.mem_filter.mp hy).1
    · intro y hy z hz hyz
      exact (horiginal n).2.1 y (Finset.mem_filter.mp hy).1 z
        (Finset.mem_filter.mp hz).1 hyz
    · rintro _ ⟨x, hx, rfl⟩
      have hxS : f x ∈ S := (hBB₁ hx).2
      obtain ⟨y, hy⟩ := Set.mem_iUnion.mp ((horiginal n).2.2.1 hxS)
      obtain ⟨hyOriginal, hxy⟩ := Set.mem_iUnion.mp hy
      have hpositive : 0 < (μ.restrict B) (f ⁻¹' Metric.ball y (dyadicRadius n)) :=
        hoccupied ⟨n, ⟨y, hyOriginal⟩⟩ ⟨x, hx, hxy⟩
      exact Set.mem_iUnion.mpr ⟨y,
        Set.mem_iUnion.mpr ⟨Finset.mem_filter.mpr ⟨hyOriginal, hpositive⟩, hxy⟩⟩
  · intro ε hε
    obtain ⟨c, hc, hc1, hcellBound⟩ := hcells₀ ε hε
    obtain ⟨D, hD, hcardBound⟩ := hcard ε hε
    refine ⟨c, D, hc, hc1, hD, ?_⟩
    intro n
    refine ⟨?_, ?_⟩
    · exact (show ((nets n).card : ENNReal) ≤ ((original n).card : ENNReal) by
        exact_mod_cast Finset.card_filter_le (original n) (fun y =>
          0 < (μ.restrict B) (f ⁻¹' Metric.ball y (dyadicRadius n)))).trans
        (hcardBound n)
    · intro y hy
      obtain ⟨hyOriginal, hypos⟩ := Finset.mem_filter.mp hy
      rw [Measure.map_apply hf measurableSet_ball]
      have hcell := hcellBound n ⟨y, hyOriginal⟩
      change (μ.restrict B₀) (f ⁻¹' Metric.ball y (dyadicRadius n)) = 0 ∨
        c * (dyadicScale n) ^ (d + ε) ≤
          (μ.restrict B₀) (f ⁻¹' Metric.ball y (dyadicRadius n)) at hcell
      rw [← hrestrict₀] at hcell
      exact hcell.resolve_left hypos.ne'

/-- Upper Minkowski dimension at most three gives all positive-slack dyadic
quarter-radius covers, with a separate finite constant for each slack. The
endpoint of the defining infimum is never assumed to be attained. -/
theorem upperMinkowskiDim_le_three_dyadic_cover
    {Y : Type*} [PseudoMetricSpace Y]
    (S : Set Y) (hdim : upperMinkowskiDim S ≤ 3) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ENNReal, C ≠ ⊤ ∧ ∀ n,
      coveringNumber S (dyadicRadius n / 4) ≤
        C * (dyadicScale n) ^ (-(3 + ε)) := by
  intro ε hε
  have hlt : upperMinkowskiDim S < ENNReal.ofReal (3 + ε) := by
    apply hdim.trans_lt
    rw [show (3 : ENNReal) = ENNReal.ofReal (3 : ℝ) by norm_num]
    exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr (by linarith)
  obtain ⟨a, ha, hatop, C, hC, hbound⟩ :=
    upperMinkowskiDim_lt_extract_power_bound S hlt
  have haReal : a.toReal < 3 + ε := by
    have h := (ENNReal.toReal_lt_toReal hatop ENNReal.ofReal_ne_top).mpr ha
    simpa only [ENNReal.toReal_ofReal (show 0 ≤ 3 + ε by linarith)] using h
  obtain ⟨δ, hδ, hsmall⟩ := eventually_nhdsGT_extract_cutoff hbound
  have hhalf : ∀ᶠ r in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      coveringNumber S r ≤ C * (ENNReal.ofReal (r / 2)) ^ (-a.toReal) := by
    apply mem_nhdsGT_iff_exists_Ioc_subset.mpr
    refine ⟨δ, hδ, ?_⟩
    intro r hr
    exact (coveringNumber_anti_radius S (show r / 2 ≤ r by linarith [hr.1])).trans
      (hsmall (r / 2) (by linarith [hr.1]) (by linarith [hr.1, hr.2]))
  obtain ⟨_, _, _, CAll, hCAll, _, hAll⟩ :=
    eventual_covering_bound_extend_to_unit_interval S hC hhalf
  obtain ⟨D, hD, hDcover⟩ := unit_power_cover_implies_dyadic S CAll hCAll a.toReal hAll
  refine ⟨D, hD, ?_⟩
  intro n
  exact (hDcover n).trans (mul_le_mul' le_rfl
    (ENNReal.rpow_le_rpow_of_exponent_ge (dyadicScale_le_one n) (by linarith)))

/-- From one compact phase support of upper Minkowski dimension at most
three, construct one positive source and one supported separated dyadic net
sequence. Their occupied-ball masses and cardinalities obey the subpower
bounds simultaneously for every positive real exponent slack. -/
theorem exists_upperMinkowskiDim_le_three_reference_source
    {X Y : Type*} [MeasurableSpace X] [MetricSpace Y]
    [MeasurableSpace Y] [BorelSpace Y]
    (μ : Measure X) [IsFiniteMeasure μ]
    (f : X → Y) (hf : Measurable f)
    (S : Set Y) (hS : IsCompact S)
    (hmass : 0 < (Measure.map f μ) S) (hdim : upperMinkowskiDim S ≤ 3) :
    ∃ B : Set X, MeasurableSet B ∧ B ⊆ f ⁻¹' S ∧ 0 < μ B ∧
      ∃ nets : ℕ → Finset Y,
        (∀ n, (∀ y ∈ nets n, y ∈ S) ∧
          (∀ y ∈ nets n, ∀ z ∈ nets n, y ≠ z →
            dyadicRadius n / 2 ≤ dist y z) ∧
          coversAtRadius (f '' B) (dyadicRadius n) (nets n)) ∧
        ∀ ε : ℝ, 0 < ε → ∃ c D : ENNReal,
          0 < c ∧ c ≤ 1 ∧ D ≠ ⊤ ∧ ∀ n,
            ((nets n).card : ENNReal) ≤ D * (dyadicScale n) ^ (-(3 + ε)) ∧
            ∀ y ∈ nets n, c * (dyadicScale n) ^ (3 + ε) ≤
              (Measure.map f (μ.restrict B)) (Metric.ball y (dyadicRadius n)) := by
  have hSmeas : MeasurableSet S := hS.isClosed.measurableSet
  have hpre : MeasurableSet (f ⁻¹' S) := hSmeas.preimage hf
  let σ : Measure X := μ.restrict (f ⁻¹' S)
  have hσpos : 0 < σ Set.univ := by
    simpa only [σ, Measure.restrict_apply_univ, Measure.map_apply hf hSmeas] using hmass
  have hσsupport : σ (f ⁻¹' S)ᶜ = 0 := by
    rw [show σ = μ.restrict (f ⁻¹' S) from rfl, Measure.restrict_apply hpre.compl]
    simp
  obtain ⟨B, hB, hBS, _hloss, hBpos, nets, hgeometry, hbounds⟩ :=
    exists_dyadic_subpower_reference_source σ hσpos f hf S hSmeas hσsupport
      3 (by norm_num) (upperMinkowskiDim_le_three_dyadic_cover S hdim)
  have hrestrict : σ.restrict B = μ.restrict B := Measure.restrict_restrict_of_subset hBS
  have hBmass : 0 < μ B := by
    rwa [show σ B = μ B from Measure.restrict_eq_self μ hBS] at hBpos
  refine ⟨B, hB, hBS, hBmass, nets, hgeometry, ?_⟩
  intro ε hε
  obtain ⟨c, D, hc, hc1, hD, hb⟩ := hbounds ε hε
  exact ⟨c, D, hc, hc1, hD, fun n => by simpa only [hrestrict] using hb n⟩

end StickyKakeya4.SubpowerReferenceNets
