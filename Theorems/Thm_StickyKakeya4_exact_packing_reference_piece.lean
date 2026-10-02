import Theorems.Thm_StickyKakeya4_compact_packing_power_piece

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace StickyKakeya4

theorem upperMinkowskiDim_mono
    {X : Type*} [PseudoMetricSpace X] {s t : Set X} (hst : s ⊆ t) :
    upperMinkowskiDim s ≤ upperMinkowskiDim t := by
  rw [upperMinkowskiDim, upperMinkowskiDim]
  apply sInf_le_sInf
  rintro d ⟨hd, C, hC, hbound⟩
  refine ⟨hd, C, hC, ?_⟩
  filter_upwards [hbound] with r hr
  exact (coveringNumber_mono hst r).trans hr

theorem upperMinkowskiDim_closure_le
    {X : Type*} [PseudoMetricSpace X] (s : Set X) :
    upperMinkowskiDim (closure s) ≤ upperMinkowskiDim s := by
  unfold upperMinkowskiDim
  apply le_sInf
  rintro d ⟨hd, C, hC, hbound⟩
  apply sInf_le
  refine ⟨hd, C * (ENNReal.ofReal (1 / 2 : ℝ)).rpow (-d.toReal), ?_, ?_⟩
  · exact ENNReal.mul_ne_top hC
      (ENNReal.rpow_ne_top_of_ne_zero (by norm_num) ENNReal.ofReal_ne_top)
  obtain ⟨δ, hδ, hsmall⟩ := eventually_nhdsGT_extract_cutoff hbound
  have hevent : ∀ᶠ r in 𝓝[>] (0 : ℝ), r ∈ Ioc 0 δ :=
    mem_nhdsGT_iff_exists_Ioc_subset.mpr ⟨δ, hδ, Subset.rfl⟩
  filter_upwards [hevent] with r hr
  calc
    coveringNumber (closure s) r ≤ coveringNumber s (r / 2) :=
      coveringNumber_closure_le s hr.1
    _ ≤ C * (ENNReal.ofReal (r / 2)).rpow (-d.toReal) :=
      hsmall (r / 2) (by linarith [hr.1]) (by linarith [hr.1, hr.2])
    _ = (C * (ENNReal.ofReal (1 / 2 : ℝ)).rpow (-d.toReal)) *
        (ENNReal.ofReal r).rpow (-d.toReal) := by
      simp only [ENNReal.rpow_eq_pow]
      rw [div_eq_mul_inv, ← one_div (2 : ℝ), ENNReal.ofReal_mul hr.1.le,
        ENNReal.mul_rpow_of_ne_top (x := ENNReal.ofReal r) (y := ENNReal.ofReal (1 / 2 : ℝ))
          ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top (-d.toReal)]
      ac_rfl

theorem upperMinkowskiDim_closure
    {X : Type*} [PseudoMetricSpace X] (s : Set X) :
    upperMinkowskiDim (closure s) = upperMinkowskiDim s :=
  le_antisymm (upperMinkowskiDim_closure_le s)
    (upperMinkowskiDim_mono subset_closure)

theorem coveringNumber_union_le_add
    {X : Type*} [PseudoMetricSpace X] (s t : Set X) (r : ℝ) :
    coveringNumber (s ∪ t) r ≤ coveringNumber s r + coveringNumber t r := by
  classical
  unfold coveringNumber
  rw [ENNReal.sInf_add]
  apply le_iInf₂
  rintro a ⟨cs, hcs, rfl⟩
  rw [ENNReal.add_sInf]
  apply le_iInf₂
  rintro b ⟨ct, hct, rfl⟩
  refine le_trans (b := ((cs ∪ ct).card : ENNReal)) (sInf_le ?_) ?_
  · refine ⟨cs ∪ ct, ?_, rfl⟩
    intro x hx
    rcases hx with hx | hx
    · obtain ⟨c, hc⟩ := mem_iUnion.mp (hcs hx)
      obtain ⟨hcfin, hxc⟩ := mem_iUnion.mp hc
      exact mem_iUnion.mpr ⟨c, mem_iUnion.mpr ⟨Finset.mem_union_left ct hcfin, hxc⟩⟩
    · obtain ⟨c, hc⟩ := mem_iUnion.mp (hct hx)
      obtain ⟨hcfin, hxc⟩ := mem_iUnion.mp hc
      exact mem_iUnion.mpr ⟨c, mem_iUnion.mpr ⟨Finset.mem_union_right cs hcfin, hxc⟩⟩
  · exact_mod_cast Finset.card_union_le cs ct

theorem upperMinkowskiDim_union_le_max
    {X : Type*} [PseudoMetricSpace X] (s t : Set X) :
    upperMinkowskiDim (s ∪ t) ≤ max (upperMinkowskiDim s) (upperMinkowskiDim t) := by
  apply le_of_forall_gt
  intro b hb
  have hs : upperMinkowskiDim s < b := (le_max_left _ _).trans_lt hb
  have ht : upperMinkowskiDim t < b := (le_max_right _ _).trans_lt hb
  obtain ⟨ds, hdsb, hds, Cs, hCs, hsBound⟩ :=
    upperMinkowskiDim_lt_extract_power_bound s hs
  obtain ⟨dt, hdtb, hdt, Ct, hCt, htBound⟩ :=
    upperMinkowskiDim_lt_extract_power_bound t ht
  have hdtop : max ds dt ≠ ⊤ := (max_lt (lt_top_iff_ne_top.mpr hds)
    (lt_top_iff_ne_top.mpr hdt)).ne
  have hdim : upperMinkowskiDim (s ∪ t) ≤ max ds dt := by
    unfold upperMinkowskiDim
    apply sInf_le
    refine ⟨hdtop, Cs + Ct, ENNReal.add_ne_top.mpr ⟨hCs, hCt⟩, ?_⟩
    have hsmall : ∀ᶠ r in 𝓝[>] (0 : ℝ), r ≤ 1 :=
      ((eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).mono fun _ h => h.le).filter_mono
        nhdsWithin_le_nhds
    filter_upwards [hsBound, htBound, hsmall] with r hrS hrT hr
    have hbase : ENNReal.ofReal r ≤ 1 := by
      simpa only [← ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hr
    have hsPower : (ENNReal.ofReal r).rpow (-ds.toReal) ≤
        (ENNReal.ofReal r).rpow (-(max ds dt).toReal) :=
      ENNReal.rpow_le_rpow_of_exponent_ge hbase
        (neg_le_neg (ENNReal.toReal_mono hdtop (le_max_left _ _)))
    have htPower : (ENNReal.ofReal r).rpow (-dt.toReal) ≤
        (ENNReal.ofReal r).rpow (-(max ds dt).toReal) :=
      ENNReal.rpow_le_rpow_of_exponent_ge hbase
        (neg_le_neg (ENNReal.toReal_mono hdtop (le_max_right _ _)))
    calc
      coveringNumber (s ∪ t) r ≤ coveringNumber s r + coveringNumber t r :=
        coveringNumber_union_le_add s t r
      _ ≤ Cs * (ENNReal.ofReal r).rpow (-ds.toReal) +
          Ct * (ENNReal.ofReal r).rpow (-dt.toReal) := add_le_add hrS hrT
      _ ≤ Cs * (ENNReal.ofReal r).rpow (-(max ds dt).toReal) +
          Ct * (ENNReal.ofReal r).rpow (-(max ds dt).toReal) := by gcongr
      _ = (Cs + Ct) * (ENNReal.ofReal r).rpow (-(max ds dt).toReal) :=
        (add_mul _ _ _).symm
  exact hdim.trans_lt (max_lt hdsb hdtb)

theorem upperMinkowskiDim_accumulate_le
    {X : Type*} [PseudoMetricSpace X] (F : ℕ → Set X) {a : ENNReal}
    (hF : ∀ n, upperMinkowskiDim (F n) ≤ a) :
    ∀ n, upperMinkowskiDim (Set.accumulate F n) ≤ a := by
  intro n
  induction n with
  | zero => simpa only [Set.accumulate_zero_nat] using hF 0
  | succ n ih =>
    rw [Set.accumulate_succ]
    exact (upperMinkowskiDim_union_le_max _ _).trans (max_le ih (hF (n + 1)))


/-- A countable compact cover of a compact carrier has a finite initial union
whose omission has arbitrarily small mass. The measure need not be regular. -/
theorem compact_countable_cover_extract_small_loss
    {Y : Type*} [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (ν : Measure Y) [IsFiniteMeasure ν] (K : Set Y) (hK : IsCompact K)
    (pieces : ℕ → Set Y) (hcompact : ∀ n, IsCompact (pieces n))
    (hcover : K ⊆ ⋃ n, pieces n) {ε : ENNReal} (hε : 0 < ε) :
    ∃ n : ℕ, ν (K \ Set.accumulate pieces n) < ε := by
  let D : ℕ → Set Y := fun n => K \ Set.accumulate pieces n
  have hD : ∀ n, MeasurableSet (D n) := fun n =>
    hK.isClosed.measurableSet.diff (isCompact_accumulate hcompact n).isClosed.measurableSet
  have hanti : Antitone D := by
    intro m n hmn x hx
    exact ⟨hx.1, fun hm => hx.2 (Set.monotone_accumulate hmn hm)⟩
  have hempty : (⋂ n, D n) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hxK := (Set.mem_iInter.mp hx 0).1
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp (hcover hxK)
    exact (Set.mem_iInter.mp hx n).2 (Set.subset_accumulate hn)
  have hzero : (⨅ n, ν (D n)) = 0 := by
    rw [← hanti.measure_iInter (fun n => (hD n).nullMeasurableSet)
      ⟨0, measure_ne_top ν _⟩, hempty, measure_empty]
  have hlt : (⨅ n, ν (D n)) < ε := hzero ▸ hε
  exact iInf_lt_iff.mp hlt

/-- Countably many hereditary set properties that can each hold on compact
pieces of arbitrarily large mass can hold on one such compact piece. -/
theorem compact_countable_constraints_extract_small_loss
    {Y : Type*} [MetricSpace Y] [MeasurableSpace Y]
    (ν : Measure Y) (K : Set Y) (hK : IsCompact K)
    (P : ℕ → Set Y → Prop)
    (hmono : ∀ n {S T : Set Y}, S ⊆ T → P n T → P n S)
    (happrox : ∀ n {δ : ENNReal}, 0 < δ →
      ∃ S : Set Y, S ⊆ K ∧ IsCompact S ∧ ν (K \ S) < δ ∧ P n S)
    {ε : ENNReal} (hε : 0 < ε) :
    ∃ S : Set Y, S ⊆ K ∧ IsCompact S ∧ ν (K \ S) < ε ∧ ∀ n, P n S := by
  classical
  obtain ⟨δ, hδ, hsum⟩ := ENNReal.exists_pos_sum_of_countable' hε.ne' ℕ
  choose pieces hsub hcompact hloss hP using fun n => happrox n (hδ n)
  let S := ⋂ n, pieces n
  have hSK : S ⊆ K := (Set.iInter_subset pieces 0).trans (hsub 0)
  have hS : IsCompact S := hK.of_isClosed_subset
    (isClosed_iInter fun n => (hcompact n).isClosed) hSK
  refine ⟨S, hSK, hS, ?_, fun n => hmono n (Set.iInter_subset pieces n) (hP n)⟩
  calc
    ν (K \ S) = ν (⋃ n, K \ pieces n) := by simp only [S, Set.sdiff_iInter]
    _ ≤ ∑' n, ν (K \ pieces n) := measure_iUnion_le _
    _ ≤ ∑' n, δ n := ENNReal.tsum_le_tsum fun n => (hloss n).le
    _ < ε := hsum

/-- At every exponent strictly above the packing dimension, one compact
piece retains all but an arbitrarily small amount of the carrier's mass. -/
theorem compact_packingDim_lt_extract_small_loss_piece
    {Y : Type*} [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (ν : Measure Y) [IsFiniteMeasure ν] (K : Set Y) (hK : IsCompact K)
    {b : ENNReal} (hpack : packingDim K < b) {ε : ENNReal} (hε : 0 < ε) :
    ∃ S : Set Y, S ⊆ K ∧ IsCompact S ∧ ν (K \ S) < ε ∧
      upperMinkowskiDim S < b := by
  obtain ⟨a, hab, raw, hcover, hdim⟩ := packingDim_lt_extract_countable_cover K hpack
  let pieces : ℕ → Set Y := fun n => closure (raw n ∩ K)
  have hsub (n : ℕ) : pieces n ⊆ K :=
    closure_minimal Set.inter_subset_right hK.isClosed
  have hcompact (n : ℕ) : IsCompact (pieces n) :=
    hK.of_isClosed_subset isClosed_closure (hsub n)
  have hpiecesDim (n : ℕ) : upperMinkowskiDim (pieces n) ≤ a :=
    (upperMinkowskiDim_closure_le _).trans
      ((upperMinkowskiDim_mono Set.inter_subset_left).trans (hdim n))
  have hpiecesCover : K ⊆ ⋃ n, pieces n := by
    intro x hx
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp (hcover hx)
    exact Set.mem_iUnion.mpr ⟨n, subset_closure ⟨hn, hx⟩⟩
  obtain ⟨n, hloss⟩ := compact_countable_cover_extract_small_loss
    ν K hK pieces hcompact hpiecesCover hε
  refine ⟨Set.accumulate pieces n, ?_, isCompact_accumulate hcompact n, hloss, ?_⟩
  · rintro x hx
    obtain ⟨j, _, hj⟩ := Set.mem_accumulate.mp hx
    exact hsub j hj
  · exact (upperMinkowskiDim_accumulate_le pieces hpiecesDim n).trans_lt hab

/-- A compact packing-dimension-at-most-three carrier has one compact piece
of arbitrarily large mass whose upper Minkowski dimension is at most three.
The piece is chosen once, before any positive exponent slack is requested. -/
theorem compact_packingDim_le_three_extract_exact_piece
    {Y : Type*} [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (ν : Measure Y) [IsFiniteMeasure ν] (K : Set Y) (hK : IsCompact K)
    (hpack : packingDim K ≤ 3) {ε : ENNReal} (hε : 0 < ε) :
    ∃ S : Set Y, S ⊆ K ∧ IsCompact S ∧ ν (K \ S) < ε ∧
      upperMinkowskiDim S ≤ 3 := by
  let a : ℕ → ENNReal := fun n => 3 + (1 / 2 : ENNReal) ^ n
  have hpacklt (n : ℕ) : packingDim K < a n := by
    apply hpack.trans_lt
    exact ENNReal.lt_add_right (by norm_num) (pow_ne_zero _ (by norm_num))
  obtain ⟨S, hSK, hS, hloss, hdim⟩ :=
    compact_countable_constraints_extract_small_loss ν K hK
      (fun n S => upperMinkowskiDim S < a n)
      (fun n _ _ hsub hdim => (upperMinkowskiDim_mono hsub).trans_lt hdim)
      (fun n _ hδ => compact_packingDim_lt_extract_small_loss_piece ν K hK (hpacklt n) hδ)
      hε
  refine ⟨S, hSK, hS, hloss, ?_⟩
  have hlim : Tendsto a atTop (𝓝 (3 : ENNReal)) := by
    simpa only [a, add_zero] using
      (tendsto_const_nhds.add
        (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one
          (show (1 / 2 : ENNReal) < 1 by norm_num)))
  exact ge_of_tendsto' hlim fun n => (hdim n).le

/-- In particular the exact upper-Minkowski piece can retain positive mass. -/
theorem compact_packingDim_le_three_extract_positive_exact_piece
    {Y : Type*} [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (ν : Measure Y) [IsFiniteMeasure ν] (K : Set Y) (hK : IsCompact K)
    (hmass : 0 < ν K) (hpack : packingDim K ≤ 3) :
    ∃ S : Set Y, S ⊆ K ∧ IsCompact S ∧ 0 < ν S ∧ upperMinkowskiDim S ≤ 3 := by
  obtain ⟨S, hSK, hS, hloss, hdim⟩ :=
    compact_packingDim_le_three_extract_exact_piece ν K hK hpack
      (ENNReal.half_pos hmass.ne')
  refine ⟨S, hSK, hS, pos_iff_ne_zero.mpr ?_, hdim⟩
  intro hz
  rw [measure_sdiff_null hz] at hloss
  exact (not_lt_of_ge ENNReal.half_le_self) hloss

/-- The exact compact piece retains arbitrarily prescribed source mass for
a measurable map supported almost everywhere on the compact carrier. -/
theorem packing_carrier_extract_exact_small_loss_piece
    {X Y : Type*} [MeasurableSpace X] [MetricSpace Y]
    [MeasurableSpace Y] [BorelSpace Y]
    (μ : Measure X) [IsFiniteMeasure μ]
    (f : X → Y) (hf : Measurable f)
    (K : Set Y) (hK : IsCompact K)
    (hsupport : μ (f ⁻¹' K)ᶜ = 0) (hpack : packingDim K ≤ 3)
    {ε : ENNReal} (hε : 0 < ε) :
    ∃ S : Set Y, S ⊆ K ∧ IsCompact S ∧
      μ (f ⁻¹' S)ᶜ < ε ∧ upperMinkowskiDim S ≤ 3 := by
  obtain ⟨S, hSK, hS, hloss, hdim⟩ :=
    compact_packingDim_le_three_extract_exact_piece (Measure.map f μ) K hK hpack hε
  have hmeas : MeasurableSet (K \ S) :=
    hK.isClosed.measurableSet.diff hS.isClosed.measurableSet
  rw [Measure.map_apply hf hmeas] at hloss
  have hsplit : (f ⁻¹' S)ᶜ = f ⁻¹' (K \ S) ∪ (f ⁻¹' K)ᶜ := by
    ext x
    simp only [Set.mem_compl_iff, Set.mem_preimage, Set.mem_union, Set.mem_sdiff]
    constructor
    · intro hx
      by_cases hxK : f x ∈ K
      · exact Or.inl ⟨hxK, hx⟩
      · exact Or.inr hxK
    · rintro (⟨_, hx⟩ | hx)
      · exact hx
      · exact fun hxS => hx (hSK hxS)
  refine ⟨S, hSK, hS, ?_, hdim⟩
  calc
    μ (f ⁻¹' S)ᶜ = μ (f ⁻¹' (K \ S) ∪ (f ⁻¹' K)ᶜ) := by rw [hsplit]
    _ ≤ μ (f ⁻¹' (K \ S)) + μ (f ⁻¹' K)ᶜ := measure_union_le _ _
    _ = μ (f ⁻¹' (K \ S)) := by rw [hsupport, add_zero]
    _ < ε := hloss

/-- The retained compact source can carry any requested fraction strictly
below the original total mass. This is the same single exact-dimension piece. -/
theorem packing_carrier_extract_exact_fraction_piece
    {X Y : Type*} [MeasurableSpace X] [MetricSpace Y]
    [MeasurableSpace Y] [BorelSpace Y]
    (μ : Measure X) [IsFiniteMeasure μ]
    (f : X → Y) (hf : Measurable f)
    (K : Set Y) (hK : IsCompact K)
    (hsupport : μ (f ⁻¹' K)ᶜ = 0) (hpack : packingDim K ≤ 3)
    (M : ENNReal) (hM : M < μ Set.univ) :
    ∃ S : Set Y, S ⊆ K ∧ IsCompact S ∧
      M < μ (f ⁻¹' S) ∧ upperMinkowskiDim S ≤ 3 := by
  obtain ⟨S, hSK, hS, hloss, hdim⟩ :=
    packing_carrier_extract_exact_small_loss_piece μ f hf K hK hsupport hpack
      (tsub_pos_of_lt hM)
  refine ⟨S, hSK, hS, ?_, hdim⟩
  rw [measure_compl ((hS.isClosed.measurableSet).preimage hf)
    (measure_ne_top μ _)] at hloss
  by_contra hle
  have hm : μ (f ⁻¹' S) ≤ M := le_of_not_gt hle
  exact (not_lt_of_ge (tsub_le_tsub_left hm _)) hloss

end StickyKakeya4
