import Definitions.Def_sticky_kakeya4_core

open Filter MeasureTheory Set

namespace StickyKakeya4

theorem coveringNumber_mono
    {X : Type*} [PseudoMetricSpace X] {s t : Set X} (hst : s ⊆ t) (r : ℝ) :
    coveringNumber s r ≤ coveringNumber t r := by
  rw [coveringNumber, coveringNumber]
  apply sInf_le_sInf
  rintro n ⟨centers, hcover, hn⟩
  exact ⟨centers, fun x hx ↦ hcover (hst hx), hn⟩

/-- Any explicit finite radius-`r` cover gives the corresponding upper bound
for the infimum defining `coveringNumber`. -/
theorem coveringNumber_le_card_of_coversAtRadius
    {X : Type*} [PseudoMetricSpace X] (s : Set X) (r : ℝ)
    (centers : Finset X) (hcover : coversAtRadius s r centers) :
    coveringNumber s r ≤ (centers.card : ENNReal) := by
  rw [coveringNumber]
  apply sInf_le
  exact ⟨centers, hcover, rfl⟩

/-- A strict upper bound for `coveringNumber` produces an actual finite cover
whose cardinality obeys the same strict bound.  The strict inequality is the
correct way to extract a witness from the infimum definition. -/
theorem coveringNumber_lt_extract_finset_cover
    {X : Type*} [PseudoMetricSpace X] (s : Set X) (r : ℝ) {B : ENNReal}
    (h : coveringNumber s r < B) :
    ∃ centers : Finset X,
      coversAtRadius s r centers ∧ (centers.card : ENNReal) < B := by
  rw [coveringNumber, sInf_lt_iff] at h
  obtain ⟨n, ⟨centers, hcover, hn⟩, hnB⟩ := h
  subst n
  exact ⟨centers, hcover, hnB⟩

/-- A finite non-strict covering-number bound still gives an actual finite
cover after adding one harmless cardinal unit.  This is the form needed when
an upper Minkowski estimate is supplied as `coveringNumber s r ≤ B`: the
infimum need not be unpacked at the endpoint `B`, but it can always be
unpacked strictly below `B + 1`. -/
theorem coveringNumber_le_extract_finset_cover
    {X : Type*} [PseudoMetricSpace X] (s : Set X) (r : ℝ) {B : ENNReal}
    (hB : B ≠ ⊤) (h : coveringNumber s r ≤ B) :
    ∃ centers : Finset X,
      coversAtRadius s r centers ∧ (centers.card : ENNReal) < B + 1 := by
  apply coveringNumber_lt_extract_finset_cover s r
  exact h.trans_lt (ENNReal.lt_add_right hB (by norm_num))

/-- An eventual power upper bound for a covering number can be read back as
actual finite metric covers at the same radii.  The added cardinal unit is
uniform and is the only loss incurred when extracting witnesses from the
infimum defining `coveringNumber`. -/
theorem eventual_power_cover_bound_extract_finset_covers
    {X : Type*} [PseudoMetricSpace X] (s : Set X)
    {C : ENNReal} (hC : C ≠ ⊤) (d : ℝ)
    (hbound : ∀ᶠ r in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      coveringNumber s r ≤ C * (ENNReal.ofReal r).rpow d) :
    ∀ᶠ r in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      ∃ centers : Finset X,
        coversAtRadius s r centers ∧
          (centers.card : ENNReal) <
            C * (ENNReal.ofReal r).rpow d + 1 := by
  filter_upwards [hbound, self_mem_nhdsWithin] with r hr hrpos
  have hbaseZero : ENNReal.ofReal r ≠ 0 :=
    (ENNReal.ofReal_pos.mpr hrpos).ne'
  have hpowerTop : (ENNReal.ofReal r).rpow d ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_ne_zero hbaseZero ENNReal.ofReal_ne_top
  exact coveringNumber_le_extract_finset_cover s r
    (ENNReal.mul_ne_top hC hpowerTop) hr

/-- Enlarging the covering radius cannot increase the covering number. -/
theorem coveringNumber_anti_radius
    {X : Type*} [PseudoMetricSpace X] (s : Set X) {r R : ℝ} (h : r ≤ R) :
    coveringNumber s R ≤ coveringNumber s r := by
  rw [coveringNumber, coveringNumber]
  apply sInf_le_sInf
  rintro n ⟨centers, hcover, hn⟩
  refine ⟨centers, ?_, hn⟩
  intro x hx
  obtain ⟨c, hc⟩ := Set.mem_iUnion.mp (hcover hx)
  obtain ⟨hcfin, hxc⟩ := Set.mem_iUnion.mp hc
  apply Set.mem_iUnion.mpr
  refine ⟨c, Set.mem_iUnion.mpr ⟨hcfin, ?_⟩⟩
  exact Metric.ball_subset_ball h hxc

theorem coversAtRadius_closure
    {X : Type*} [PseudoMetricSpace X] {s : Set X} {r : ℝ}
    (hr : 0 < r) (centers : Finset X)
    (hcover : coversAtRadius s (r / 2) centers) :
    coversAtRadius (closure s) r centers := by
  intro y hy
  obtain ⟨x, hxs, hyx⟩ :=
    Metric.mem_closure_iff.mp hy (r / 2) (by linarith)
  obtain ⟨c, hc⟩ := Set.mem_iUnion.mp (hcover hxs)
  obtain ⟨hcfin, hxc⟩ := Set.mem_iUnion.mp hc
  apply Set.mem_iUnion.mpr
  refine ⟨c, Set.mem_iUnion.mpr ⟨hcfin, ?_⟩⟩
  rw [Metric.mem_ball]
  calc
    dist y c ≤ dist y x + dist x c := dist_triangle y x c
    _ < r / 2 + r / 2 := add_lt_add hyx (by simpa [Metric.mem_ball] using hxc)
    _ = r := by ring

theorem coveringNumber_closure_le
    {X : Type*} [PseudoMetricSpace X] (s : Set X) {r : ℝ} (hr : 0 < r) :
    coveringNumber (closure s) r ≤ coveringNumber s (r / 2) := by
  rw [coveringNumber, coveringNumber]
  apply sInf_le_sInf
  rintro n ⟨centers, hcover, hn⟩
  exact ⟨centers, coversAtRadius_closure hr centers hcover, hn⟩

/-- An eventual assertion at positive radii can be made uniform on one
punctured interval `(0, δ₀]`. -/
theorem eventually_nhdsGT_extract_cutoff {P : ℝ → Prop}
    (hP : ∀ᶠ r in nhdsWithin (0 : ℝ) (Set.Ioi 0), P r) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ r : ℝ, 0 < r → r ≤ δ₀ → P r := by
  obtain ⟨δ₀, hδ₀, hsub⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp hP
  exact ⟨δ₀, hδ₀, fun r hr hrδ₀ ↦ hsub ⟨hr, hrδ₀⟩⟩

/-- An eventual power covering estimate can be extended to every radius in
`(0, 1]` by enlarging its finite coefficient once.  At radii above the
eventual cutoff, monotonicity charges the single cutoff covering number; the
nonpositive power is at least one on the unit interval. -/
theorem eventual_covering_bound_extend_to_unit_interval
    {X : Type*} [PseudoMetricSpace X] (s : Set X)
    {C d : ENNReal} (hCtop : C ≠ ⊤)
    (hbound : ∀ᶠ r in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      coveringNumber s r ≤
        C * (ENNReal.ofReal (r / 2)).rpow (-d.toReal)) :
    ∃ cutoff : ℝ, 0 < cutoff ∧ cutoff ≤ 1 ∧
      ∃ CAll : ENNReal, CAll ≠ ⊤ ∧ C ≤ CAll ∧
        ∀ r : ℝ, 0 < r → r ≤ 1 →
          coveringNumber s r ≤
            CAll * (ENNReal.ofReal (r / 2)).rpow (-d.toReal) := by
  obtain ⟨rawCutoff, hrawCutoff, hsmall⟩ :=
    eventually_nhdsGT_extract_cutoff hbound
  let cutoff : ℝ := min rawCutoff 1
  have hcutoff : 0 < cutoff := by
    dsimp [cutoff]
    exact lt_min hrawCutoff (by norm_num)
  have hcutoffOne : cutoff ≤ 1 := by
    exact min_le_right _ _
  have hcutoffRaw : cutoff ≤ rawCutoff := by
    exact min_le_left _ _
  have hcutoffBound : coveringNumber s cutoff ≤
      C * (ENNReal.ofReal (cutoff / 2)).rpow (-d.toReal) :=
    hsmall cutoff hcutoff hcutoffRaw
  have hcutoffCoverTop : coveringNumber s cutoff ≠ ⊤ := by
    apply ne_top_of_le_ne_top _ hcutoffBound
    exact ENNReal.mul_ne_top hCtop
      (ENNReal.rpow_ne_top_of_ne_zero
        (ENNReal.ofReal_ne_zero_iff.mpr (by positivity))
        ENNReal.ofReal_ne_top)
  let CAll : ENNReal := max C (coveringNumber s cutoff)
  have hCAllTop : CAll ≠ ⊤ := by
    dsimp [CAll]
    exact max_lt (lt_top_iff_ne_top.mpr hCtop)
      (lt_top_iff_ne_top.mpr hcutoffCoverTop) |>.ne
  refine ⟨cutoff, hcutoff, hcutoffOne, CAll, hCAllTop,
    le_max_left _ _, ?_⟩
  intro r hr hrOne
  rcases le_total r cutoff with hrCutoff | hcutoffR
  · calc
      coveringNumber s r ≤
          C * (ENNReal.ofReal (r / 2)).rpow (-d.toReal) :=
        hsmall r hr (hrCutoff.trans hcutoffRaw)
      _ ≤ CAll * (ENNReal.ofReal (r / 2)).rpow (-d.toReal) := by
        gcongr
        exact le_max_left _ _
  · have hbasePos : 0 < ENNReal.ofReal (r / 2) :=
      ENNReal.ofReal_pos.mpr (by positivity)
    have hbaseOne : ENNReal.ofReal (r / 2) ≤ 1 := by
      rw [← ENNReal.ofReal_one]
      apply ENNReal.ofReal_le_ofReal
      linarith
    have hpowOne : (1 : ENNReal) ≤
        (ENNReal.ofReal (r / 2)).rpow (-d.toReal) :=
      by
        by_cases hd0 : d = 0
        · simp [hd0]
        by_cases hdtop : d = ⊤
        · simp [hdtop]
        exact ENNReal.one_le_rpow_of_pos_of_le_one_of_neg
          hbasePos hbaseOne (by linarith [ENNReal.toReal_pos hd0 hdtop])
    calc
      coveringNumber s r ≤ coveringNumber s cutoff :=
        coveringNumber_anti_radius s hcutoffR
      _ ≤ CAll := le_max_right _ _
      _ = CAll * 1 := (mul_one CAll).symm
      _ ≤ CAll * (ENNReal.ofReal (r / 2)).rpow (-d.toReal) :=
        mul_le_mul_right hpowOne CAll

/-!
`packingDim` and `upperMinkowskiDim` are defined as infima.  The two lemmas
below record the logically valid way to unpack those infima: one first moves
to a strictly larger exponent and only then obtains an actual witness.  This
prevents the endpoint value of an infimum from being used as though it were
automatically attained.
-/

theorem packingDim_lt_extract_countable_cover
    {X : Type*} [PseudoMetricSpace X] (s : Set X) {b : ENNReal}
    (h : packingDim s < b) :
    ∃ d : ENNReal, d < b ∧
      ∃ pieces : ℕ → Set X,
        s ⊆ ⋃ n, pieces n ∧
        ∀ n, upperMinkowskiDim (pieces n) ≤ d := by
  rw [packingDim, sInf_lt_iff] at h
  rcases h with ⟨d, hd, hdb⟩
  exact ⟨d, hdb, hd⟩

theorem packingDim_eq_three_extract_countable_cover
    {X : Type*} [PseudoMetricSpace X] (s : Set X)
    (hpacking : packingDim s = 3) {slack : ENNReal} (hslack : 0 < slack) :
    ∃ d : ENNReal, d < 3 + slack ∧
      ∃ pieces : ℕ → Set X,
        s ⊆ ⋃ n, pieces n ∧
        ∀ n, upperMinkowskiDim (pieces n) ≤ d := by
  apply packingDim_lt_extract_countable_cover s
  rw [hpacking]
  exact ENNReal.lt_add_right (by norm_num) (ne_of_gt hslack)

theorem upperMinkowskiDim_lt_extract_power_bound
    {X : Type*} [PseudoMetricSpace X] (s : Set X) {b : ENNReal}
    (h : upperMinkowskiDim s < b) :
    ∃ d : ENNReal, d < b ∧ d ≠ ⊤ ∧
      ∃ C : ENNReal, C ≠ ⊤ ∧
        ∀ᶠ r in nhdsWithin (0 : ℝ) (Set.Ioi 0),
          coveringNumber s r ≤
            C * (ENNReal.ofReal r).rpow (-d.toReal) := by
  rw [upperMinkowskiDim, sInf_lt_iff] at h
  rcases h with ⟨d, hd, hdb⟩
  exact ⟨d, hdb, hd⟩

/-- A packing-dimension-three carrier admits a countable cover whose every
piece comes with an honest small-scale covering estimate at an exponent
strictly below `3 + slack`.  The exponent and constant may depend on the
piece; no endpoint attainment is asserted. -/
theorem packingDim_eq_three_extract_power_cover
    {X : Type*} [PseudoMetricSpace X] (s : Set X)
    (hpacking : packingDim s = 3) {slack : ENNReal} (hslack : 0 < slack) :
    ∃ pieces : ℕ → Set X,
      s ⊆ ⋃ n, pieces n ∧
      ∀ n, ∃ d : ENNReal, d < 3 + slack ∧ d ≠ ⊤ ∧
        ∃ C : ENNReal, C ≠ ⊤ ∧
          ∀ᶠ r in nhdsWithin (0 : ℝ) (Set.Ioi 0),
            coveringNumber (pieces n) r ≤
              C * (ENNReal.ofReal r).rpow (-d.toReal) := by
  obtain ⟨d, hd, pieces, hcover, hdim⟩ :=
    packingDim_eq_three_extract_countable_cover s hpacking hslack
  refine ⟨pieces, hcover, ?_⟩
  intro n
  apply upperMinkowskiDim_lt_extract_power_bound (pieces n)
  exact lt_of_le_of_lt (hdim n) hd

/-- A countable cover of a set of nonzero mass has a member of nonzero mass.
No measurability of the covering pieces is needed for this null-set argument. -/
theorem exists_nonzero_measure_piece_of_countable_cover
    {X : Type*} [MeasurableSpace X] (mu : Measure X)
    {s : Set X} {pieces : ℕ → Set X}
    (hcover : s ⊆ ⋃ n, pieces n) (hs : mu s ≠ 0) :
    ∃ n, mu (pieces n) ≠ 0 := by
  by_contra h
  push_neg at h
  have hunion : mu (⋃ n, pieces n) = 0 := measure_iUnion_null h
  exact hs (measure_mono_null hcover hunion)

/-- Combining the packing witness with the null-set argument produces one
positive-mass carrier piece carrying an actual finite-scale power bound. -/
theorem packingDim_eq_three_extract_nonzero_measure_power_piece
    {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    (mu : Measure X) (s : Set X)
    (hpacking : packingDim s = 3) (hs : mu s ≠ 0)
    {slack : ENNReal} (hslack : 0 < slack) :
    ∃ piece : Set X, mu piece ≠ 0 ∧
      ∃ d : ENNReal, d < 3 + slack ∧ d ≠ ⊤ ∧
        ∃ C : ENNReal, C ≠ ⊤ ∧
          ∀ᶠ r in nhdsWithin (0 : ℝ) (Set.Ioi 0),
            coveringNumber piece r ≤
              C * (ENNReal.ofReal r).rpow (-d.toReal) := by
  obtain ⟨pieces, hcover, hpower⟩ :=
    packingDim_eq_three_extract_power_cover s hpacking hslack
  obtain ⟨n, hn⟩ :=
    exists_nonzero_measure_piece_of_countable_cover mu hcover hs
  exact ⟨pieces n, hn, hpower n⟩

end StickyKakeya4
