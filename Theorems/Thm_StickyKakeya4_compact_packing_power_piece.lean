import Theorems.Thm_StickyKakeya4_dimension_witness_extraction

open Filter MeasureTheory Set

namespace StickyKakeya4

/-- A compact set of positive mass and packing dimension strictly below `b`
contains a compact positive-mass piece with an actual eventual covering bound
at an exponent strictly below `b`.

The raw countable packing pieces need not be measurable. Intersecting them
with `S` before the null-set argument ensures that the positive piece lies
in `S`; taking its closure then preserves both positive mass and containment
in the compact carrier. The radius loss makes the closure covering estimate
valid without assuming closedness of the raw packing pieces. -/
theorem compact_packingDim_lt_extract_eventual_power_piece
    {Y : Type*} [MetricSpace Y] [MeasurableSpace Y]
    (ν : Measure Y) (S : Set Y) (hS : IsCompact S) (hνS : 0 < ν S)
    {b : ENNReal} (hpack : packingDim S < b) :
    ∃ K : Set Y, K ⊆ S ∧ IsCompact K ∧ 0 < ν K ∧
      ∃ d : ENNReal, d < b ∧ d ≠ ⊤ ∧
        ∃ C : ENNReal, C ≠ ⊤ ∧
          ∀ᶠ r in nhdsWithin (0 : ℝ) (Set.Ioi 0),
            coveringNumber K r ≤
              C * (ENNReal.ofReal (r / 2)).rpow (-d.toReal) := by
  obtain ⟨a, hab, pieces, hcover, hdim⟩ :=
    packingDim_lt_extract_countable_cover S hpack
  have hinterCover : S ⊆ ⋃ n, pieces n ∩ S := by
    intro x hx
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp (hcover hx)
    exact Set.mem_iUnion.mpr ⟨n, hn, hx⟩
  obtain ⟨n, hn⟩ :=
    exists_nonzero_measure_piece_of_countable_cover ν hinterCover hνS.ne'
  obtain ⟨d, hdb, hdtop, C, hCtop, hbound⟩ :=
    upperMinkowskiDim_lt_extract_power_bound (pieces n) ((hdim n).trans_lt hab)
  have hclosureSub : closure (pieces n ∩ S) ⊆ S :=
    closure_minimal Set.inter_subset_right hS.isClosed
  have hclosureCompact : IsCompact (closure (pieces n ∩ S)) :=
    hS.of_isClosed_subset isClosed_closure hclosureSub
  have hclosurePos : 0 < ν (closure (pieces n ∩ S)) :=
    (pos_iff_ne_zero.mpr hn).trans_le (measure_mono subset_closure)
  refine ⟨closure (pieces n ∩ S), hclosureSub, hclosureCompact,
    hclosurePos, d, hdb, hdtop, C, hCtop, ?_⟩
  obtain ⟨δ₀, hδ₀, hsmall⟩ := eventually_nhdsGT_extract_cutoff hbound
  apply mem_nhdsGT_iff_exists_Ioc_subset.mpr
  refine ⟨2 * δ₀, ?_, ?_⟩
  · change (0 : ℝ) < 2 * δ₀
    positivity
  · intro r hr
    calc
      coveringNumber (closure (pieces n ∩ S)) r ≤
          coveringNumber (pieces n ∩ S) (r / 2) :=
        coveringNumber_closure_le _ hr.1
      _ ≤ coveringNumber (pieces n) (r / 2) :=
        coveringNumber_mono Set.inter_subset_left _
      _ ≤ C * (ENNReal.ofReal (r / 2)).rpow (-d.toReal) :=
        hsmall (r / 2) (by linarith [hr.1]) (by linarith [hr.2])

/-- The compact positive-mass packing piece has a single finite power-cover
constant valid at every positive radius at most one, not merely eventually.
Neither finiteness of the measure nor measurability of the raw packing pieces
is needed. -/
theorem compact_packingDim_lt_extract_power_piece
    {Y : Type*} [MetricSpace Y] [MeasurableSpace Y]
    (ν : Measure Y) (S : Set Y) (hS : IsCompact S) (hνS : 0 < ν S)
    {b : ENNReal} (hpack : packingDim S < b) :
    ∃ K : Set Y, K ⊆ S ∧ IsCompact K ∧ 0 < ν K ∧
      ∃ d : ENNReal, d < b ∧ d ≠ ⊤ ∧
        ∃ C : ENNReal, C ≠ ⊤ ∧
          ∀ r : ℝ, 0 < r → r ≤ 1 →
            coveringNumber K r ≤
              C * (ENNReal.ofReal (r / 2)).rpow (-d.toReal) := by
  obtain ⟨K, hKS, hK, hνK, d, hdb, hdtop, C, hCtop, hbound⟩ :=
    compact_packingDim_lt_extract_eventual_power_piece ν S hS hνS hpack
  obtain ⟨_, _, _, CAll, hCAllTop, _, hboundAll⟩ :=
    eventual_covering_bound_extend_to_unit_interval K hCtop hbound
  exact ⟨K, hKS, hK, hνK, d, hdb, hdtop, CAll, hCAllTop, hboundAll⟩

/-- In particular, a compact positive-mass carrier of packing dimension at
most three contains a compact positive-mass piece with a uniform actual
power-cover bound below `3 + slack`, for every positive slack. -/
theorem compact_packingDim_le_three_extract_power_piece
    {Y : Type*} [MetricSpace Y] [MeasurableSpace Y]
    (ν : Measure Y) (S : Set Y) (hS : IsCompact S) (hνS : 0 < ν S)
    (hpack : packingDim S ≤ 3) {slack : ENNReal} (hslack : 0 < slack) :
    ∃ K : Set Y, K ⊆ S ∧ IsCompact K ∧ 0 < ν K ∧
      ∃ d : ENNReal, d < 3 + slack ∧ d ≠ ⊤ ∧
        ∃ C : ENNReal, C ≠ ⊤ ∧
          ∀ r : ℝ, 0 < r → r ≤ 1 →
            coveringNumber K r ≤
              C * (ENNReal.ofReal (r / 2)).rpow (-d.toReal) := by
  apply compact_packingDim_lt_extract_power_piece ν S hS hνS
  exact hpack.trans_lt (ENNReal.lt_add_right (by norm_num) hslack.ne')

end StickyKakeya4
