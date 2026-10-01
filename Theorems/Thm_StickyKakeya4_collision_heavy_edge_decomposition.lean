import Theorems.Thm_StickyKakeya4_collision_support_cardinality
import Theorems.Thm_StickyKakeya4_raw_collision_support

open MeasureTheory Set

noncomputable section

namespace StickyKakeya4

/-- A single normalized collision edge never carries more mass than its
complete source row.  This follows from the exact Markov row identity and
does not require estimating the quotient in the definition edge by edge. -/
theorem sourceNormalizedCollisionFlow_le_sourceRowMass_of_row_finite
    {n : ℕ} (R : FiniteScaleSource n) (i j : Fin n)
    (hrowTop : sourceOffDiagonalRowMass R i ≠ ⊤) :
    sourceNormalizedCollisionFlow R i j ≤ sourceRowMass R i := by
  classical
  by_cases hrow0 : sourceOffDiagonalRowMass R i = 0
  · simp [sourceNormalizedCollisionFlow, hrow0]
  · calc
      sourceNormalizedCollisionFlow R i j ≤
          ∑ k, sourceNormalizedCollisionFlow R i k := by
        exact Finset.single_le_sum (fun k _ ↦ bot_le) (Finset.mem_univ j)
      _ = sourceRowMass R i :=
        sourceNormalizedCollisionFlow_row_sum R i hrow0 hrowTop

/-- The geometric capacity of one collision edge at the source thickness.
The constant is the explicit four-dimensional marked-tube volume constant. -/
noncomputable def sourceGeometricEdgeCapacity {n : ℕ}
    (D : FiniteScaleSource n) : ENNReal :=
  32 * (ENNReal.ofReal D.thickness) ^ 3 *
    ENNReal.ofReal (Real.pi ^ 2 / 2)

/-- Indices whose retained shading is active at a physical point.  Zero
weights are excluded, so membership records an actual source occurrence. -/
noncomputable def sourceActiveIndicesAtPoint {n : ℕ}
    (R : FiniteScaleSource n) (x : E4) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun i ↦ x ∈ R.shading i ∧ R.weight i ≠ 0

/-- Exact pointwise readback of the source function on its genuinely active
rows.  This keeps the original weights: zero rows are deleted, but no
cardinality replacement or normalization is made. -/
theorem sourceFunction_eq_sum_activeWeights
    {n : ℕ} (R : FiniteScaleSource n) (x : E4) :
    sourceFunction R x =
      ∑ i ∈ sourceActiveIndicesAtPoint R x, R.weight i := by
  classical
  unfold sourceFunction sourceActiveIndicesAtPoint
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hshade : x ∈ R.shading i
  · by_cases hzero : R.weight i = 0
    · simp [hshade, hzero]
    · simp [hshade, hzero]
  · simp [hshade]

/-- Pointwise weighted multiplicity is at most the number of genuinely active
rows when every source weight is at most one. -/
theorem sourceFunction_le_activeIndicesAtPoint_card
    {n : ℕ} (R : FiniteScaleSource n)
    (hweight : ∀ i, R.weight i ≤ 1) (x : E4) :
    sourceFunction R x ≤
      ((sourceActiveIndicesAtPoint R x).card : ENNReal) := by
  classical
  rw [sourceFunction_eq_sum_activeWeights]
  calc
    (∑ i ∈ sourceActiveIndicesAtPoint R x, R.weight i) ≤
        ∑ _i ∈ sourceActiveIndicesAtPoint R x, (1 : ENNReal) := by
      exact Finset.sum_le_sum fun i _hi ↦ hweight i
    _ = ((sourceActiveIndicesAtPoint R x).card : ENNReal) := by simp

/-- A scaled union failure has a point whose actual weighted multiplicity is
strictly larger than the gain.  This is the weighted form of the common-point
extraction: no replacement by the number of occupied rows is made. -/
theorem scaled_union_failure_has_pointwise_multiplicity_gt_gain
    {n : ℕ} {R D : FiniteScaleSource n} {epsilon : ℝ}
    {C gain : ENNReal}
    (hD : IsAdmissibleStickySource D epsilon C)
    (hR : IsFractionalSourceRestriction R D)
    (hmass0 : sourceMass R ≠ 0)
    (hgainTop : gain ≠ ⊤)
    (hfailure : (gain + 1) * volume (sourceUnion R) ≤ sourceMass R) :
    ∃ x : E4, x ∈ sourceUnion R ∧ gain < sourceFunction R x := by
  have hunionTop : volume (sourceUnion R) ≠ ⊤ :=
    volume_sourceUnion_ne_top_of_fractional_admissibleStickySource hD hR
  have hholder := sourceMass_le_sqrt_energy_mul_sqrt_union R hR.2.2.2.2.1
  have hunion0 : volume (sourceUnion R) ≠ 0 := by
    intro hzero
    rw [hzero] at hholder
    simp at hholder
    exact hmass0 hholder
  by_contra hpoint
  push Not at hpoint
  have hpointwise : ∀ x : E4, sourceFunction R x ≤ gain := by
    intro x
    by_cases hx : x ∈ sourceUnion R
    · exact hpoint x hx
    · have hzero : sourceFunction R x = 0 := by
        apply le_antisymm
        · exact not_lt.mp (by simpa [sourceUnion] using hx)
        · exact bot_le
      simp [hzero]
  have hmassUpper : sourceMass R ≤
      gain * volume (sourceUnion R) := by
    have hU : MeasurableSet (sourceUnion R) :=
      sourceUnion_measurable R hR.2.2.2.2.1
    have hdom : ∀ x : E4, sourceFunction R x ≤
        (sourceUnion R).indicator (fun _ ↦ gain) x := by
      intro x
      by_cases hx : x ∈ sourceUnion R
      · simpa [hx] using hpointwise x
      · have hzero : sourceFunction R x = 0 := by
          apply le_antisymm
          · exact not_lt.mp (by simpa [sourceUnion] using hx)
          · exact bot_le
        simp [hx, hzero]
    calc
      sourceMass R ≤
          ∫⁻ x, (sourceUnion R).indicator
            (fun _ ↦ gain) x ∂volume := lintegral_mono hdom
      _ = gain * volume (sourceUnion R) := by
        simpa [mul_comm] using
          (MeasureTheory.lintegral_indicator_const
            (μ := volume) hU gain)
  have hcancel : gain + 1 ≤ gain := by
    apply (ENNReal.mul_le_mul_iff_right hunion0 hunionTop).mp
    calc
      volume (sourceUnion R) * (gain + 1) =
          (gain + 1) * volume (sourceUnion R) := mul_comm _ _
      _ ≤ sourceMass R := hfailure
      _ ≤ gain * volume (sourceUnion R) := hmassUpper
      _ = volume (sourceUnion R) * gain := mul_comm _ _
  exact (not_le_of_gt (ENNReal.lt_add_right hgainTop (by norm_num))) hcancel

/-- Once the union deficit exceeds three, four distinct positive-weight
source rows meet at one physical point.  This is stronger than extracting a
four-cycle from the pair-support graph: the six pairwise collision edges are
all witnessed by the same point, so arbitrarily small weights cannot inflate
the ambient vertex population and obstruct DRC. -/
theorem scaled_union_failure_has_fourfold_common_overlap
    {n : ℕ} {R D : FiniteScaleSource n} {epsilon : ℝ}
    {C gain : ENNReal}
    (hD : IsAdmissibleStickySource D epsilon C)
    (hR : IsFractionalSourceRestriction R D)
    (hmass0 : sourceMass R ≠ 0)
    (hgain : (3 : ENNReal) < gain + 1)
    (hfailure : (gain + 1) * volume (sourceUnion R) ≤ sourceMass R) :
    ∃ x : E4, 4 ≤ (sourceActiveIndicesAtPoint R x).card := by
  classical
  have hweight : ∀ i, R.weight i ≤ 1 := fun i ↦
    (hR.2.2.2.2.2.2 i).trans (hD.2.2.1 i)
  have hunionTop : volume (sourceUnion R) ≠ ⊤ :=
    volume_sourceUnion_ne_top_of_fractional_admissibleStickySource hD hR
  have hholder := sourceMass_le_sqrt_energy_mul_sqrt_union R hR.2.2.2.2.1
  have hunion0 : volume (sourceUnion R) ≠ 0 := by
    intro hzero
    rw [hzero] at hholder
    simp at hholder
    exact hmass0 hholder
  by_contra hfour
  push Not at hfour
  have hpoint : ∀ x : E4, sourceFunction R x ≤ (3 : ENNReal) := by
    intro x
    have hcardNat : (sourceActiveIndicesAtPoint R x).card ≤ 3 := by
      have hx := hfour x
      omega
    calc
      sourceFunction R x ≤
          ((sourceActiveIndicesAtPoint R x).card : ENNReal) :=
        sourceFunction_le_activeIndicesAtPoint_card R hweight x
      _ ≤ (3 : ENNReal) := by exact_mod_cast hcardNat
  have hmassUpper : sourceMass R ≤
      3 * volume (sourceUnion R) := by
    have hU : MeasurableSet (sourceUnion R) :=
      sourceUnion_measurable R hR.2.2.2.2.1
    have hdom : ∀ x : E4, sourceFunction R x ≤
        (sourceUnion R).indicator (fun _ ↦ (3 : ENNReal)) x := by
      intro x
      by_cases hx : x ∈ sourceUnion R
      · simpa [hx] using hpoint x
      · have hzero : sourceFunction R x = 0 := by
          apply le_antisymm
          · exact not_lt.mp (by simpa [sourceUnion] using hx)
          · exact bot_le
        simp [hx, hzero]
    calc
      sourceMass R ≤
          ∫⁻ x, (sourceUnion R).indicator
            (fun _ ↦ (3 : ENNReal)) x ∂volume :=
        lintegral_mono hdom
      _ = 3 * volume (sourceUnion R) := by
        simpa [mul_comm] using
          (MeasureTheory.lintegral_indicator_const
            (μ := volume) hU (3 : ENNReal))
  have hcancel : gain + 1 ≤ (3 : ENNReal) := by
    apply (ENNReal.mul_le_mul_iff_right hunion0 hunionTop).mp
    calc
      volume (sourceUnion R) * (gain + 1) =
          (gain + 1) * volume (sourceUnion R) := mul_comm _ _
      _ ≤ sourceMass R := hfailure
      _ ≤ 3 * volume (sourceUnion R) := hmassUpper
      _ = volume (sourceUnion R) * 3 := mul_comm _ _
  exact (not_le_of_gt hgain) hcancel

/-- Enumerated form of the fourfold common-overlap conclusion.  The four
indices are genuinely distinct, carry positive retained weight, and contain
the same physical point in their shadings. -/
theorem scaled_union_failure_has_four_distinct_common_shading_rows
    {n : ℕ} {R D : FiniteScaleSource n} {epsilon : ℝ}
    {C gain : ENNReal}
    (hD : IsAdmissibleStickySource D epsilon C)
    (hR : IsFractionalSourceRestriction R D)
    (hmass0 : sourceMass R ≠ 0)
    (hgain : (3 : ENNReal) < gain + 1)
    (hfailure : (gain + 1) * volume (sourceUnion R) ≤ sourceMass R) :
    ∃ (x : E4) (index : Fin 4 → Fin n),
      Function.Injective index ∧
      ∀ k, x ∈ R.shading (index k) ∧ 0 < R.weight (index k) := by
  classical
  obtain ⟨x, hcard⟩ :=
    scaled_union_failure_has_fourfold_common_overlap
      hD hR hmass0 hgain hfailure
  obtain ⟨rows, hrowsSubset, hrowsCard⟩ :=
    Finset.exists_subset_card_eq hcard
  let e : {i // i ∈ rows} ≃ Fin 4 :=
    (Finset.equivFin rows).trans (finCongr hrowsCard)
  let index : Fin 4 → Fin n := fun k ↦ (e.symm k).1
  refine ⟨x, index, ?_, ?_⟩
  · intro a b hab
    apply e.symm.injective
    exact Subtype.ext hab
  · intro k
    have hrow : index k ∈ sourceActiveIndicesAtPoint R x :=
      hrowsSubset (e.symm k).2
    simp only [sourceActiveIndicesAtPoint, Finset.mem_filter,
      Finset.mem_univ, true_and] at hrow
    exact ⟨hrow.1, bot_lt_iff_ne_bot.mpr hrow.2⟩

/-- Every row of an admissible fractional restriction is bounded by the
volume of one ambient marked tube.  In particular, the bound is uniform in
the retained shading and its fractional weight. -/
theorem sourceRowMass_le_sourceGeometricEdgeCapacity_of_fractional_admissible
    {n : ℕ} {R D : FiniteScaleSource n} {epsilon : ℝ} {C : ENNReal}
    (hD : IsAdmissibleStickySource D epsilon C)
    (hR : IsFractionalSourceRestriction R D) (i : Fin n) :
    sourceRowMass R i ≤ sourceGeometricEdgeCapacity D := by
  have hweight : R.weight i ≤ 1 :=
    (hR.2.2.2.2.2.2 i).trans (hD.2.2.1 i)
  have hshadeTube : R.shading i ⊆
      markedUnitTube (D.line i) D.thickness := by
    intro x hx
    exact hD.2.2.2.2.2.2.2.1 i x (hR.2.2.2.2.2.1 i hx)
  unfold sourceRowMass sourceGeometricEdgeCapacity
  calc
    R.weight i * volume (R.shading i) ≤
        1 * volume (R.shading i) := by
      simpa [mul_comm] using
        mul_le_mul_right hweight (volume (R.shading i))
    _ = volume (R.shading i) := one_mul _
    _ ≤ volume (markedUnitTube (D.line i) D.thickness) :=
      measure_mono hshadeTube
    _ ≤ 32 * (ENNReal.ofReal D.thickness) ^ 3 *
          ENNReal.ofReal (Real.pi ^ 2 / 2) :=
      volume_markedUnitTube_upper_bound (hD.2.2.2.2.1 i) hD.1
        (le_of_lt hD.2.1)

/-- A raw pair contribution is bounded by the same geometric capacity as a
complete source row.  This estimate is made before row normalization, so it
can be combined with the gain-preserving off-diagonal energy inequality. -/
theorem sourcePairMass_le_sourceGeometricEdgeCapacity_of_fractional_admissible
    {n : ℕ} {R D : FiniteScaleSource n} {epsilon : ℝ} {C : ENNReal}
    (hD : IsAdmissibleStickySource D epsilon C)
    (hR : IsFractionalSourceRestriction R D) (i j : Fin n) :
    sourcePairMass R i j ≤ sourceGeometricEdgeCapacity D := by
  have hweightI : R.weight i ≤ 1 :=
    (hR.2.2.2.2.2.2 i).trans (hD.2.2.1 i)
  have hweightJ : R.weight j ≤ 1 :=
    (hR.2.2.2.2.2.2 j).trans (hD.2.2.1 j)
  have hweights : R.weight i * R.weight j ≤ 1 := by
    calc
      R.weight i * R.weight j ≤ 1 * 1 :=
        mul_le_mul' hweightI hweightJ
      _ = 1 := one_mul 1
  have hshadeTube : R.shading i ⊆
      markedUnitTube (D.line i) D.thickness := by
    intro x hx
    exact hD.2.2.2.2.2.2.2.1 i x (hR.2.2.2.2.2.1 i hx)
  unfold sourcePairMass sourceGeometricEdgeCapacity
  calc
    (R.weight i * R.weight j) * volume (R.shading i ∩ R.shading j) ≤
        1 * volume (R.shading i ∩ R.shading j) := by
      simpa [mul_comm] using
        mul_le_mul_right hweights (volume (R.shading i ∩ R.shading j))
    _ = volume (R.shading i ∩ R.shading j) := one_mul _
    _ ≤ volume (R.shading i) := measure_mono inter_subset_left
    _ ≤ volume (markedUnitTube (D.line i) D.thickness) :=
      measure_mono hshadeTube
    _ ≤ 32 * (ENNReal.ofReal D.thickness) ^ 3 *
          ENNReal.ofReal (Real.pi ^ 2 / 2) :=
      volume_markedUnitTube_upper_bound (hD.2.2.2.2.1 i) hD.1
        (le_of_lt hD.2.1)

/-- A raw collision edge is bounded by the volume of the actual retained
physical union, rather than by the volume of a complete ambient tube.  This
is the scale-sharp local capacity: once both endpoint weights are positive,
the entire first shading, and hence their intersection, lies in
`sourceUnion R`. -/
theorem sourcePairMass_le_volume_sourceUnion_of_weight_le_one
    {n : ℕ} (R : FiniteScaleSource n)
    (hweight : ∀ i, R.weight i ≤ 1) (i j : Fin n) :
    sourcePairMass R i j ≤ volume (sourceUnion R) := by
  by_cases hi : R.weight i = 0
  · simp [sourcePairMass, hi]
  by_cases hj : R.weight j = 0
  · simp [sourcePairMass, hj]
  have hiPos : 0 < R.weight i := bot_lt_iff_ne_bot.mpr hi
  have hweights : R.weight i * R.weight j ≤ 1 := by
    calc
      R.weight i * R.weight j ≤ 1 * 1 :=
        mul_le_mul' (hweight i) (hweight j)
      _ = 1 := one_mul 1
  unfold sourcePairMass
  calc
    (R.weight i * R.weight j) * volume (R.shading i ∩ R.shading j) ≤
        1 * volume (R.shading i ∩ R.shading j) := by
      simpa [mul_comm] using
        mul_le_mul_right hweights (volume (R.shading i ∩ R.shading j))
    _ = volume (R.shading i ∩ R.shading j) := one_mul _
    _ ≤ volume (sourceUnion R) := by
      apply measure_mono
      exact inter_subset_left.trans
        (shading_subset_sourceUnion_of_weight_pos R i hiPos)

/-- The complete off-diagonal energy is bounded by the number of its genuine
support edges times the physical union volume.  Unlike the ambient-tube
capacity bound, this estimate gains the missing longitudinal factor at a
localized bad ball. -/
theorem sourceOffDiagonalMass_le_rawCollisionCard_mul_unionVolume
    {n : ℕ} (R : FiniteScaleSource n)
    (hweight : ∀ i, R.weight i ≤ 1) :
    sourceOffDiagonalMass R ≤
      ((sourceRawCollisionSupport R).card : ENNReal) *
        volume (sourceUnion R) := by
  rw [← sum_sourceRawCollisionSupport_eq_offDiagonal R]
  calc
    (∑ p ∈ sourceRawCollisionSupport R,
        sourcePairMass R p.1 p.2) ≤
        ∑ _p ∈ sourceRawCollisionSupport R,
          volume (sourceUnion R) := by
      exact Finset.sum_le_sum fun p _hp ↦
        sourcePairMass_le_volume_sourceUnion_of_weight_le_one
          R hweight p.1 p.2
    _ = ((sourceRawCollisionSupport R).card : ENNReal) *
          volume (sourceUnion R) := by
      simp

/-- A scaled union failure forces a quadratic number of actual marked
collision edges.  The same local union volume occurs in the lower and upper
energy bounds and cancels, so no ambient `delta^3` edge-capacity loss remains.
This is the gain-preserving weighted-to-unweighted bridge needed before DRC. -/
theorem scaled_union_failure_forces_markedCollision_cardinality_quadratic
    {n : ℕ} {R D : FiniteScaleSource n} {epsilon : ℝ}
    {C gain : ENNReal}
    (hD : IsAdmissibleStickySource D epsilon C)
    (hR : IsFractionalSourceRestriction R D)
    (hmass0 : sourceMass R ≠ 0)
    (hfailure : (gain + 1) * volume (sourceUnion R) ≤ sourceMass R) :
    gain * (gain + 1) ≤
      ((sourceMarkedCollisionSupport R).card : ENNReal) := by
  have hunionTop : volume (sourceUnion R) ≠ ⊤ :=
    volume_sourceUnion_ne_top_of_fractional_admissibleStickySource hD hR
  have hholder := sourceMass_le_sqrt_energy_mul_sqrt_union R hR.2.2.2.2.1
  have hunion0 : volume (sourceUnion R) ≠ 0 := by
    intro hzero
    rw [hzero] at hholder
    simp at hholder
    exact hmass0 hholder
  have hoffDiagonal :
      gain * sourceMass R ≤ sourceOffDiagonalMass R :=
    scaled_union_failure_forces_source_offDiagonal_of_fractional_admissible
      hD hR hmass0 hfailure
  have hweight : ∀ i, R.weight i ≤ 1 := fun i ↦
    (hR.2.2.2.2.2.2 i).trans (hD.2.2.1 i)
  have hraw :
      sourceOffDiagonalMass R ≤
        ((sourceRawCollisionSupport R).card : ENNReal) *
          volume (sourceUnion R) :=
    sourceOffDiagonalMass_le_rawCollisionCard_mul_unionVolume R hweight
  have hscaled :
      (gain * (gain + 1)) * volume (sourceUnion R) ≤
        ((sourceRawCollisionSupport R).card : ENNReal) *
          volume (sourceUnion R) := by
    calc
      (gain * (gain + 1)) * volume (sourceUnion R) =
          gain * ((gain + 1) * volume (sourceUnion R)) := by ac_rfl
      _ ≤ gain * sourceMass R := by gcongr
      _ ≤ sourceOffDiagonalMass R := hoffDiagonal
      _ ≤ ((sourceRawCollisionSupport R).card : ENNReal) *
          volume (sourceUnion R) := hraw
  have hcard : gain * (gain + 1) ≤
      ((sourceRawCollisionSupport R).card : ENNReal) :=
    (ENNReal.mul_le_mul_iff_right hunion0 hunionTop).mp (by
      simpa [mul_comm] using hscaled)
  simpa [card_sourceMarkedCollisionSupport,
    sourceRawCollisionSupport_eq_sourceCollisionSupport hD hR] using hcard

/-- The complete raw off-diagonal energy is bounded by the number of its
genuine support edges times one geometric edge capacity. -/
theorem sourceOffDiagonalMass_le_rawCollisionCard_mul_geometricCapacity
    {n : ℕ} {R D : FiniteScaleSource n} {epsilon : ℝ} {C : ENNReal}
    (hD : IsAdmissibleStickySource D epsilon C)
    (hR : IsFractionalSourceRestriction R D) :
    sourceOffDiagonalMass R ≤
      ((sourceRawCollisionSupport R).card : ENNReal) *
        sourceGeometricEdgeCapacity D := by
  rw [← sum_sourceRawCollisionSupport_eq_offDiagonal R]
  calc
    (∑ p ∈ sourceRawCollisionSupport R,
        sourcePairMass R p.1 p.2) ≤
        ∑ _p ∈ sourceRawCollisionSupport R,
          sourceGeometricEdgeCapacity D := by
      exact Finset.sum_le_sum fun p _hp ↦
        sourcePairMass_le_sourceGeometricEdgeCapacity_of_fractional_admissible
          hD hR p.1 p.2
    _ = ((sourceRawCollisionSupport R).card : ENNReal) *
          sourceGeometricEdgeCapacity D := by
      simp

/-- Gain-preserving geometric collision count.  A scaled union failure forces
the full raw gain into the cardinality of actual marked collision edges; no
Markov row normalization is used in this passage. -/
theorem scaled_union_failure_forces_markedCollision_cardinality_geometric
    {n : ℕ} {R D : FiniteScaleSource n} {epsilon : ℝ}
    {C gain : ENNReal}
    (hD : IsAdmissibleStickySource D epsilon C)
    (hR : IsFractionalSourceRestriction R D)
    (hmass0 : sourceMass R ≠ 0)
    (hfailure : (gain + 1) * volume (sourceUnion R) ≤ sourceMass R) :
    gain * sourceMass R ≤
      ((sourceMarkedCollisionSupport R).card : ENNReal) *
        sourceGeometricEdgeCapacity D := by
  calc
    gain * sourceMass R ≤ sourceOffDiagonalMass R :=
      scaled_union_failure_forces_source_offDiagonal_of_fractional_admissible
        hD hR hmass0 hfailure
    _ ≤ ((sourceRawCollisionSupport R).card : ENNReal) *
          sourceGeometricEdgeCapacity D :=
      sourceOffDiagonalMass_le_rawCollisionCard_mul_geometricCapacity hD hR
    _ = ((sourceMarkedCollisionSupport R).card : ENNReal) *
          sourceGeometricEdgeCapacity D := by
      rw [card_sourceMarkedCollisionSupport,
        ← sourceRawCollisionSupport_eq_sourceCollisionSupport hD hR]

/-- The formerly assumed per-edge capacity is forced by the admissible source
geometry.  Thus the heavy-edge ledger has no independent `hcap` input. -/
theorem sourceNormalizedCollisionFlow_le_sourceGeometricEdgeCapacity
    {n : ℕ} {R D : FiniteScaleSource n} {epsilon : ℝ} {C : ENNReal}
    (hD : IsAdmissibleStickySource D epsilon C)
    (hR : IsFractionalSourceRestriction R D) (i j : Fin n) :
    sourceNormalizedCollisionFlow R i j ≤ sourceGeometricEdgeCapacity D := by
  exact (sourceNormalizedCollisionFlow_le_sourceRowMass_of_row_finite R i j
    (sourceOffDiagonalRowMass_ne_top_of_fractional_admissibleStickySource
      hD hR i)).trans
    (sourceRowMass_le_sourceGeometricEdgeCapacity_of_fractional_admissible
      hD hR i)

/-- Collision pairs whose normalized flow exceeds a chosen threshold. -/
def sourceHeavyCollisionSupport {n : ℕ} (R : FiniteScaleSource n)
    (threshold : ENNReal) : Finset (Fin n × Fin n) := by
  classical
  exact (Finset.univ ×ˢ Finset.univ).filter fun p ↦
    threshold < sourceNormalizedCollisionFlow R p.1 p.2

/-- The complementary light pairs. -/
def sourceLightCollisionSupport {n : ℕ} (R : FiniteScaleSource n)
    (threshold : ENNReal) : Finset (Fin n × Fin n) := by
  classical
  exact (Finset.univ ×ˢ Finset.univ).filter fun p ↦
    ¬ threshold < sourceNormalizedCollisionFlow R p.1 p.2

theorem sourceHeavyCollisionSupport_subset_sourceCollisionSupport
    {n : ℕ} (R : FiniteScaleSource n) (threshold : ENNReal) :
    sourceHeavyCollisionSupport R threshold ⊆ sourceCollisionSupport R := by
  classical
  intro p hp
  have hheavy : threshold < sourceNormalizedCollisionFlow R p.1 p.2 := by
    simpa [sourceHeavyCollisionSupport] using hp
  have hflow : sourceNormalizedCollisionFlow R p.1 p.2 ≠ 0 := by
    exact ne_of_gt (lt_of_le_of_lt bot_le hheavy)
  rcases p with ⟨i, j⟩
  simpa using (mem_sourceCollisionSupport_iff R i j).2 hflow

/-- At threshold zero the heavy support is exactly the complete positive-flow
collision support.  This eliminates any separate threshold-selection loss
when only support cardinality is required. -/
theorem sourceHeavyCollisionSupport_zero {n : ℕ}
    (R : FiniteScaleSource n) :
    sourceHeavyCollisionSupport R 0 = sourceCollisionSupport R := by
  classical
  ext p
  rcases p with ⟨i, j⟩
  simp only [sourceHeavyCollisionSupport, Finset.mem_filter,
    Finset.mem_product, Finset.mem_univ, and_self]
  simpa using
    (pos_iff_ne_zero.trans (mem_sourceCollisionSupport_iff R i j).symm)

/-- Heavy and light pairs give an exact partition of the complete normalized
collision flow. -/
theorem totalFlow_eq_heavy_add_light {n : ℕ}
    (R : FiniteScaleSource n) (threshold : ENNReal) :
    (∑ i, ∑ j, sourceNormalizedCollisionFlow R i j) =
      (∑ p ∈ sourceHeavyCollisionSupport R threshold,
        sourceNormalizedCollisionFlow R p.1 p.2) +
      ∑ p ∈ sourceLightCollisionSupport R threshold,
        sourceNormalizedCollisionFlow R p.1 p.2 := by
  classical
  calc
    (∑ i, ∑ j, sourceNormalizedCollisionFlow R i j) =
        ∑ p ∈ (Finset.univ ×ˢ Finset.univ),
          sourceNormalizedCollisionFlow R p.1 p.2 :=
      (Finset.sum_product' Finset.univ Finset.univ
        (sourceNormalizedCollisionFlow R)).symm
    _ = (∑ p ∈ sourceHeavyCollisionSupport R threshold,
          sourceNormalizedCollisionFlow R p.1 p.2) +
        ∑ p ∈ sourceLightCollisionSupport R threshold,
          sourceNormalizedCollisionFlow R p.1 p.2 := by
      simpa [sourceHeavyCollisionSupport, sourceLightCollisionSupport] using
        (Finset.sum_filter_add_sum_filter_not
          (Finset.univ ×ˢ Finset.univ)
          (fun p : Fin n × Fin n ↦
            threshold < sourceNormalizedCollisionFlow R p.1 p.2)
          (fun p ↦ sourceNormalizedCollisionFlow R p.1 p.2)).symm

/-- The light part costs at most the number of all ordered pairs times the
threshold. -/
theorem lightCollisionFlow_le_pairCount_mul_threshold {n : ℕ}
    (R : FiniteScaleSource n) (threshold : ENNReal) :
    (∑ p ∈ sourceLightCollisionSupport R threshold,
        sourceNormalizedCollisionFlow R p.1 p.2) ≤
      ((n * n : ℕ) : ENNReal) * threshold := by
  calc
    (∑ p ∈ sourceLightCollisionSupport R threshold,
        sourceNormalizedCollisionFlow R p.1 p.2) ≤
        ∑ _p ∈ sourceLightCollisionSupport R threshold, threshold := by
      apply Finset.sum_le_sum
      intro p hp
      have hlight :
          ¬ threshold < sourceNormalizedCollisionFlow R p.1 p.2 := by
        simpa [sourceLightCollisionSupport] using hp
      exact le_of_not_gt hlight
    _ = (((sourceLightCollisionSupport R threshold).card : ℕ) : ENNReal) *
          threshold := by simp
    _ ≤ ((n * n : ℕ) : ENNReal) * threshold := by
      gcongr
      simpa using (Finset.card_le_card
        (show sourceLightCollisionSupport R threshold ⊆
            Finset.univ ×ˢ (Finset.univ : Finset (Fin n)) by
          intro p hp
          simpa [sourceLightCollisionSupport] using hp))
    _ = ((n * n : ℕ) : ENNReal) * threshold := rfl

/-- A capacity bound on the genuine support also bounds the heavy part, since
every heavy pair is a genuine collision edge. -/
theorem heavyCollisionFlow_le_card_mul_of_support_cap
    {n : ℕ} (R : FiniteScaleSource n) (threshold edgeCapacity : ENNReal)
    (hcap : ∀ p ∈ sourceCollisionSupport R,
      sourceNormalizedCollisionFlow R p.1 p.2 ≤ edgeCapacity) :
    (∑ p ∈ sourceHeavyCollisionSupport R threshold,
        sourceNormalizedCollisionFlow R p.1 p.2) ≤
      ((sourceHeavyCollisionSupport R threshold).card : ENNReal) *
        edgeCapacity := by
  calc
    (∑ p ∈ sourceHeavyCollisionSupport R threshold,
        sourceNormalizedCollisionFlow R p.1 p.2) ≤
        ∑ _p ∈ sourceHeavyCollisionSupport R threshold, edgeCapacity := by
      exact Finset.sum_le_sum fun p hp ↦
        hcap p (sourceHeavyCollisionSupport_subset_sourceCollisionSupport
          R threshold hp)
    _ = ((sourceHeavyCollisionSupport R threshold).card : ENNReal) *
          edgeCapacity := by simp

/-- Threshold regularization of the complete collision kernel.  This is the
weighted-to-unweighted interface needed before degree pruning and DRC. -/
theorem totalFlow_le_heavyCard_mul_add_lightBudget
    {n : ℕ} (R : FiniteScaleSource n) (threshold edgeCapacity : ENNReal)
    (hcap : ∀ p ∈ sourceCollisionSupport R,
      sourceNormalizedCollisionFlow R p.1 p.2 ≤ edgeCapacity) :
    (∑ i, ∑ j, sourceNormalizedCollisionFlow R i j) ≤
      ((sourceHeavyCollisionSupport R threshold).card : ENNReal) *
          edgeCapacity +
        ((n * n : ℕ) : ENNReal) * threshold := by
  rw [totalFlow_eq_heavy_add_light]
  exact add_le_add
    (heavyCollisionFlow_le_card_mul_of_support_cap
      R threshold edgeCapacity hcap)
    (lightCollisionFlow_le_pairCount_mul_threshold R threshold)

/-- Under factor-two union failure, the heavy graph plus the explicit light
budget carries the whole retained source mass. -/
theorem factor_two_union_failure_forces_heavyCollision_budget
    {n : ℕ} {R D : FiniteScaleSource n} {epsilon : ℝ} {C : ENNReal}
    (hD : IsAdmissibleStickySource D epsilon C)
    (hR : IsFractionalSourceRestriction R D)
    (hfailure : 2 * volume (sourceUnion R) ≤ sourceMass R)
    (threshold edgeCapacity : ENNReal)
    (hcap : ∀ p ∈ sourceCollisionSupport R,
      sourceNormalizedCollisionFlow R p.1 p.2 ≤ edgeCapacity) :
    sourceMass R ≤
      2 * (((sourceHeavyCollisionSupport R threshold).card : ENNReal) *
          edgeCapacity + ((n * n : ℕ) : ENNReal) * threshold) := by
  calc
    sourceMass R ≤
        2 * (∑ i, ∑ j, sourceNormalizedCollisionFlow R i j) :=
      factor_two_union_failure_forces_normalizedCollisionFlow hD hR hfailure
    _ ≤ 2 * (((sourceHeavyCollisionSupport R threshold).card : ENNReal) *
          edgeCapacity + ((n * n : ℕ) : ENNReal) * threshold) := by
      gcongr
      exact totalFlow_le_heavyCard_mul_add_lightBudget
        R threshold edgeCapacity hcap

/-- If the threshold is chosen so that the explicit light budget is no larger
than the heavy-edge capacity budget, the heavy graph alone carries the failed
source mass, up to the fixed factor four. -/
theorem factor_two_union_failure_forces_heavyCollision_cardinality_of_light_le_heavy
    {n : ℕ} {R D : FiniteScaleSource n} {epsilon : ℝ} {C : ENNReal}
    (hD : IsAdmissibleStickySource D epsilon C)
    (hR : IsFractionalSourceRestriction R D)
    (hfailure : 2 * volume (sourceUnion R) ≤ sourceMass R)
    (threshold edgeCapacity : ENNReal)
    (hcap : ∀ p ∈ sourceCollisionSupport R,
      sourceNormalizedCollisionFlow R p.1 p.2 ≤ edgeCapacity)
    (hlight : ((n * n : ℕ) : ENNReal) * threshold ≤
      ((sourceHeavyCollisionSupport R threshold).card : ENNReal) *
        edgeCapacity) :
    sourceMass R ≤
      4 * (((sourceHeavyCollisionSupport R threshold).card : ENNReal) *
        edgeCapacity) := by
  let heavyBudget : ENNReal :=
    ((sourceHeavyCollisionSupport R threshold).card : ENNReal) * edgeCapacity
  calc
    sourceMass R ≤
        2 * (heavyBudget + ((n * n : ℕ) : ENNReal) * threshold) := by
      simpa [heavyBudget] using
        factor_two_union_failure_forces_heavyCollision_budget
          hD hR hfailure threshold edgeCapacity hcap
    _ ≤ 2 * (heavyBudget + heavyBudget) := by
      gcongr
    _ = 4 * heavyBudget := by ring
    _ = 4 * (((sourceHeavyCollisionSupport R threshold).card : ENNReal) *
        edgeCapacity) := rfl

/-- Heavy collision edges expressed as pairs of actual marked lines.  The
source parametrization is injective, so this transport preserves cardinality
and hence preserves the preceding quantitative lower bound exactly. -/
def sourceMarkedHeavyCollisionSupport {n : ℕ} (R : FiniteScaleSource n)
    (threshold : ENNReal) : Finset (MarkedLine × MarkedLine) := by
  classical
  exact (sourceHeavyCollisionSupport R threshold).image (sourceLinePair R)

theorem card_sourceMarkedHeavyCollisionSupport {n : ℕ}
    (R : FiniteScaleSource n) (threshold : ENNReal) :
    (sourceMarkedHeavyCollisionSupport R threshold).card =
      (sourceHeavyCollisionSupport R threshold).card := by
  classical
  apply Finset.card_image_iff.mpr
  intro p hp q hq hpq
  exact sourceLinePair_injective R hpq

theorem sourceMarkedHeavyCollisionSupport_subset_sourceMarkedCollisionSupport
    {n : ℕ} (R : FiniteScaleSource n) (threshold : ENNReal) :
    sourceMarkedHeavyCollisionSupport R threshold ⊆
      sourceMarkedCollisionSupport R := by
  classical
  intro p hp
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
  exact Finset.mem_image.mpr
    ⟨q, sourceHeavyCollisionSupport_subset_sourceCollisionSupport
      R threshold hq, rfl⟩

theorem sourceMarkedHeavyCollisionSupport_zero {n : ℕ}
    (R : FiniteScaleSource n) :
    sourceMarkedHeavyCollisionSupport R 0 =
      sourceMarkedCollisionSupport R := by
  simp [sourceMarkedHeavyCollisionSupport, sourceMarkedCollisionSupport,
    sourceHeavyCollisionSupport_zero]

theorem sourceMarkedHeavyCollisionSupport_lines_ne
    {n : ℕ} {R : FiniteScaleSource n} {threshold : ENNReal}
    {p : MarkedLine × MarkedLine}
    (hp : p ∈ sourceMarkedHeavyCollisionSupport R threshold) :
    p.1 ≠ p.2 := by
  exact sourceMarkedCollisionSupport_lines_ne
    (sourceMarkedHeavyCollisionSupport_subset_sourceMarkedCollisionSupport
      R threshold hp)

/-- The canonical collision time and the contact residual bounds already
constructed on the full support restrict verbatim to the quantitative heavy
graph. -/
theorem sourceMarkedHeavyCollisionSupport_has_uniform_contact_residual_control
    {n : ℕ} {R D : FiniteScaleSource n} {epsilon : ℝ} {C : ENNReal}
    (hD : IsAdmissibleStickySource D epsilon C)
    (hR : IsFractionalSourceRestriction R D)
    (kappa : ℝ) (hkappa : 0 < kappa)
    (hchart : ∀ i, kappa ≤ |direction (R.line i) (3 : Fin 4)|)
    (eta : ℝ) (heta : 0 < eta) (threshold : ENNReal)
    {p : MarkedLine × MarkedLine}
    (hp : p ∈ sourceMarkedHeavyCollisionSupport R threshold) :
    markedPairContactResidualNorm p
          (markedSourceCollisionTime hD hR kappa hkappa hchart eta heta p) <
        (2 * kappa⁻¹ + 2) * (R.thickness + eta) ∧
    markedPairContactResidualNorm (p.2, p.1)
          (markedSourceCollisionTime hD hR kappa hkappa hchart eta heta p) <
        (2 * kappa⁻¹ + 2) * (R.thickness + eta) := by
  exact markedSourceCollisionTime_spec hD hR kappa hkappa hchart eta heta
    (sourceMarkedHeavyCollisionSupport_subset_sourceMarkedCollisionSupport
      R threshold hp)

theorem factor_two_union_failure_forces_markedHeavyCollision_cardinality
    {n : ℕ} {R D : FiniteScaleSource n} {epsilon : ℝ} {C : ENNReal}
    (hD : IsAdmissibleStickySource D epsilon C)
    (hR : IsFractionalSourceRestriction R D)
    (hfailure : 2 * volume (sourceUnion R) ≤ sourceMass R)
    (threshold edgeCapacity : ENNReal)
    (hcap : ∀ p ∈ sourceCollisionSupport R,
      sourceNormalizedCollisionFlow R p.1 p.2 ≤ edgeCapacity)
    (hlight : ((n * n : ℕ) : ENNReal) * threshold ≤
      ((sourceHeavyCollisionSupport R threshold).card : ENNReal) *
        edgeCapacity) :
    sourceMass R ≤
      4 * (((sourceMarkedHeavyCollisionSupport R threshold).card : ENNReal) *
        edgeCapacity) := by
  rw [card_sourceMarkedHeavyCollisionSupport]
  exact
    factor_two_union_failure_forces_heavyCollision_cardinality_of_light_le_heavy
      hD hR hfailure threshold edgeCapacity hcap hlight

/-- Fully geometric version of the marked heavy-collision lower bound: the
edge-capacity hypothesis has been discharged by the marked-tube volume bound. -/
theorem factor_two_union_failure_forces_markedHeavyCollision_cardinality_geometric
    {n : ℕ} {R D : FiniteScaleSource n} {epsilon : ℝ} {C : ENNReal}
    (hD : IsAdmissibleStickySource D epsilon C)
    (hR : IsFractionalSourceRestriction R D)
    (hfailure : 2 * volume (sourceUnion R) ≤ sourceMass R)
    (threshold : ENNReal)
    (hlight : ((n * n : ℕ) : ENNReal) * threshold ≤
      ((sourceHeavyCollisionSupport R threshold).card : ENNReal) *
        sourceGeometricEdgeCapacity D) :
    sourceMass R ≤
      4 * (((sourceMarkedHeavyCollisionSupport R threshold).card : ENNReal) *
        sourceGeometricEdgeCapacity D) := by
  exact factor_two_union_failure_forces_markedHeavyCollision_cardinality
    hD hR hfailure threshold (sourceGeometricEdgeCapacity D)
    (fun p _ ↦ sourceNormalizedCollisionFlow_le_sourceGeometricEdgeCapacity
      hD hR p.1 p.2)
    hlight

/-- Zero-threshold closure of the collision ledger.  A factor-two physical
union failure forces many genuine marked collision edges, with both the
per-edge capacity and the light-flow payment discharged internally. -/
theorem factor_two_union_failure_forces_markedCollision_cardinality_geometric
    {n : ℕ} {R D : FiniteScaleSource n} {epsilon : ℝ} {C : ENNReal}
    (hD : IsAdmissibleStickySource D epsilon C)
    (hR : IsFractionalSourceRestriction R D)
    (hfailure : 2 * volume (sourceUnion R) ≤ sourceMass R) :
    sourceMass R ≤
      4 * (((sourceMarkedCollisionSupport R).card : ENNReal) *
        sourceGeometricEdgeCapacity D) := by
  have h :=
    factor_two_union_failure_forces_markedHeavyCollision_cardinality_geometric
      hD hR hfailure 0 (by simp)
  simpa [sourceMarkedHeavyCollisionSupport_zero] using h

end StickyKakeya4
