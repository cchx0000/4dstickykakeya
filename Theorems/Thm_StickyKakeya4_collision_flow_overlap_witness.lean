import Theorems.Thm_StickyKakeya4_finite_scale_source_mass

open MeasureTheory Set

noncomputable section

namespace StickyKakeya4

/-- The literal finite support of the row-normalized collision flow.  An edge
is retained exactly when the actual weighted shading intersection sends
nonzero flow; no auxiliary graph is inserted. -/
def sourceCollisionSupport {n : ℕ} (D : FiniteScaleSource n) :
    Finset (Fin n × Fin n) := by
  classical
  exact (Finset.univ ×ˢ Finset.univ).filter fun p ↦
    sourceNormalizedCollisionFlow D p.1 p.2 ≠ 0

@[simp] theorem mem_sourceCollisionSupport_iff {n : ℕ}
    (D : FiniteScaleSource n) (i j : Fin n) :
    (i, j) ∈ sourceCollisionSupport D ↔
      sourceNormalizedCollisionFlow D i j ≠ 0 := by
  classical
  simp [sourceCollisionSupport]

/-- Every nonzero normalized collision-flow edge is genuinely off diagonal. -/
theorem sourceNormalizedCollisionFlow_ne_zero_implies_ne {n : ℕ}
    (D : FiniteScaleSource n) {i j : Fin n}
    (hflow : sourceNormalizedCollisionFlow D i j ≠ 0) :
    i ≠ j := by
  intro hij
  subst j
  simp [sourceNormalizedCollisionFlow] at hflow

/-- A nonzero normalized edge comes from a nonzero raw weighted shading
intersection. -/
theorem sourceNormalizedCollisionFlow_ne_zero_implies_pairMass_ne_zero
    {n : ℕ} (D : FiniteScaleSource n) {i j : Fin n}
    (hflow : sourceNormalizedCollisionFlow D i j ≠ 0) :
    sourcePairMass D i j ≠ 0 := by
  have hij := sourceNormalizedCollisionFlow_ne_zero_implies_ne D hflow
  intro hpair
  simp [sourceNormalizedCollisionFlow, hij, hpair] at hflow

/-- The underlying shading intersection of every nonzero normalized edge has
positive measure.  In particular the support graph cannot be created merely
by normalization of a zero physical incidence. -/
theorem sourceNormalizedCollisionFlow_ne_zero_implies_intersection_measure_ne_zero
    {n : ℕ} (D : FiniteScaleSource n) {i j : Fin n}
    (hflow : sourceNormalizedCollisionFlow D i j ≠ 0) :
    volume (D.shading i ∩ D.shading j) ≠ 0 := by
  have hpair :=
    sourceNormalizedCollisionFlow_ne_zero_implies_pairMass_ne_zero D hflow
  intro hvolume
  simp [sourcePairMass, hvolume] at hpair

/-- Every support edge has a literal common physical point in its two
shadings. -/
theorem sourceCollisionSupport_has_physical_overlap {n : ℕ}
    (D : FiniteScaleSource n) {i j : Fin n}
    (hedge : (i, j) ∈ sourceCollisionSupport D) :
    ∃ x : E4, x ∈ D.shading i ∧ x ∈ D.shading j := by
  have hflow : sourceNormalizedCollisionFlow D i j ≠ 0 :=
    (mem_sourceCollisionSupport_iff D i j).mp hedge
  have hmeasure : volume (D.shading i ∩ D.shading j) ≠ 0 :=
    sourceNormalizedCollisionFlow_ne_zero_implies_intersection_measure_ne_zero
      D hflow
  obtain ⟨x, hxi, hxj⟩ := nonempty_of_measure_ne_zero hmeasure
  exact ⟨x, hxi, hxj⟩

/-- A support edge joins two distinct actual marked lines. -/
theorem sourceCollisionSupport_lines_ne {n : ℕ}
    (D : FiniteScaleSource n) {i j : Fin n}
    (hedge : (i, j) ∈ sourceCollisionSupport D) :
    D.line i ≠ D.line j := by
  have hflow : sourceNormalizedCollisionFlow D i j ≠ 0 :=
    (mem_sourceCollisionSupport_iff D i j).mp hedge
  have hij : i ≠ j :=
    sourceNormalizedCollisionFlow_ne_zero_implies_ne D hflow
  intro hline
  exact hij (D.line_injective hline)

/-- For a fractional restriction of an admissible source, the common shading
point furnished by a support edge is simultaneously within the source
thickness of both retained marked unit segments. -/
theorem sourceCollisionSupport_has_marked_tube_overlap
    {n : ℕ} {R D : FiniteScaleSource n} {epsilon : ℝ} {C : ENNReal}
    (hD : IsAdmissibleStickySource D epsilon C)
    (hR : IsFractionalSourceRestriction R D) {i j : Fin n}
    (hedge : (i, j) ∈ sourceCollisionSupport R) :
    ∃ x : E4,
      x ∈ R.shading i ∧ x ∈ R.shading j ∧
      Metric.infDist x (unitFront {R.line i}) ≤ R.thickness ∧
      Metric.infDist x (unitFront {R.line j}) ≤ R.thickness := by
  obtain ⟨x, hxi, hxj⟩ := sourceCollisionSupport_has_physical_overlap R hedge
  rcases hD with
    ⟨hdeltaPos, hdeltaLt, hweight, hmark, hvalid, hmeasurable,
      hshadingLower, htube, hdirection, hcover⟩
  rcases hR with
    ⟨hthickness, hline, hfibreMark, htree, hrestrictionMeasurable,
      hshadingSubset, hweightLe⟩
  have hline_i : R.line i = D.line i := congrFun hline i
  have hline_j : R.line j = D.line j := congrFun hline j
  have hi := htube i x (hshadingSubset i hxi)
  have hj := htube j x (hshadingSubset j hxj)
  refine ⟨x, hxi, hxj, ?_, ?_⟩
  · simpa [hline_i, hthickness] using hi
  · simpa [hline_j, hthickness] using hj

/-- An `infDist` tube incidence has a genuine marked-segment parameter
witness, with an arbitrarily small positive slack. -/
theorem exists_rawFrontParam_dist_lt_of_infDist_le
    (line : MarkedLine) (x : E4) {delta eta : ℝ}
    (hnear : Metric.infDist x (unitFront {line}) ≤ delta)
    (heta : 0 < eta) :
    ∃ t ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ),
      dist x (rawFrontParam (line, t)) < delta + eta := by
  have hfrontNonempty : (unitFront {line}).Nonempty :=
    ⟨rawFrontParam (line, 0),
      rawFrontParam_mem_unitFront_singleton line (by norm_num)⟩
  have hinfDistLt :
      Metric.infDist x (unitFront {line}) < delta + eta :=
    hnear.trans_lt (lt_add_of_pos_right delta heta)
  obtain ⟨y, hy, hxy⟩ :=
    (Metric.infDist_lt_iff hfrontNonempty).mp hinfDistLt
  rcases hy with ⟨line', hline', t, ht, rfl⟩
  have hlineEq : line' = line := by simpa using hline'
  subst line'
  exact ⟨t, ht, by simpa [rawFrontParam] using hxy⟩

/-- A collision-support edge of an admissible fractional source has two
literal marked-segment points within `thickness + eta` of the same physical
shading point. -/
theorem sourceCollisionSupport_has_front_parameter_overlap
    {n : ℕ} {R D : FiniteScaleSource n} {epsilon : ℝ} {C : ENNReal}
    (hD : IsAdmissibleStickySource D epsilon C)
    (hR : IsFractionalSourceRestriction R D) {i j : Fin n}
    (hedge : (i, j) ∈ sourceCollisionSupport R)
    {eta : ℝ} (heta : 0 < eta) :
    ∃ (x : E4) (ti tj : ℝ),
      x ∈ R.shading i ∧ x ∈ R.shading j ∧
      ti ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ) ∧
      tj ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ) ∧
      dist x (rawFrontParam (R.line i, ti)) < R.thickness + eta ∧
      dist x (rawFrontParam (R.line j, tj)) < R.thickness + eta := by
  obtain ⟨x, hxi, hxj, hiTube, hjTube⟩ :=
    sourceCollisionSupport_has_marked_tube_overlap hD hR hedge
  obtain ⟨ti, hti, hiDist⟩ :=
    exists_rawFrontParam_dist_lt_of_infDist_le (R.line i) x hiTube heta
  obtain ⟨tj, htj, hjDist⟩ :=
    exists_rawFrontParam_dist_lt_of_infDist_le (R.line j) x hjTube heta
  exact ⟨x, ti, tj, hxi, hxj, hti, htj, hiDist, hjDist⟩

/-- If the total normalized flow is nonzero, its literal support contains an
edge. -/
theorem sourceCollisionSupport_nonempty_of_total_flow_ne_zero {n : ℕ}
    (D : FiniteScaleSource n)
    (htotal : (∑ i, ∑ j, sourceNormalizedCollisionFlow D i j) ≠ 0) :
    (sourceCollisionSupport D).Nonempty := by
  classical
  by_contra hempty
  have hnotMem : ∀ i j, (i, j) ∉ sourceCollisionSupport D := by
    intro i j hedge
    exact hempty ⟨(i, j), hedge⟩
  have hzero : ∀ i j, sourceNormalizedCollisionFlow D i j = 0 := by
    intro i j
    by_contra hflow
    exact hnotMem i j ((mem_sourceCollisionSupport_iff D i j).mpr hflow)
  simp [hzero] at htotal

/-- A factor-two physical-union failure with nonzero source mass produces a
genuine off-diagonal collision edge and a common physical point, with both
marked tube incidences retained.  This is the source-to-collision-support
bridge needed before finite graph pruning and dependent random choice. -/
theorem factor_two_union_failure_has_marked_collision_witness
    {n : ℕ} {R D : FiniteScaleSource n} {epsilon : ℝ} {C : ENNReal}
    (hD : IsAdmissibleStickySource D epsilon C)
    (hR : IsFractionalSourceRestriction R D)
    (hmass : sourceMass R ≠ 0)
    (hfailure : 2 * volume (sourceUnion R) ≤ sourceMass R) :
    ∃ i j : Fin n, ∃ x : E4,
      i ≠ j ∧ R.line i ≠ R.line j ∧
      x ∈ R.shading i ∧ x ∈ R.shading j ∧
      Metric.infDist x (unitFront {R.line i}) ≤ R.thickness ∧
      Metric.infDist x (unitFront {R.line j}) ≤ R.thickness := by
  have hflowBound :=
    factor_two_union_failure_forces_normalizedCollisionFlow hD hR hfailure
  have htotal :
      (∑ i, ∑ j, sourceNormalizedCollisionFlow R i j) ≠ 0 := by
    intro hzero
    have hmassZero : sourceMass R = 0 := by
      have hle : sourceMass R ≤ 0 := by
        simpa [hzero] using hflowBound
      exact le_antisymm hle bot_le
    exact hmass hmassZero
  obtain ⟨p, hp⟩ := sourceCollisionSupport_nonempty_of_total_flow_ne_zero R htotal
  obtain ⟨x, hxi, hxj, hiTube, hjTube⟩ :=
    sourceCollisionSupport_has_marked_tube_overlap hD hR hp
  have hflow : sourceNormalizedCollisionFlow R p.1 p.2 ≠ 0 :=
    (mem_sourceCollisionSupport_iff R p.1 p.2).mp hp
  refine ⟨p.1, p.2, x,
    sourceNormalizedCollisionFlow_ne_zero_implies_ne R hflow,
    sourceCollisionSupport_lines_ne R hp,
    hxi, hxj, hiTube, hjTube⟩

/-- The same union-failure witness with explicit parameters on both actual
marked unit segments.  This is the form consumed by the subsequent fixed
height contact-coordinate estimate. -/
theorem factor_two_union_failure_has_front_parameter_collision_witness
    {n : ℕ} {R D : FiniteScaleSource n} {epsilon : ℝ} {C : ENNReal}
    (hD : IsAdmissibleStickySource D epsilon C)
    (hR : IsFractionalSourceRestriction R D)
    (hmass : sourceMass R ≠ 0)
    (hfailure : 2 * volume (sourceUnion R) ≤ sourceMass R)
    {eta : ℝ} (heta : 0 < eta) :
    ∃ i j : Fin n, ∃ (x : E4) (ti tj : ℝ),
      i ≠ j ∧ R.line i ≠ R.line j ∧
      x ∈ R.shading i ∧ x ∈ R.shading j ∧
      ti ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ) ∧
      tj ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ) ∧
      dist x (rawFrontParam (R.line i, ti)) < R.thickness + eta ∧
      dist x (rawFrontParam (R.line j, tj)) < R.thickness + eta := by
  obtain ⟨i, j, x, hij, hline, hxi, hxj, hiTube, hjTube⟩ :=
    factor_two_union_failure_has_marked_collision_witness
      hD hR hmass hfailure
  obtain ⟨ti, hti, hiDist⟩ :=
    exists_rawFrontParam_dist_lt_of_infDist_le (R.line i) x hiTube heta
  obtain ⟨tj, htj, hjDist⟩ :=
    exists_rawFrontParam_dist_lt_of_infDist_le (R.line j) x hjTube heta
  exact ⟨i, j, x, ti, tj, hij, hline, hxi, hxj,
    hti, htj, hiDist, hjDist⟩

end StickyKakeya4
