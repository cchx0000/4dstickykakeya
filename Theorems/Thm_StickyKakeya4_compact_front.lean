import Definitions.Def_sticky_kakeya4_core

open MeasureTheory Set

namespace StickyKakeya4

/-- The physical front map before choosing one line in each direction. -/
def rawFrontParam (z : MarkedLine × ℝ) : E4 :=
  offset z.1 + (mark z.1 + z.2) • direction z.1

theorem continuous_rawFrontParam : Continuous rawFrontParam := by
  unfold rawFrontParam offset mark direction
  fun_prop

theorem image_rawFrontParam_prod_Icc (lines : Set MarkedLine) :
    rawFrontParam ''
        (lines ×ˢ Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)) =
      unitFront lines := by
  ext x
  constructor
  · rintro ⟨⟨line, t⟩, ⟨hline, ht⟩, rfl⟩
    exact ⟨line, hline, t, ht, rfl⟩
  · rintro ⟨line, hline, t, ht, rfl⟩
    exact ⟨⟨line, t⟩, ⟨hline, ht⟩, rfl⟩

/-- A compact marked-line family has a compact, hence Borel, unit front. -/
theorem IsCompact.unitFront {lines : Set MarkedLine}
    (hlines : IsCompact lines) : IsCompact (unitFront lines) := by
  rw [← image_rawFrontParam_prod_Icc lines]
  exact (hlines.prod isCompact_Icc).image continuous_rawFrontParam

/-- On a compact marked-line family, the physical front is uniformly
continuous jointly in the marked line and in the segment parameter.  This is
the step that lets a finite net in the full marked-line space control physical
displacement without any regularity assumption on the mark as a function of
the unmarked carrier. -/
theorem IsCompact.uniformContinuousOn_rawFrontParam
    {lines : Set MarkedLine} (hlines : IsCompact lines) :
    UniformContinuousOn rawFrontParam
      (lines ×ˢ Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)) := by
  exact (hlines.prod isCompact_Icc).uniformContinuousOn_of_continuous
    continuous_rawFrontParam.continuousOn

/-- Quantitative form used in the marked discretization: for a prescribed
physical error, one marked-line radius works simultaneously for every point
of every unit segment in the compact family. -/
theorem IsCompact.exists_marked_radius_for_front
    {lines : Set MarkedLine} (hlines : IsCompact lines)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ rho : ℝ, 0 < rho ∧
      ∀ line ∈ lines, ∀ line' ∈ lines, dist line line' < rho →
        ∀ t ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ),
          dist (rawFrontParam (line, t)) (rawFrontParam (line', t)) < epsilon := by
  obtain ⟨rho, hrho, hcontrol⟩ := Metric.uniformContinuousOn_iff.mp
    (StickyKakeya4.IsCompact.uniformContinuousOn_rawFrontParam hlines)
      epsilon hepsilon
  refine ⟨rho, hrho, ?_⟩
  intro line hline line' hline' hdist t ht
  apply hcontrol (line, t) ⟨hline, ht⟩ (line', t) ⟨hline', ht⟩
  simpa [Prod.dist_eq] using hdist

/-- Every subset of a compact ambient marked-line family has a finite metric
net whose centers are chosen from the subset itself.  The centers therefore
retain the actual selector marks, even when the mark is not continuous in the
unmarked carrier coordinates. -/
theorem IsCompact.exists_finite_marked_net
    {ambient lines : Set MarkedLine} (hambient : IsCompact ambient)
    (hlines : lines ⊆ ambient) {δ : ℝ} (hδ : 0 < δ) :
    ∃ centers : Set MarkedLine,
      centers ⊆ lines ∧ centers.Finite ∧
        lines ⊆ ⋃ line ∈ centers, Metric.ball line δ := by
  have hclosure : IsCompact (closure lines) :=
    hambient.of_isClosed_subset isClosed_closure
      (closure_minimal hlines hambient.isClosed)
  exact exists_finite_cover_balls_of_isCompact_closure hclosure hδ

/-- Tie-broken finite disjointification.  The `i`-th cell keeps the `i`-th
set and removes all earlier sets.  For a finite marked ball cover this is the
measurable Voronoi substitute used to assign each retained line to exactly
one center. -/
def orderedMeasurableCell {X : Type*} {n : ℕ}
    (u : Fin n → Set X) (i : Fin n) : Set X :=
  u i \ ⋃ j, ⋃ (_ : j < i), u j

theorem measurableSet_orderedMeasurableCell
    {X : Type*} [MeasurableSpace X] {n : ℕ}
    (u : Fin n → Set X) (hu : ∀ i, MeasurableSet (u i)) (i : Fin n) :
    MeasurableSet (orderedMeasurableCell u i) := by
  exact (hu i).diff (MeasurableSet.iUnion fun j =>
    MeasurableSet.iUnion fun (_ : j < i) => hu j)

theorem orderedMeasurableCell_subset
    {X : Type*} {n : ℕ} (u : Fin n → Set X) (i : Fin n) :
    orderedMeasurableCell u i ⊆ u i := by
  intro x hx
  exact hx.1

theorem orderedMeasurableCell_pairwise_disjoint
    {X : Type*} {n : ℕ} (u : Fin n → Set X) :
    Pairwise (fun i j =>
      Disjoint (orderedMeasurableCell u i) (orderedMeasurableCell u j)) := by
  intro i j hij
  rcases lt_or_gt_of_ne hij with hij | hji
  · rw [Set.disjoint_left]
    intro x hxi hxj
    exact hxj.2 (Set.mem_iUnion.2
      ⟨i, Set.mem_iUnion.2 ⟨hij, hxi.1⟩⟩)
  · rw [Set.disjoint_left]
    intro x hxi hxj
    exact hxi.2 (Set.mem_iUnion.2
      ⟨j, Set.mem_iUnion.2 ⟨hji, hxj.1⟩⟩)

/-- The ordered cells neither lose nor add any point of the original finite
cover. -/
theorem iUnion_orderedMeasurableCell
    {X : Type*} {n : ℕ} (u : Fin n → Set X) :
    (⋃ i, orderedMeasurableCell u i) = ⋃ i, u i := by
  classical
  apply Set.Subset.antisymm
  · intro x hx
    simp only [Set.mem_iUnion] at hx ⊢
    obtain ⟨i, hi⟩ := hx
    exact ⟨i, hi.1⟩
  · intro x hx
    simp only [Set.mem_iUnion] at hx ⊢
    obtain ⟨i, hi⟩ := hx
    let s : Finset (Fin n) := Finset.univ.filter fun j => x ∈ u j
    have hs : s.Nonempty := by
      exact ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ i, hi⟩⟩
    let i0 : Fin n := s.min' hs
    have hi0s : i0 ∈ s := Finset.min'_mem s hs
    have hi0u : x ∈ u i0 := (Finset.mem_filter.1 hi0s).2
    refine ⟨i0, hi0u, ?_⟩
    intro hbefore
    simp only [Set.mem_iUnion] at hbefore
    obtain ⟨j, hji0, hju⟩ := hbefore
    have hjs : j ∈ s :=
      Finset.mem_filter.2 ⟨Finset.mem_univ j, hju⟩
    have hmin : i0 ≤ j := Finset.min'_le s j hjs
    exact (not_lt_of_ge hmin) hji0

/-- If a probability is supported on a finite measurable cover, the masses of
the tie-broken cells are honest weights whose total mass is one. -/
theorem tsum_measure_orderedMeasurableCell_eq_one
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsProbabilityMeasure μ] {n : ℕ}
    (u : Fin n → Set X) (hu : ∀ i, MeasurableSet (u i))
    (hsupport : μ ((⋃ i, u i)ᶜ) = 0) :
    (∑' i, μ (orderedMeasurableCell u i)) = 1 := by
  rw [← measure_iUnion (orderedMeasurableCell_pairwise_disjoint u)
    (measurableSet_orderedMeasurableCell u hu)]
  rw [iUnion_orderedMeasurableCell]
  let U : Set X := ⋃ i, u i
  have hU : MeasurableSet U := MeasurableSet.iUnion hu
  calc
    μ U = μ U + μ Uᶜ := by rw [hsupport, add_zero]
    _ = μ (U ∪ Uᶜ) := (measure_union disjoint_compl_right hU.compl).symm
    _ = μ Set.univ := by rw [Set.union_compl_self]
    _ = 1 := measure_univ

/-- The closed physical tube of radius `delta` around the unit segment of one
actual marked line.  Keeping the singleton `unitFront` in the definition makes
the affine mark part of the geometry rather than an auxiliary label. -/
def markedUnitTube (line : MarkedLine) (delta : ℝ) : Set E4 :=
  {x | Metric.infDist x (unitFront {line}) ≤ delta}

theorem measurableSet_markedUnitTube (line : MarkedLine) (delta : ℝ) :
    MeasurableSet (markedUnitTube line delta) := by
  exact measurableSet_le (Metric.continuous_infDist_pt _).measurable measurable_const

/-- The same Borel statement in the measurable-space instance carried by
Lebesgue volume, for direct use in source-mass integration. -/
theorem volumeMeasurableSet_markedUnitTube (line : MarkedLine) (delta : ℝ) :
    @MeasurableSet E4 (MeasureSpace.toMeasurableSpace : MeasurableSpace E4)
      (markedUnitTube line delta) := by
  exact measurableSet_le (Metric.continuous_infDist_pt _).measurable measurable_const

theorem mem_markedUnitTube_iff (line : MarkedLine) (delta : ℝ) (x : E4) :
    x ∈ markedUnitTube line delta ↔
      Metric.infDist x (unitFront {line}) ≤ delta := Iff.rfl

/-- Every point of the marked unit segment belongs to its physical front.
This is the elementary incidence fact used to place transverse balls inside
the corresponding marked tube. -/
theorem rawFrontParam_mem_unitFront_singleton (line : MarkedLine) {t : ℝ}
    (ht : t ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)) :
    rawFrontParam (line, t) ∈ unitFront {line} := by
  exact ⟨line, Set.mem_singleton line, t, ht, rfl⟩

/-- A metric ball about any point of the actual marked segment lies in the
closed physical tube of the same radius.  In particular this retains the
affine fibre mark exactly; no unmarked carrier surrogate is used. -/
theorem ball_rawFrontParam_subset_markedUnitTube (line : MarkedLine) {t delta : ℝ}
    (ht : t ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)) :
    Metric.ball (rawFrontParam (line, t)) delta ⊆ markedUnitTube line delta := by
  intro x hx
  exact (Metric.infDist_le_dist_of_mem
    (rawFrontParam_mem_unitFront_singleton line ht)).trans hx.le

/-- The tube contains a genuine four-dimensional ball about the midpoint of
the marked segment.  The later sharp `delta^3` estimate strengthens this by
packing order `delta⁻¹` disjoint such balls along the longitudinal parameter. -/
theorem volume_midpoint_ball_le_markedUnitTube (line : MarkedLine) (delta : ℝ) :
    volume (Metric.ball (rawFrontParam (line, 0)) delta) ≤
      volume (markedUnitTube line delta) := by
  apply measure_mono
  exact ball_rawFrontParam_subset_markedUnitTube line (t := 0) (delta := delta)
    (by norm_num)

/-- Longitudinal parameters with spacing `4 * delta`.  The offset by
`2 * delta` keeps every center away from the endpoints of the unit segment. -/
noncomputable def packedTime (delta : ℝ) (i : ℕ) : ℝ :=
  -(1 / 2 : ℝ) + (4 * (i : ℝ) + 2) * delta

/-- The finite family of radius-`delta` balls centered at the packed
longitudinal parameters of one actual marked segment. -/
def packedSegmentBalls (line : MarkedLine) (delta : ℝ) (N : ℕ) : Set E4 :=
  ⋃ i : Fin N, Metric.ball (rawFrontParam (line, packedTime delta i.val)) delta

theorem packedTime_mem_Icc {delta : ℝ} (hdelta : 0 ≤ delta) {N : ℕ}
    (hfit : (4 * (N : ℝ)) * delta ≤ 1) (i : Fin N) :
    packedTime delta i.val ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ) := by
  have hiNat : i.val + 1 ≤ N := Nat.succ_le_iff.mpr i.isLt
  have hiReal : (i.val : ℝ) + 1 ≤ (N : ℝ) := by
    exact_mod_cast hiNat
  have hiNonneg : (0 : ℝ) ≤ (i.val : ℝ) := by positivity
  constructor <;> unfold packedTime <;> nlinarith

/-- Along one valid marked line, physical distance at equal transverse
coordinates is exactly the difference of the longitudinal parameters. -/
theorem dist_rawFrontParam_same_line {line : MarkedLine}
    (hvalid : IsValidLine line) (s t : ℝ) :
    dist (rawFrontParam (line, s)) (rawFrontParam (line, t)) = |s - t| := by
  rw [dist_eq_norm]
  have hdiff :
      rawFrontParam (line, s) - rawFrontParam (line, t) =
        (s - t) • direction line := by
    simp only [rawFrontParam]
    module
  rw [hdiff, norm_smul, hvalid.1, mul_one]
  exact Real.norm_eq_abs (s - t)

theorem packedSegmentBalls_pairwise_disjoint {line : MarkedLine}
    (hvalid : IsValidLine line) {delta : ℝ} (hdelta : 0 ≤ delta) {N : ℕ} :
    Pairwise fun i j : Fin N =>
      Disjoint
        (Metric.ball (rawFrontParam (line, packedTime delta i.val)) delta)
        (Metric.ball (rawFrontParam (line, packedTime delta j.val)) delta) := by
  intro i j hij
  apply Metric.ball_disjoint_ball
  rw [dist_rawFrontParam_same_line hvalid]
  rcases lt_or_gt_of_ne hij with hijlt | hjilt
  · have hijNat : i.val + 1 ≤ j.val := Nat.succ_le_iff.mpr hijlt
    have hijReal : (i.val : ℝ) + 1 ≤ (j.val : ℝ) := by
      exact_mod_cast hijNat
    have hsep : 4 * delta ≤ packedTime delta j.val - packedTime delta i.val := by
      unfold packedTime
      nlinarith
    rw [abs_of_nonpos (by linarith)]
    nlinarith
  · have hjiNat : j.val + 1 ≤ i.val := Nat.succ_le_iff.mpr hjilt
    have hjiReal : (j.val : ℝ) + 1 ≤ (i.val : ℝ) := by
      exact_mod_cast hjiNat
    have hsep : 4 * delta ≤ packedTime delta i.val - packedTime delta j.val := by
      unfold packedTime
      nlinarith
    rw [abs_of_nonneg (by linarith)]
    nlinarith

theorem packedSegmentBalls_subset_markedUnitTube {line : MarkedLine}
    {delta : ℝ} (hdelta : 0 ≤ delta) {N : ℕ}
    (hfit : (4 * (N : ℝ)) * delta ≤ 1) :
    packedSegmentBalls line delta N ⊆ markedUnitTube line delta := by
  intro x hx
  simp only [packedSegmentBalls, Set.mem_iUnion] at hx
  obtain ⟨i, hxi⟩ := hx
  exact ball_rawFrontParam_subset_markedUnitTube line
    (packedTime_mem_Icc hdelta hfit i) hxi

/-- Borel measurability stated in the measurable-space instance carried by
`volume`.  This explicit form avoids the non-definitional measurable-space
diamond for `EuclideanSpace`. -/
theorem volumeMeasurableSet_ball (x : E4) (r : ℝ) :
    @MeasurableSet E4 (MeasureSpace.toMeasurableSpace : MeasurableSpace E4)
      (Metric.ball x r) := by
  exact Metric.isOpen_ball.measurableSet

theorem volume_packedSegmentBalls {line : MarkedLine}
    (hvalid : IsValidLine line) {delta : ℝ} (hdelta : 0 ≤ delta) (N : ℕ) :
    volume (packedSegmentBalls line delta N) =
      ∑' i : Fin N,
        volume (Metric.ball
          (rawFrontParam (line, packedTime delta i.val)) delta) := by
  unfold packedSegmentBalls
  rw [measure_iUnion (packedSegmentBalls_pairwise_disjoint hvalid hdelta)
    (fun i => volumeMeasurableSet_ball _ _)]

/-- The marked tube dominates the sum of the volumes of all longitudinally
packed balls.  This is the finite-additivity step behind the codimension-one
gain from `delta^4` to `delta^3`. -/
theorem tsum_packedBall_volume_le_markedUnitTube {line : MarkedLine}
    (hvalid : IsValidLine line) {delta : ℝ} (hdelta : 0 ≤ delta) {N : ℕ}
    (hfit : (4 * (N : ℝ)) * delta ≤ 1) :
    (∑' i : Fin N,
        volume (Metric.ball
          (rawFrontParam (line, packedTime delta i.val)) delta)) ≤
      volume (markedUnitTube line delta) := by
  rw [← volume_packedSegmentBalls hvalid hdelta N]
  exact measure_mono (packedSegmentBalls_subset_markedUnitTube hdelta hfit)

theorem volume_ball_E4 (x : E4) (r : ℝ) :
    volume (Metric.ball x r) =
      (ENNReal.ofReal r) ^ 4 * ENNReal.ofReal (Real.pi ^ 2 / 2) := by
  simpa using
    (InnerProductSpace.volume_ball_of_dim_even (E := E4) (k := 2)
      (by norm_num) x r)

/-- If a point of the marked segment lies within `3 delta / 2` of `x`, a
quarter-scale four-ball about that segment point lies simultaneously in the
actual marked tube and in the doubled physical ball.  This is the geometric
lower bound used by the local source readback. -/
theorem volume_quarterBall_le_markedUnitTube_inter_closedBall
    (line : MarkedLine) {t delta : ℝ}
    (ht : t ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ))
    (hdelta : 0 < delta) (x : E4)
    (hnear : dist (rawFrontParam (line, t)) x < 3 * delta / 2) :
    (ENNReal.ofReal (delta / 4)) ^ 4 *
        ENNReal.ofReal (Real.pi ^ 2 / 2) ≤
      volume (markedUnitTube line delta ∩ Metric.closedBall x (2 * delta)) := by
  rw [← volume_ball_E4 (rawFrontParam (line, t)) (delta / 4)]
  apply measure_mono
  intro y hy
  have hydelta : dist y (rawFrontParam (line, t)) < delta := by
    exact hy.trans_le (by linarith)
  refine ⟨ball_rawFrontParam_subset_markedUnitTube line ht hydelta, ?_⟩
  change dist y x ≤ 2 * delta
  exact (calc
    dist y x ≤ dist y (rawFrontParam (line, t)) +
        dist (rawFrontParam (line, t)) x := dist_triangle _ _ _
    _ < delta / 4 + 3 * delta / 2 := add_lt_add hy hnear
    _ ≤ 2 * delta := by linarith).le

/-- Equally spaced parameters used to cover the whole marked unit segment.
There is one more center than the natural floor of `delta⁻¹`, so the last
partial interval is retained without an endpoint convention. -/
noncomputable def coveringTime (delta : ℝ) (i : ℕ) : ℝ :=
  -(1 / 2 : ℝ) + (i : ℝ) * delta

/-- Every parameter of the unit segment is within `delta` of one of the
explicit covering parameters. -/
theorem exists_coveringTime {delta t : ℝ} (hdelta : 0 < delta)
    (ht : t ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)) :
    ∃ i : Fin (⌊delta⁻¹⌋₊ + 1),
      |t - coveringTime delta i.val| < delta := by
  let a : ℝ := (t + 1 / 2) / delta
  have ha : 0 ≤ a := by
    dsimp [a]
    exact div_nonneg (by linarith [ht.1]) hdelta.le
  have hupper : a ≤ delta⁻¹ := by
    dsimp [a]
    apply (div_le_iff₀ hdelta).2
    have htdelta : t + 1 / 2 ≤ 1 := by linarith [ht.2]
    have hinv : delta * delta⁻¹ = 1 := by
      exact mul_inv_cancel₀ (ne_of_gt hdelta)
    nlinarith
  let k : ℕ := ⌊a⌋₊
  have hkbound : k < ⌊delta⁻¹⌋₊ + 1 := by
    apply Nat.lt_succ_iff.mpr
    exact Nat.floor_mono hupper
  let i : Fin (⌊delta⁻¹⌋₊ + 1) := ⟨k, hkbound⟩
  refine ⟨i, ?_⟩
  have hkle : (k : ℝ) ≤ a := by
    dsimp [k]
    exact Nat.floor_le ha
  have halt : a < (k : ℝ) + 1 := by
    dsimp [k]
    exact Nat.lt_floor_add_one a
  dsimp [coveringTime, i]
  have hscale : t + 1 / 2 = a * delta := by
    dsimp [a]
    field_simp
  rw [abs_of_nonneg]
  · nlinarith
  · nlinarith

/-- The closed marked tube is covered by a controlled finite family of
four-balls.  Compact attainment of `infDist` is used here, so the statement
also covers points on the boundary of the closed tube. -/
theorem markedUnitTube_subset_coveringBalls {line : MarkedLine}
    (hvalid : IsValidLine line) {delta : ℝ} (hdelta : 0 < delta) :
    markedUnitTube line delta ⊆
      ⋃ i : Fin (⌊delta⁻¹⌋₊ + 1),
        Metric.ball (rawFrontParam (line, coveringTime delta i.val)) (2 * delta) := by
  intro x hx
  have hfrontCompact : IsCompact (unitFront ({line} : Set MarkedLine)) :=
    StickyKakeya4.IsCompact.unitFront isCompact_singleton
  have hfrontNonempty : (unitFront ({line} : Set MarkedLine)).Nonempty :=
    ⟨rawFrontParam (line, 0),
      rawFrontParam_mem_unitFront_singleton line (by norm_num)⟩
  obtain ⟨y, hy, hxy⟩ :=
    hfrontCompact.exists_infDist_eq_dist hfrontNonempty x
  rcases hy with ⟨line', hline', t, ht, rfl⟩
  have hline' : line' = line := by simpa using hline'
  subst line'
  change Metric.infDist x (unitFront {line}) =
    dist x (rawFrontParam (line, t)) at hxy
  obtain ⟨i, hi⟩ := exists_coveringTime hdelta ht
  refine Set.mem_iUnion.2 ⟨i, ?_⟩
  rw [Metric.mem_ball]
  calc
    dist x (rawFrontParam (line, coveringTime delta i.val)) ≤
        dist x (rawFrontParam (line, t)) +
          dist (rawFrontParam (line, t))
            (rawFrontParam (line, coveringTime delta i.val)) := dist_triangle _ _ _
    _ = dist x (rawFrontParam (line, t)) +
        |t - coveringTime delta i.val| := by
      rw [dist_rawFrontParam_same_line hvalid]
    _ < delta + delta := add_lt_add_of_le_of_lt (by rw [← hxy]; exact hx) hi
    _ = 2 * delta := by ring

theorem volume_markedUnitTube_le_coveringBalls {line : MarkedLine}
    (hvalid : IsValidLine line) {delta : ℝ} (hdelta : 0 < delta) :
    volume (markedUnitTube line delta) ≤
      ∑' i : Fin (⌊delta⁻¹⌋₊ + 1),
        volume (Metric.ball
          (rawFrontParam (line, coveringTime delta i.val)) (2 * delta)) := by
  calc
    volume (markedUnitTube line delta) ≤
        volume (⋃ i : Fin (⌊delta⁻¹⌋₊ + 1),
          Metric.ball
            (rawFrontParam (line, coveringTime delta i.val)) (2 * delta)) :=
      measure_mono (markedUnitTube_subset_coveringBalls hvalid hdelta)
    _ ≤ ∑' i : Fin (⌊delta⁻¹⌋₊ + 1),
        volume (Metric.ball
          (rawFrontParam (line, coveringTime delta i.val)) (2 * delta)) :=
      measure_iUnion_le _

theorem tsum_coveringBall_volume_eq_natCast_mul (line : MarkedLine)
    (delta : ℝ) :
    (∑' i : Fin (⌊delta⁻¹⌋₊ + 1),
        volume (Metric.ball
          (rawFrontParam (line, coveringTime delta i.val)) (2 * delta))) =
      ((⌊delta⁻¹⌋₊ + 1 : ℕ) : ENNReal) *
        (ENNReal.ofReal (2 * delta)) ^ 4 *
          ENNReal.ofReal (Real.pi ^ 2 / 2) := by
  rw [tsum_fintype]
  simp_rw [volume_ball_E4]
  simp [mul_assoc]

theorem coveringBall_count_mul_delta_le_two {delta : ℝ}
    (hdelta : 0 < delta) (hsmall : delta ≤ 1) :
    (((⌊delta⁻¹⌋₊ + 1 : ℕ) : ℝ) * delta) ≤ 2 := by
  have hinvNonneg : 0 ≤ delta⁻¹ := inv_nonneg.mpr hdelta.le
  have hfloor : ((⌊delta⁻¹⌋₊ : ℕ) : ℝ) ≤ delta⁻¹ :=
    Nat.floor_le hinvNonneg
  have hinvMul : delta⁻¹ * delta = 1 := by
    exact inv_mul_cancel₀ (ne_of_gt hdelta)
  have hone : delta ≤ 1 := hsmall
  push_cast
  nlinarith

/-- Uniform codimension-one upper volume bound for an actual marked tube.
Together with `volume_markedUnitTube_lower_bound`, this gives the two-sided
`delta^3` normalization used by the finite-scale source construction. -/
theorem volume_markedUnitTube_upper_bound {line : MarkedLine}
    (hvalid : IsValidLine line) {delta : ℝ} (hdelta : 0 < delta)
    (hsmall : delta ≤ 1) :
    volume (markedUnitTube line delta) ≤
      32 * (ENNReal.ofReal delta) ^ 3 *
        ENNReal.ofReal (Real.pi ^ 2 / 2) := by
  let N : ℕ := ⌊delta⁻¹⌋₊ + 1
  have hcountReal : (N : ℝ) * delta ≤ 2 := by
    simpa [N] using coveringBall_count_mul_delta_le_two hdelta hsmall
  have hcount : (N : ENNReal) * ENNReal.ofReal delta ≤ 2 := by
    have h := ENNReal.ofReal_le_ofReal hcountReal
    simpa [ENNReal.ofReal_mul (Nat.cast_nonneg N)] using h
  have hdeltaNonneg : 0 ≤ delta := hdelta.le
  calc
    volume (markedUnitTube line delta) ≤
        ∑' i : Fin (⌊delta⁻¹⌋₊ + 1),
          volume (Metric.ball
            (rawFrontParam (line, coveringTime delta i.val)) (2 * delta)) :=
      volume_markedUnitTube_le_coveringBalls hvalid hdelta
    _ = (N : ENNReal) * (ENNReal.ofReal (2 * delta)) ^ 4 *
          ENNReal.ofReal (Real.pi ^ 2 / 2) := by
      simpa [N] using tsum_coveringBall_volume_eq_natCast_mul line delta
    _ = ((N : ENNReal) * ENNReal.ofReal delta) *
          (16 * (ENNReal.ofReal delta) ^ 3 *
            ENNReal.ofReal (Real.pi ^ 2 / 2)) := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
      ring
    _ ≤ 2 * (16 * (ENNReal.ofReal delta) ^ 3 *
          ENNReal.ofReal (Real.pi ^ 2 / 2)) :=
      by simpa [mul_comm] using
        (mul_le_mul_right hcount
          (16 * (ENNReal.ofReal delta) ^ 3 *
            ENNReal.ofReal (Real.pi ^ 2 / 2)))
    _ = 32 * (ENNReal.ofReal delta) ^ 3 *
          ENNReal.ofReal (Real.pi ^ 2 / 2) := by ring

theorem tsum_packedBall_volume_eq {line : MarkedLine} (delta : ℝ) (N : ℕ) :
    (∑' i : Fin N,
        volume (Metric.ball
          (rawFrontParam (line, packedTime delta i.val)) delta)) =
      ∑ _i : Fin N,
        (ENNReal.ofReal delta) ^ 4 * ENNReal.ofReal (Real.pi ^ 2 / 2) := by
  rw [tsum_fintype]
  apply Finset.sum_congr rfl
  intro i _
  exact volume_ball_E4 _ _

/-- At every sufficiently small thickness there is an integral number of
longitudinal balls which both fits in the unit segment and is bounded below by
a constant multiple of `delta⁻¹`. -/
theorem exists_packedBall_count {delta : ℝ} (hdelta : 0 < delta)
    (hsmall : delta ≤ 1 / 8) :
    ∃ N : ℕ,
      (4 * (N : ℝ)) * delta ≤ 1 ∧
      1 ≤ (8 * (N : ℝ)) * delta := by
  let a : ℝ := (4 * delta)⁻¹
  let N : ℕ := ⌊a⌋₊
  have h4pos : 0 < 4 * delta := by positivity
  have haNonneg : 0 ≤ a := by
    dsimp [a]
    positivity
  have haMul : (4 * delta) * a = 1 := by
    dsimp [a]
    exact mul_inv_cancel₀ (ne_of_gt h4pos)
  have hNupper : (N : ℝ) ≤ a := by
    exact Nat.floor_le haNonneg
  have hNlower : a - 1 < (N : ℝ) := by
    exact Nat.sub_one_lt_floor a
  have haTwo : 2 ≤ a := by
    nlinarith
  have haHalf : a / 2 ≤ (N : ℝ) := by
    linarith
  refine ⟨N, ?_, ?_⟩
  · have hmul := mul_le_mul_of_nonneg_left hNupper h4pos.le
    nlinarith
  · have h8nonneg : 0 ≤ 8 * delta := by positivity
    have hmul := mul_le_mul_of_nonneg_left haHalf h8nonneg
    calc
      1 = (8 * delta) * (a / 2) := by nlinarith
      _ ≤ (8 * delta) * (N : ℝ) := hmul
      _ = (8 * (N : ℝ)) * delta := by ring

theorem tsum_packedBall_volume_eq_natCast_mul {line : MarkedLine}
    (delta : ℝ) (N : ℕ) :
    (∑' i : Fin N,
        volume (Metric.ball
          (rawFrontParam (line, packedTime delta i.val)) delta)) =
      (N : ENNReal) * (ENNReal.ofReal delta) ^ 4 *
        ENNReal.ofReal (Real.pi ^ 2 / 2) := by
  rw [tsum_packedBall_volume_eq]
  simp [mul_assoc]

/-- Sharp transverse-volume lower bound for a marked unit tube in four
dimensions.  The constant is explicit; the essential point is the power
`delta^3`, obtained from order `delta⁻¹` disjoint four-balls. -/
theorem volume_markedUnitTube_lower_bound {line : MarkedLine}
    (hvalid : IsValidLine line) {delta : ℝ} (hdelta : 0 < delta)
    (hsmall : delta ≤ 1 / 8) :
    ENNReal.ofReal (1 / 8 : ℝ) * (ENNReal.ofReal delta) ^ 3 *
        ENNReal.ofReal (Real.pi ^ 2 / 2) ≤
      volume (markedUnitTube line delta) := by
  obtain ⟨N, hfit, hcount⟩ := exists_packedBall_count hdelta hsmall
  have hbaseReal : (1 / 8 : ℝ) ≤ (N : ℝ) * delta := by
    nlinarith
  have hbase :
      ENNReal.ofReal (1 / 8 : ℝ) ≤
        (N : ENNReal) * ENNReal.ofReal delta := by
    have h := ENNReal.ofReal_le_ofReal hbaseReal
    simpa [ENNReal.ofReal_mul (Nat.cast_nonneg N)] using h
  have hscale :
      ENNReal.ofReal (1 / 8 : ℝ) * (ENNReal.ofReal delta) ^ 3 ≤
        (N : ENNReal) * (ENNReal.ofReal delta) ^ 4 := by
    have h := mul_le_mul_left hbase ((ENNReal.ofReal delta) ^ 3)
    simpa [pow_succ, mul_assoc, mul_left_comm, mul_comm] using h
  calc
    ENNReal.ofReal (1 / 8 : ℝ) * (ENNReal.ofReal delta) ^ 3 *
          ENNReal.ofReal (Real.pi ^ 2 / 2)
        ≤ (N : ENNReal) * (ENNReal.ofReal delta) ^ 4 *
          ENNReal.ofReal (Real.pi ^ 2 / 2) :=
      mul_le_mul_left hscale _
    _ = ∑' i : Fin N,
          volume (Metric.ball
            (rawFrontParam (line, packedTime delta i.val)) delta) :=
      (tsum_packedBall_volume_eq_natCast_mul delta N).symm
    _ ≤ volume (markedUnitTube line delta) :=
      tsum_packedBall_volume_le_markedUnitTube hvalid hdelta.le hfit

/-- The sharp `delta^3` tube bound supplies the weaker
`delta^(3 + epsilon)` shading normalization uniformly below one positive
cutoff depending only on `epsilon`. -/
theorem exists_markedUnitTube_admissible_scale {epsilon : ℝ}
    (hepsilon : 0 < epsilon) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (line : MarkedLine), IsValidLine line →
      ∀ delta : ℝ, 0 < delta → delta ≤ delta0 →
        (ENNReal.ofReal delta).rpow (3 + epsilon) ≤
          volume (markedUnitTube line delta) := by
  let delta0 : ℝ :=
    min (1 / 8 : ℝ) ((1 / 2 : ℝ) ^ (1 / epsilon : ℝ))
  have hhalfpos : (0 : ℝ) < 1 / 2 := by norm_num
  have hrootpos : (0 : ℝ) < (1 / 2 : ℝ) ^ (1 / epsilon : ℝ) :=
    Real.rpow_pos_of_pos hhalfpos _
  have hdelta0 : 0 < delta0 := by
    exact lt_min (by norm_num) hrootpos
  refine ⟨delta0, hdelta0, ?_⟩
  intro line hvalid delta hdelta hle
  have hsmall : delta ≤ 1 / 8 :=
    hle.trans (min_le_left _ _)
  have hroot : delta ≤ (1 / 2 : ℝ) ^ (1 / epsilon : ℝ) :=
    hle.trans (min_le_right _ _)
  have hrootPow :
      ((1 / 2 : ℝ) ^ (1 / epsilon : ℝ)) ^ epsilon = 1 / 2 := by
    calc
      ((1 / 2 : ℝ) ^ (1 / epsilon : ℝ)) ^ epsilon =
          (1 / 2 : ℝ) ^ ((1 / epsilon : ℝ) * epsilon) :=
        (Real.rpow_mul hhalfpos.le _ _).symm
      _ = (1 / 2 : ℝ) ^ (1 : ℝ) := by
        congr 1
        field_simp
      _ = 1 / 2 := by simp
  have hrpowReal : delta ^ epsilon ≤ (1 / 2 : ℝ) := by
    calc
      delta ^ epsilon ≤ ((1 / 2 : ℝ) ^ (1 / epsilon : ℝ)) ^ epsilon :=
        Real.rpow_le_rpow hdelta.le hroot hepsilon.le
      _ = 1 / 2 := hrootPow
  have hrpowENN :
      (ENNReal.ofReal delta).rpow epsilon ≤ ENNReal.ofReal (1 / 2 : ℝ) := by
    change ENNReal.ofReal delta ^ epsilon ≤ ENNReal.ofReal (1 / 2 : ℝ)
    rw [ENNReal.ofReal_rpow_of_pos hdelta]
    exact ENNReal.ofReal_le_ofReal hrpowReal
  have hconstReal :
      (1 / 2 : ℝ) ≤ (1 / 8 : ℝ) * (Real.pi ^ 2 / 2) := by
    nlinarith [Real.pi_gt_three]
  have hconstENN :
      ENNReal.ofReal (1 / 2 : ℝ) ≤
        ENNReal.ofReal (1 / 8 : ℝ) *
          ENNReal.ofReal (Real.pi ^ 2 / 2) := by
    have h := ENNReal.ofReal_le_ofReal hconstReal
    simpa [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 8)] using h
  have hscaledRpow :=
    mul_le_mul_right hrpowENN ((ENNReal.ofReal delta) ^ 3)
  have hscaledConst :=
    mul_le_mul_right hconstENN ((ENNReal.ofReal delta) ^ 3)
  have hpower :
      (ENNReal.ofReal delta).rpow (3 + epsilon) ≤
        ENNReal.ofReal (1 / 8 : ℝ) * (ENNReal.ofReal delta) ^ 3 *
          ENNReal.ofReal (Real.pi ^ 2 / 2) := by
    change ENNReal.ofReal delta ^ (3 + epsilon) ≤
      ENNReal.ofReal (1 / 8 : ℝ) * (ENNReal.ofReal delta) ^ 3 *
        ENNReal.ofReal (Real.pi ^ 2 / 2)
    rw [ENNReal.rpow_add_of_nonneg 3 epsilon (by norm_num) hepsilon.le]
    exact le_trans
      (by simpa [mul_assoc, mul_left_comm, mul_comm] using hscaledRpow)
      (by simpa [mul_assoc, mul_left_comm, mul_comm] using hscaledConst)
  exact hpower.trans (volume_markedUnitTube_lower_bound hvalid hdelta hsmall)

end StickyKakeya4
