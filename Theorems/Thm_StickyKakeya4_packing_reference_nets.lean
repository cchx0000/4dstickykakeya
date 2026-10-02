import Theorems.Thm_StickyKakeya4_wz_carrier_pruning

open Filter MeasureTheory Set Metric
open scoped ENNReal Topology

namespace StickyKakeya4

/-!
Actual supported metric nets extracted from the finite-cover witnesses in a
covering-number estimate.  In particular, centers in the ambient space are
replaced by points of the carrier before taking a maximal separated family.
The number of retained points never exceeds the cardinality of the original
cover.  All statements hold in a pseudometric space.
-/

/-- A finite open-ball cover can be recentered on the set it covers, at the
cost of doubling the radius and with no increase in the number of centers.
Empty intersections with the carrier are discarded. -/
theorem exists_supported_cover_of_finite_cover
    {X : Type*} [PseudoMetricSpace X]
    (s : Set X) (r : ℝ) (centers : Finset X)
    (hcover : coversAtRadius s r centers) :
    ∃ supported : Finset X,
      (∀ x ∈ supported, x ∈ s) ∧
      supported.card ≤ centers.card ∧
      coversAtRadius s (2 * r) supported := by
  classical
  let occupied : Finset X := centers.filter fun c => ∃ x ∈ s, dist x c < r
  have hoccupied (c : occupied) : ∃ x ∈ s, dist x (c : X) < r :=
    (Finset.mem_filter.mp c.property).2
  let representative : occupied → X := fun c => Classical.choose (hoccupied c)
  have hrepresentative (c : occupied) :
      representative c ∈ s ∧ dist (representative c) (c : X) < r :=
    Classical.choose_spec (hoccupied c)
  let supported : Finset X := occupied.attach.image representative
  refine ⟨supported, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨c, _hc, rfl⟩ := Finset.mem_image.mp hx
    exact (hrepresentative c).1
  · calc
      supported.card ≤ occupied.attach.card := Finset.card_image_le
      _ = occupied.card := Finset.card_attach
      _ ≤ centers.card := Finset.card_filter_le _ _
  · intro x hx
    obtain ⟨c, hc⟩ := Set.mem_iUnion.mp (hcover hx)
    obtain ⟨hcCenters, hxc⟩ := Set.mem_iUnion.mp hc
    have hxcDist : dist x c < r := Metric.mem_ball.mp hxc
    have hcOccupied : c ∈ occupied :=
      Finset.mem_filter.mpr ⟨hcCenters, x, hx, hxcDist⟩
    let c' : occupied := ⟨c, hcOccupied⟩
    have hcSupported : representative c' ∈ supported :=
      Finset.mem_image.mpr ⟨c', Finset.mem_attach _ _, rfl⟩
    apply Set.mem_iUnion.mpr
    refine ⟨representative c', Set.mem_iUnion.mpr ⟨hcSupported, ?_⟩⟩
    rw [Metric.mem_ball]
    calc
      dist x (representative c') ≤ dist x c + dist c (representative c') :=
        dist_triangle _ _ _
      _ < r + r := add_lt_add hxcDist (by
        simpa only [dist_comm] using (hrepresentative c').2)
      _ = 2 * r := by ring

/-- From an ambient finite cover at radius `tau / 4`, obtain a net supported
on the carrier, separated by `tau / 2`, covering at the open radius `tau`,
and no larger than the original family of centers. -/
theorem exists_supported_separated_net_of_finite_cover
    {X : Type*} [PseudoMetricSpace X]
    (s : Set X) {tau : ℝ} (htau : 0 < tau)
    (centers : Finset X)
    (hcover : coversAtRadius s (tau / 4) centers) :
    ∃ net : Finset X,
      (∀ x ∈ net, x ∈ s) ∧
      (∀ x ∈ net, ∀ y ∈ net, x ≠ y → tau / 2 ≤ dist x y) ∧
      coversAtRadius s tau net ∧ net.card ≤ centers.card := by
  obtain ⟨supported, hsupported, hcard, hcoverSupported⟩ :=
    exists_supported_cover_of_finite_cover s (tau / 4) centers hcover
  obtain ⟨net, hsubset, hseparated, hnet⟩ :=
    exists_maximal_image_separated_subfamily supported id
      (show 0 < tau / 2 by positivity)
  refine ⟨net, fun x hx => hsupported x (hsubset hx), hseparated, ?_,
    (Finset.card_le_card hsubset).trans hcard⟩
  intro x hx
  obtain ⟨c, hc⟩ := Set.mem_iUnion.mp (hcoverSupported hx)
  obtain ⟨hcSupported, hxc⟩ := Set.mem_iUnion.mp hc
  obtain ⟨y, hy, hcy⟩ := hnet c hcSupported
  apply Set.mem_iUnion.mpr
  refine ⟨y, Set.mem_iUnion.mpr ⟨hy, ?_⟩⟩
  rw [Metric.mem_ball]
  calc
    dist x y ≤ dist x c + dist c y := dist_triangle _ _ _
    _ < 2 * (tau / 4) + tau / 2 :=
      add_lt_add (Metric.mem_ball.mp hxc) hcy
    _ = tau := by ring

/-- A finite non-strict covering-number bound produces a supported,
separated net.  The only cardinal loss is the unit already used when
extracting a finite cover from the defining infimum. -/
theorem coveringNumber_le_extract_supported_separated_net
    {X : Type*} [PseudoMetricSpace X]
    (s : Set X) {tau : ℝ} (htau : 0 < tau) {B : ENNReal}
    (hB : B ≠ ⊤) (hbound : coveringNumber s (tau / 4) ≤ B) :
    ∃ net : Finset X,
      (∀ x ∈ net, x ∈ s) ∧
      (∀ x ∈ net, ∀ y ∈ net, x ≠ y → tau / 2 ≤ dist x y) ∧
      coversAtRadius s tau net ∧ (net.card : ENNReal) < B + 1 := by
  obtain ⟨centers, hcover, hcard⟩ :=
    coveringNumber_le_extract_finset_cover s (tau / 4) hB hbound
  obtain ⟨net, hsupported, hseparated, hnet, hcardNet⟩ :=
    exists_supported_separated_net_of_finite_cover s htau centers hcover
  refine ⟨net, hsupported, hseparated, hnet, ?_⟩
  exact lt_of_le_of_lt (by exact_mod_cast hcardNet) hcard

/-- Simultaneous supported-net extraction at an arbitrary family of positive
scales.  This supplies actual finite reference sets, rather than assuming
that covering-number estimates are already attained by supported centers. -/
theorem coveringNumber_bounds_extract_supported_separated_nets
    {X I : Type*} [PseudoMetricSpace X]
    (s : Set X) (tau : I → ℝ) (B : I → ENNReal)
    (htau : ∀ i, 0 < tau i) (hB : ∀ i, B i ≠ ⊤)
    (hbound : ∀ i, coveringNumber s (tau i / 4) ≤ B i) :
    ∃ nets : I → Finset X, ∀ i,
      (∀ x ∈ nets i, x ∈ s) ∧
      (∀ x ∈ nets i, ∀ y ∈ nets i, x ≠ y → tau i / 2 ≤ dist x y) ∧
      coversAtRadius s (tau i) (nets i) ∧
      ((nets i).card : ENNReal) < B i + 1 := by
  classical
  exact Classical.axiom_of_choice fun i =>
    coveringNumber_le_extract_supported_separated_net s (htau i) (hB i) (hbound i)

/-- The finite references obtained from a nonempty carrier cannot be empty.
This is independent of the radius and of the separation property. -/
theorem finset_nonempty_of_coversAtRadius
    {X : Type*} [PseudoMetricSpace X]
    {s : Set X} (hs : s.Nonempty) {r : ℝ} {centers : Finset X}
    (hcover : coversAtRadius s r centers) : centers.Nonempty := by
  obtain ⟨x, hx⟩ := hs
  obtain ⟨c, hc⟩ := Set.mem_iUnion.mp (hcover hx)
  obtain ⟨hcCenters, _hxc⟩ := Set.mem_iUnion.mp hc
  exact ⟨c, hcCenters⟩

end StickyKakeya4
