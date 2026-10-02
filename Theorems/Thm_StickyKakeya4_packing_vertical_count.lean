import Theorems.Thm_StickyKakeya4_packing_reference_overlap

open Filter MeasureTheory Set Metric
open scoped ENNReal Topology

namespace StickyKakeya4

attribute [local instance] Classical.propDecidable

/-!
A vertical counting estimate for supported reference nets, obtained from an
actual measure on the carrier.  The count uses lower masses of the original
reference balls, a cubic upper bound on their direction marginal, and uniform
overlap.  Covering a smaller supported set then uses the same reference balls;
no lower bound on the mass of a restricted cell is claimed or needed.
-/

/-- Lower masses and bounded overlap control the number of reference centers
whose images lie in one direction ball.  A `1`-Lipschitz direction map sends
all their radius-`tau` balls into the direction ball of radius `2 * tau`. -/
theorem direction_ball_card_mul_le_of_mass_lower_and_overlap
    {E Y : Type*} [PseudoMetricSpace E] [MeasurableSpace E] [BorelSpace E]
    [PseudoMetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (nu : Measure E) (q : E → Y) (hq : Measurable q) (hlip : LipschitzWith 1 q)
    (centers : Finset E) (tau : ℝ) (htau : 0 < tau) (theta : Y)
    (c D : ENNReal) (zeta : ℝ) (K : ℕ)
    (hlower : ∀ x ∈ centers,
      c * (ENNReal.ofReal tau).rpow (3 + zeta) ≤ nu (Metric.ball x tau))
    (hoverlap : ∀ p : E,
      (centers.filter fun x => p ∈ Metric.ball x tau).card ≤ K)
    (hdirection : nu.map q (Metric.ball theta (2 * tau)) ≤
      D * (ENNReal.ofReal (2 * tau)) ^ (3 : ℕ)) :
    ((centers.filter fun x => q x ∈ Metric.ball theta tau).card : ENNReal) *
        c * (ENNReal.ofReal tau).rpow (3 + zeta) ≤
      (8 * (K : ENNReal) * D) * (ENNReal.ofReal tau) ^ (3 : ℕ) := by
  classical
  let selected : Finset E := centers.filter fun x => q x ∈ Metric.ball theta tau
  have hselected : selected ⊆ centers := Finset.filter_subset _ _
  have hcontained : ∀ x ∈ selected,
      Metric.ball x tau ⊆ q ⁻¹' Metric.ball theta (2 * tau) := by
    intro x hx y hy
    have hxTheta : dist (q x) theta < tau := (Finset.mem_filter.mp hx).2
    have hyx : dist y x < tau := hy
    change dist (q y) theta < 2 * tau
    have hlipDist : dist (q y) (q x) ≤ dist y x := by
      simpa using hlip.dist_le_mul y x
    calc
      dist (q y) theta ≤ dist (q y) (q x) + dist (q x) theta := dist_triangle _ _ _
      _ ≤ dist y x + dist (q x) theta := add_le_add hlipDist le_rfl
      _ < tau + tau := add_lt_add hyx hxTheta
      _ = 2 * tau := by ring
  have hselectedOverlap : ∀ p : E,
      (selected.filter fun x => p ∈ Metric.ball x tau).card ≤ K := by
    intro p
    calc
      (selected.filter fun x => p ∈ Metric.ball x tau).card ≤
          (centers.filter fun x => p ∈ Metric.ball x tau).card := by
        apply Finset.card_le_card
        exact Finset.filter_subset_filter _ hselected
      _ ≤ K := hoverlap p
  have hcount := card_mul_le_mul_measure_of_mass_lower_and_overlap nu selected
    (fun x => Metric.ball x tau) (q ⁻¹' Metric.ball theta (2 * tau))
    (c * (ENNReal.ofReal tau).rpow (3 + zeta)) K
    (fun _ _ => measurableSet_ball) hcontained
    (fun x hx => hlower x (hselected hx)) hselectedOverlap
  calc
    ((centers.filter fun x => q x ∈ Metric.ball theta tau).card : ENNReal) *
        c * (ENNReal.ofReal tau).rpow (3 + zeta) ≤
        (K : ENNReal) * nu (q ⁻¹' Metric.ball theta (2 * tau)) := by
      simpa only [selected, mul_assoc] using hcount
    _ = (K : ENNReal) * nu.map q (Metric.ball theta (2 * tau)) := by
      rw [Measure.map_apply hq measurableSet_ball]
    _ ≤ (K : ENNReal) * (D * (ENNReal.ofReal (2 * tau)) ^ (3 : ℕ)) :=
      mul_le_mul' le_rfl hdirection
    _ = (8 * (K : ENNReal) * D) * (ENNReal.ofReal tau) ^ (3 : ℕ) := by
      rw [show 2 * tau = tau * 2 by ring, ENNReal.ofReal_mul htau.le, mul_pow]
      norm_num
      ac_rfl

/-- Cancellation of the common cubic scale converts the weighted count into
its vertical exponent.  Positivity and finiteness are required only for the
lower-mass coefficient and the radius, not for the upper coefficient. -/
theorem ennreal_cubic_reference_power_cancel
    {n C c : ENNReal} (hc : 0 < c) (hctop : c ≠ ⊤)
    {tau : ℝ} (htau : 0 < tau) (zeta : ℝ)
    (hbound : n * c * (ENNReal.ofReal tau).rpow (3 + zeta) ≤
      C * (ENNReal.ofReal tau) ^ (3 : ℕ)) :
    n ≤ (C / c) * (ENNReal.ofReal tau).rpow (-zeta) := by
  have htauZero : ENNReal.ofReal tau ≠ 0 := (ENNReal.ofReal_pos.mpr htau).ne'
  have hpowZero : (ENNReal.ofReal tau).rpow (3 + zeta) ≠ 0 :=
    (ENNReal.rpow_pos (ENNReal.ofReal_pos.mpr htau) ENNReal.ofReal_ne_top).ne'
  have hpowTop : (ENNReal.ofReal tau).rpow (3 + zeta) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_ne_zero htauZero ENNReal.ofReal_ne_top
  apply (ENNReal.mul_le_mul_iff_left (mul_ne_zero hc.ne' hpowZero)
    (ENNReal.mul_ne_top hctop hpowTop)).mp
  calc
    n * (c * (ENNReal.ofReal tau).rpow (3 + zeta)) ≤
        C * (ENNReal.ofReal tau) ^ (3 : ℕ) := by simpa only [mul_assoc] using hbound
    _ = ((C / c) * (ENNReal.ofReal tau).rpow (-zeta)) *
        (c * (ENNReal.ofReal tau).rpow (3 + zeta)) := by
      symm
      calc
        ((C / c) * (ENNReal.ofReal tau).rpow (-zeta)) *
            (c * (ENNReal.ofReal tau).rpow (3 + zeta)) =
            ((C / c) * c) * ((ENNReal.ofReal tau).rpow (-zeta) *
              (ENNReal.ofReal tau).rpow (3 + zeta)) := by ac_rfl
        _ = C * (ENNReal.ofReal tau).rpow (-zeta + (3 + zeta)) := by
          rw [ENNReal.div_mul_cancel hc.ne' hctop]
          exact congrArg (fun x : ENNReal => C * x)
            (ENNReal.rpow_add (-zeta) (3 + zeta) htauZero ENNReal.ofReal_ne_top).symm
        _ = C * (ENNReal.ofReal tau) ^ (3 : ℕ) := by
          rw [show -zeta + (3 + zeta) = (3 : ℝ) by ring]
          exact congrArg (fun x : ENNReal => C * x)
            (ENNReal.rpow_natCast (ENNReal.ofReal tau) 3)

/-- A cubic upper bound for the direction marginal and a uniform lower mass
for separated reference balls give a single finite vertical-count constant
valid at every positive scale.  Its value is `8 * K * D / c`, where `K` is the
uniform geometric overlap constant of the ambient normed space. -/
theorem exists_uniform_vertical_reference_count_bound
    {E Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    [MeasurableSpace E] [BorelSpace E]
    [PseudoMetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (nu : Measure E) (q : E → Y) (hq : Measurable q) (hlip : LipschitzWith 1 q)
    (c D : ENNReal) (hc : 0 < c) (hctop : c ≠ ⊤) (hDtop : D ≠ ⊤)
    (zeta : ℝ)
    (hdirection : ∀ (theta : Y) (r : ℝ), 0 < r →
      nu.map q (Metric.ball theta r) ≤ D * (ENNReal.ofReal r) ^ (3 : ℕ)) :
    ∃ A : ENNReal, A ≠ ⊤ ∧ ∀ (tau : ℝ), 0 < tau → ∀ centers : Finset E,
      (∀ x ∈ centers, ∀ y ∈ centers, x ≠ y → tau / 2 ≤ dist x y) →
      (∀ x ∈ centers,
        c * (ENNReal.ofReal tau).rpow (3 + zeta) ≤ nu (Metric.ball x tau)) →
      ∀ theta : Y,
        ((centers.filter fun x => q x ∈ Metric.ball theta tau).card : ENNReal) ≤
          A * (ENNReal.ofReal tau).rpow (-zeta) := by
  obtain ⟨K, hK⟩ := exists_uniform_separated_ball_overlap_bound E
  let A : ENNReal := (8 * (K : ENNReal) * D) / c
  have hAtop : A ≠ ⊤ := by
    apply ENNReal.div_ne_top _ hc.ne'
    exact ENNReal.mul_ne_top (by finiteness) hDtop
  refine ⟨A, hAtop, ?_⟩
  intro tau htau centers hsep hlower theta
  apply ennreal_cubic_reference_power_cancel hc hctop htau zeta
  exact direction_ball_card_mul_le_of_mass_lower_and_overlap
    nu q hq hlip centers tau htau theta c D zeta K hlower
    (hK tau htau centers hsep) (hdirection theta (2 * tau) (by positivity))

/-- An already constructed reference cover covers every subset without any
new measure lower bound.  This is the support heredity used when the source
measure is subsequently restricted. -/
theorem coversAtRadius_mono_set
    {X : Type*} [PseudoMetricSpace X] {s t : Set X} (hts : t ⊆ s)
    {tau : ℝ} {centers : Finset X} (hcover : coversAtRadius s tau centers) :
    coversAtRadius t tau centers := fun _ hx => hcover (hts hx)

/-- Discarding reference balls that miss a hereditary subset leaves a cover
of that subset and preserves every vertical support-count bound.  The retained
centers are still chosen from the original references; no restricted-source
cell-mass lower bound occurs in the statement. -/
theorem exists_hereditary_reference_subfamily_with_vertical_count
    {E Y : Type*} [PseudoMetricSpace E] [PseudoMetricSpace Y]
    (s t : Set E) (hts : t ⊆ s) (tau : ℝ) (centers : Finset E)
    (hcover : coversAtRadius s tau centers)
    (q : E → Y) (A : ENNReal) (zeta : ℝ)
    (hcount : ∀ theta : Y,
      ((centers.filter fun x => q x ∈ Metric.ball theta tau).card : ENNReal) ≤
        A * (ENNReal.ofReal tau).rpow (-zeta)) :
    ∃ retained : Finset E, retained ⊆ centers ∧
      coversAtRadius t tau retained ∧
      (∀ x ∈ retained, ∃ y ∈ t, y ∈ Metric.ball x tau) ∧
      ∀ theta : Y,
        ((retained.filter fun x => q x ∈ Metric.ball theta tau).card : ENNReal) ≤
          A * (ENNReal.ofReal tau).rpow (-zeta) := by
  classical
  let retained : Finset E := centers.filter fun x => ∃ y ∈ t, y ∈ Metric.ball x tau
  have hretained : retained ⊆ centers := Finset.filter_subset _ _
  refine ⟨retained, hretained, ?_, ?_, ?_⟩
  · intro y hy
    obtain ⟨x, hx⟩ := Set.mem_iUnion.mp (hcover (hts hy))
    obtain ⟨hxCenters, hyx⟩ := Set.mem_iUnion.mp hx
    apply Set.mem_iUnion.mpr
    refine ⟨x, Set.mem_iUnion.mpr ⟨?_, hyx⟩⟩
    exact Finset.mem_filter.mpr ⟨hxCenters, y, hy, hyx⟩
  · intro x hx
    exact (Finset.mem_filter.mp hx).2
  · intro theta
    apply le_trans _ (hcount theta)
    exact_mod_cast Finset.card_le_card
      (Finset.filter_subset_filter (fun x => q x ∈ Metric.ball theta tau) hretained)

end StickyKakeya4
