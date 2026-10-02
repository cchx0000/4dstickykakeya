import Theorems.Thm_StickyKakeya4_actual_slope_source
import Theorems.Thm_StickyKakeya4_collision_edge_contact_residual
import Theorems.Thm_StickyKakeya4_compact_front
import Theorems.Thm_StickyKakeya4_markov_endpoint_preservation
import Theorems.Thm_StickyKakeya4_finite_hausdorff_ball_cover

/-!
# Exact fractional routing through small physical balls

The old occurrence space is an arbitrary measurable space. A fresh uniform
parameter chooses a time in the quarter of the true common slab opposite the
old time. A finite first-hit partition is projected back to the entire old
occurrence, so all inherited labels remain untouched.
-/

open Filter MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace StickyKakeya4.HausdorffBushRouting

open ActualSlopeSource

/-- Fresh uniform probability on the closed unit interval. -/
def unitTime : Measure ℝ := volume.restrict (Icc 0 1)

instance : IsProbabilityMeasure unitTime where
  measure_univ := by simp [unitTime, Real.volume_Icc]

/-- The quarter-slab endpoint farthest from the inherited time. -/
def quarterStart (u v t : ℝ) : ℝ :=
  if (u + v) / 2 ≤ t then u else v - (v - u) / 4

/-- The newly sampled time; the inherited time is only read, never changed. -/
def sampledTime (u v t z : ℝ) : ℝ :=
  quarterStart u v t + (v - u) * z / 4

theorem measurable_quarterStart {Ω : Type*} [MeasurableSpace Ω]
    (u v : ℝ) {t : Ω → ℝ} (ht : Measurable t) :
    Measurable (fun ω => quarterStart u v (t ω)) := by
  unfold quarterStart
  exact Measurable.ite (measurableSet_le measurable_const ht)
    measurable_const measurable_const

theorem measurable_sampledTime {Ω : Type*} [MeasurableSpace Ω]
    (u v : ℝ) {t : Ω → ℝ} (ht : Measurable t) :
    Measurable (fun p : Ω × ℝ => sampledTime u v (t p.1) p.2) := by
  unfold sampledTime
  exact ((measurable_quarterStart u v ht).comp measurable_fst).add
    ((measurable_const.mul measurable_snd).div_const 4)

theorem sampledTime_mem_slab {u v t z : ℝ} (huv : u < v)
    (hz : z ∈ Icc (0 : ℝ) 1) : sampledTime u v t z ∈ Icc u v := by
  rcases hz with ⟨hz0, hz1⟩
  have hzL : 0 ≤ (v - u) * z := mul_nonneg (by linarith) hz0
  have hzU : (v - u) * z ≤ v - u := by nlinarith
  unfold sampledTime quarterStart
  split_ifs <;> constructor <;> linarith

theorem sampledTime_separated {u v t z : ℝ} (huv : u < v)
    (hz : z ∈ Icc (0 : ℝ) 1) :
    (v - u) / 4 ≤ |sampledTime u v t z - t| := by
  rcases hz with ⟨hz0, hz1⟩
  have hzL : 0 ≤ (v - u) * z := mul_nonneg (by linarith) hz0
  have hzU : (v - u) * z ≤ v - u := by nlinarith
  unfold sampledTime quarterStart
  split_ifs with h
  · rw [abs_of_nonpos] <;> linarith
  · rw [abs_of_nonneg] <;> linarith

theorem measurable_heightPoint {Ω : Type*} [MeasurableSpace Ω]
    {x : Ω → E3} {s : Ω → ℝ} (hx : Measurable x) (hs : Measurable s) :
    Measurable (fun ω => heightPoint (x ω) (s ω)) := by
  apply (WithLp.measurable_toLp 2 (Fin 4 → ℝ)).comp
  apply measurable_pi_lambda
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa only [Fin.lastCases_last] using hs
  · simpa only [Fin.lastCases_castSucc, Function.comp_def] using
      ((PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) j).measurable.comp hx)

/-- The actual physical front point at the fresh time. -/
def sampledPoint {Ω : Type*} (a b : Ω → E3) (t : Ω → ℝ)
    (u v : ℝ) (p : Ω × ℝ) : E4 :=
  heightPoint (b p.1 + sampledTime u v (t p.1) p.2 • a p.1)
    (sampledTime u v (t p.1) p.2)

theorem measurable_sampledPoint {Ω : Type*} [MeasurableSpace Ω]
    {a b : Ω → E3} {t : Ω → ℝ} (ha : Measurable a)
    (hb : Measurable b) (ht : Measurable t) (u v : ℝ) :
    Measurable (sampledPoint a b t u v) := by
  exact measurable_heightPoint
    ((hb.comp measurable_fst).add
      ((measurable_sampledTime u v ht).smul (ha.comp measurable_fst)))
    (measurable_sampledTime u v ht)

/-- Ambient ball membership controls the literal fourth coordinate. -/
theorem height_distance_lt_of_ball {x : E3} {s R : ℝ} {c : E4}
    (h : heightPoint x s ∈ Metric.ball c R) :
    |s - c (Fin.last 3)| < R := by
  have hnorm := PiLp.norm_apply_le (heightPoint x s - c) (Fin.last 3)
  have hd : ‖heightPoint x s - c‖ < R := by
    simpa only [Metric.mem_ball, dist_eq_norm] using h
  have hcoord : |s - c (Fin.last 3)| ≤ ‖heightPoint x s - c‖ := by
    change |heightPoint x s (Fin.last 3) - c (Fin.last 3)| ≤ _ at hnorm
    rw [heightPoint_last] at hnorm
    exact hnorm
  exact hcoord.trans_lt hd

@[simp] theorem horizontalProjection_heightPoint (x : E3) (s : ℝ) :
    horizontalProjection (heightPoint x s) = x := by
  ext i
  simp

/-- A physical ball hit places the original graph source in the bush at the
ball's height, with error twice the ball radius. -/
theorem bush_error_lt_of_ball {a b : E3} {s R : ℝ} {c : E4}
    (ha : ‖a‖ ≤ 1)
    (h : heightPoint (b + s • a) s ∈ Metric.ball c R) :
    ‖b + c (Fin.last 3) • a - horizontalProjection c‖ < 2 * R := by
  have hh : ‖b + s • a - horizontalProjection c‖ < R := by
    have hp := norm_horizontalProjection_le (heightPoint (b + s • a) s - c)
    rw [horizontalProjection_sub, horizontalProjection_heightPoint] at hp
    exact hp.trans_lt (by simpa only [Metric.mem_ball, dist_eq_norm] using h)
  have hs := height_distance_lt_of_ball h
  have hdiff : b + c (Fin.last 3) • a - horizontalProjection c =
      (b + s • a - horizontalProjection c) + (c (Fin.last 3) - s) • a := by
    module
  rw [hdiff]
  calc
    _ ≤ ‖b + s • a - horizontalProjection c‖ + ‖(c (Fin.last 3) - s) • a‖ :=
      norm_add_le _ _
    _ ≤ ‖b + s • a - horizontalProjection c‖ + |c (Fin.last 3) - s| := by
      rw [norm_smul, Real.norm_eq_abs]
      gcongr
      exact mul_le_of_le_one_right (abs_nonneg _) ha
    _ < 2 * R := by rw [abs_sub_comm]; linarith

/-- Transferring separation from the fresh time to a cover-ball height
retains one eighth of the original slab length. -/
theorem ball_height_separated {u v t z R : ℝ} {a b : E3} {c : E4}
    (huv : u < v) (hz : z ∈ Icc (0 : ℝ) 1) (hR : R ≤ (v - u) / 8)
    (h : heightPoint (b + sampledTime u v t z • a)
      (sampledTime u v t z) ∈ Metric.ball c R) :
    (v - u) / 8 ≤ |c (Fin.last 3) - t| := by
  have hsep := sampledTime_separated (t := t) huv hz
  have hheight := height_distance_lt_of_ball h
  have htri : |sampledTime u v t z - t| ≤
      |sampledTime u v t z - c (Fin.last 3)| + |c (Fin.last 3) - t| := by
    simpa only [sub_add_sub_cancel] using
      abs_add_le (sampledTime u v t z - c (Fin.last 3)) (c (Fin.last 3) - t)
  linarith

/-- A ball hit uses at most `8 R / (v-u)` of the fresh uniform parameter.
This is a fibre estimate for each whole old occurrence, not a selector-mass
or branch-count estimate. -/
theorem unitTime_ball_hit_le {Ω : Type*}
    (a b : Ω → E3) (t : Ω → ℝ) {u v : ℝ} (huv : u < v)
    (c : E4) (R : ℝ) (ω : Ω) :
    unitTime {z | sampledPoint a b t u v (ω, z) ∈ Metric.ball c R} ≤
      ENNReal.ofReal (8 * R / (v - u)) := by
  have hL : 0 < v - u := sub_pos.mpr huv
  let lo := 4 * (c (Fin.last 3) - R - quarterStart u v (t ω)) / (v - u)
  let hi := 4 * (c (Fin.last 3) + R - quarterStart u v (t ω)) / (v - u)
  have hsub : {z | sampledPoint a b t u v (ω, z) ∈ Metric.ball c R} ⊆ Ioo lo hi := by
    intro z hz
    have hh := abs_lt.mp (height_distance_lt_of_ball hz)
    change -R < sampledTime u v (t ω) z - c (Fin.last 3) ∧
      sampledTime u v (t ω) z - c (Fin.last 3) < R at hh
    dsimp [lo, hi]
    rw [mem_Ioo, div_lt_iff₀ hL, lt_div_iff₀ hL]
    dsimp [sampledTime] at hh
    constructor <;> nlinarith [hh.1, hh.2]
  calc
    _ ≤ volume {z | sampledPoint a b t u v (ω, z) ∈ Metric.ball c R} :=
      Measure.restrict_le_self _
    _ ≤ volume (Ioo lo hi) := measure_mono hsub
    _ = ENNReal.ofReal (8 * R / (v - u)) := by
      rw [Real.volume_Ioo]
      congr 1
      dsimp [lo, hi]
      ring

/-- Project an event in the fresh-label extension to the entire old space. -/
def eventBranch {Ω : Type*} [MeasurableSpace Ω]
    (Γ : Measure Ω) (event : Set (Ω × ℝ)) : Measure Ω :=
  ((Γ.prod unitTime).restrict event).fst

theorem eventBranch_le {Ω : Type*} [MeasurableSpace Ω]
    (Γ : Measure Ω) (event : Set (Ω × ℝ)) : eventBranch Γ event ≤ Γ := by
  simpa only [eventBranch, Measure.fst_prod] using
    Measure.fst_mono (μ := Γ.prod unitTime) (Measure.restrict_le_self (s := event))

/-- A pointwise upper bound on the fresh-label fibre gives a measure-valued
upper bound on every subset of the original occurrence space. -/
theorem eventBranch_le_smul_of_fibre_le {Ω : Type*} [MeasurableSpace Ω]
    (Γ : Measure Ω) {event : Set (Ω × ℝ)} (hevent : MeasurableSet event)
    {C : ENNReal} (hC : ∀ ω, unitTime (Prod.mk ω ⁻¹' event) ≤ C) :
    eventBranch Γ event ≤ C • Γ := by
  apply Measure.le_iff.mpr
  intro s hs
  rw [eventBranch, Measure.fst_apply hs,
    Measure.restrict_apply (measurable_fst hs),
    Measure.prod_apply ((measurable_fst hs).inter hevent)]
  calc
    _ ≤ ∫⁻ ω, s.indicator (fun _ => C) ω ∂Γ := by
      apply lintegral_mono
      intro ω
      by_cases hω : ω ∈ s
      · simpa [Set.indicator_of_mem hω, Set.preimage, hω] using hC ω
      · simp [Set.preimage, hω]
    _ = C * Γ s := by rw [lintegral_indicator hs, setLIntegral_const]
    _ = (C • Γ) s := by simp

/-- A disjoint first-hit partition preserves the full inherited law exactly. -/
theorem sum_eventBranch_ordered_eq {Ω : Type*} [MeasurableSpace Ω]
    (Γ : Measure Ω) {n : ℕ} (events : Fin n → Set (Ω × ℝ))
    (hevents : ∀ i, MeasurableSet (events i))
    (hcover : ∀ᵐ p ∂Γ.prod unitTime, p ∈ ⋃ i, events i) :
    Measure.sum (fun i => eventBranch Γ (orderedMeasurableCell events i)) = Γ := by
  simp only [eventBranch]
  rw [← Measure.fst_sum,
    ← Measure.restrict_iUnion (orderedMeasurableCell_pairwise_disjoint events)
      (measurableSet_orderedMeasurableCell events hevents),
    iUnion_orderedMeasurableCell,
    Measure.restrict_eq_self_of_ae_mem hcover, Measure.fst_prod]

/-- The literal preimage of each cover ball in the actual time extension. -/
def ballEvents {Ω : Type*} {n : ℕ} (a b : Ω → E3) (t : Ω → ℝ)
    (u v : ℝ) (center : Fin n → E4) (radius : Fin n → ℝ)
    (i : Fin n) : Set (Ω × ℝ) :=
  sampledPoint a b t u v ⁻¹' Metric.ball (center i) (radius i)

/-- Canonical first-hit branch, retaining the whole old occurrence. -/
def ballBranch {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (Γ : Measure Ω) (a b : Ω → E3) (t : Ω → ℝ) (u v : ℝ)
    (center : Fin n → E4) (radius : Fin n → ℝ) (i : Fin n) : Measure Ω :=
  eventBranch Γ (orderedMeasurableCell (ballEvents a b t u v center radius) i)

theorem measurableSet_ballEvents {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    {a b : Ω → E3} {t : Ω → ℝ} (ha : Measurable a)
    (hb : Measurable b) (ht : Measurable t) (u v : ℝ)
    (center : Fin n → E4) (radius : Fin n → ℝ) (i : Fin n) :
    MeasurableSet (ballEvents a b t u v center radius i) :=
  (measurable_sampledPoint ha hb ht u v) Metric.isOpen_ball.measurableSet

theorem ballBranch_le {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (Γ : Measure Ω) (a b : Ω → E3) (t : Ω → ℝ) (u v : ℝ)
    (center : Fin n → E4) (radius : Fin n → ℝ) (i : Fin n) :
    ballBranch Γ a b t u v center radius i ≤ Γ :=
  eventBranch_le Γ _

theorem ballBranch_le_radius_smul {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (Γ : Measure Ω) {a b : Ω → E3} {t : Ω → ℝ}
    (ha : Measurable a) (hb : Measurable b) (ht : Measurable t)
    {u v : ℝ} (huv : u < v)
    (center : Fin n → E4) (radius : Fin n → ℝ) (i : Fin n) :
    ballBranch Γ a b t u v center radius i ≤
      ENNReal.ofReal (8 * radius i / (v - u)) • Γ := by
  apply eventBranch_le_smul_of_fibre_le Γ
    (measurableSet_orderedMeasurableCell _
      (measurableSet_ballEvents ha hb ht u v center radius) i)
  intro ω
  calc
    _ ≤ unitTime (Prod.mk ω ⁻¹' ballEvents a b t u v center radius i) :=
      measure_mono (Set.preimage_mono (orderedMeasurableCell_subset _ i))
    _ ≤ _ := unitTime_ball_hit_le a b t huv (center i) (radius i) ω

/-- Literal support on the common slab implies exact conservation of every
old coordinate when the physical balls cover the actual front. -/
theorem sum_ballBranch_eq {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (Γ : Measure Ω) {a b : Ω → E3} {t : Ω → ℝ}
    (ha : Measurable a) (hb : Measurable b) (ht : Measurable t)
    {u v : ℝ} (huv : u < v) (front : Set E4)
    (hfront : ∀ᵐ ω ∂Γ, ∀ s ∈ Icc u v, heightPoint (b ω + s • a ω) s ∈ front)
    (center : Fin n → E4) (radius : Fin n → ℝ)
    (hcover : front ⊆ ⋃ i, Metric.ball (center i) (radius i)) :
    Measure.sum (ballBranch Γ a b t u v center radius) = Γ := by
  apply sum_eventBranch_ordered_eq Γ _
    (measurableSet_ballEvents ha hb ht u v center radius)
  apply (Measure.ae_prod_mem_iff_ae_ae_mem (MeasurableSet.iUnion
    (measurableSet_ballEvents ha hb ht u v center radius))).mpr
  filter_upwards [hfront] with ω hω
  filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Icc] with z hz
  have hp := hcover (hω (sampledTime u v (t ω) z) (sampledTime_mem_slab huv hz))
  simpa only [mem_iUnion, ballEvents, mem_preimage, sampledPoint] using hp

/-- Every measurable inherited observable, including a whole ordered
endpoint/flag tuple, retains its exact original law after summing branches. -/
theorem sum_ballBranch_map_eq {Ω Y : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Y] {n : ℕ}
    (Γ : Measure Ω) {a b : Ω → E3} {t : Ω → ℝ}
    (ha : Measurable a) (hb : Measurable b) (ht : Measurable t)
    {u v : ℝ} (huv : u < v) (front : Set E4)
    (hfront : ∀ᵐ ω ∂Γ, ∀ s ∈ Icc u v, heightPoint (b ω + s • a ω) s ∈ front)
    (center : Fin n → E4) (radius : Fin n → ℝ)
    (hcover : front ⊆ ⋃ i, Metric.ball (center i) (radius i))
    (observable : Ω → Y) (hobservable : Measurable observable) :
    Measure.sum (fun i => (ballBranch Γ a b t u v center radius i).map observable) =
      Γ.map observable := by
  rw [← Measure.map_sum hobservable.aemeasurable,
    sum_ballBranch_eq Γ ha hb ht huv front hfront center radius hcover]

/-- The new-label law is supported on its actual unit interval, while any
inherited almost-everywhere slope bound is unchanged. -/
theorem ae_good_labels {Ω : Type*} [MeasurableSpace Ω]
    (Γ : Measure Ω) {a : Ω → E3} (ha : Measurable a)
    (ha1 : ∀ᵐ ω ∂Γ, ‖a ω‖ ≤ 1) :
    ∀ᵐ p ∂Γ.prod unitTime, ‖a p.1‖ ≤ 1 ∧ p.2 ∈ Icc (0 : ℝ) 1 := by
  apply (Measure.ae_prod_iff_ae_ae
    ((measurableSet_le (ha.comp measurable_fst).norm measurable_const).inter
      (measurable_snd measurableSet_Icc))).mpr
  filter_upwards [ha1] with ω hω
  filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Icc] with z hz
  exact ⟨hω, hz⟩

/-- Every branch is physically in its assigned bush and remains separated
from its own inherited old time. Both facts hold for the original occurrence
law on `Ω`, without replacing any endpoint, time, or flag. -/
theorem ballBranch_ae_bush_and_separated
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (Γ : Measure Ω) {a b : Ω → E3} {t : Ω → ℝ}
    (ha : Measurable a) (hb : Measurable b) (ht : Measurable t)
    (ha1 : ∀ᵐ ω ∂Γ, ‖a ω‖ ≤ 1)
    {u v : ℝ} (huv : u < v)
    (center : Fin n → E4) (radius : Fin n → ℝ) (i : Fin n)
    (hR : radius i ≤ (v - u) / 8) :
    ∀ᵐ ω ∂ballBranch Γ a b t u v center radius i,
      ‖b ω + center i (Fin.last 3) • a ω - horizontalProjection (center i)‖ <
        2 * radius i ∧
      (v - u) / 8 ≤ |center i (Fin.last 3) - t ω| := by
  let E : Set (Ω × ℝ) := orderedMeasurableCell
    (ballEvents a b t u v center radius) i
  let P : Ω → Prop := fun ω =>
    ‖b ω + center i (Fin.last 3) • a ω - horizontalProjection (center i)‖ <
      2 * radius i ∧ (v - u) / 8 ≤ |center i (Fin.last 3) - t ω|
  have he : MeasurableSet E :=
    measurableSet_orderedMeasurableCell _
      (measurableSet_ballEvents ha hb ht u v center radius) i
  have hP : MeasurableSet {ω : Ω | P ω} :=
    (measurableSet_lt
      ((hb.add (ha.const_smul (center i (Fin.last 3)))).sub
        (measurable_const : Measurable (fun _ : Ω => horizontalProjection (center i)))).norm
      (measurable_const : Measurable (fun _ : Ω => 2 * radius i))).inter
      (measurableSet_le
        (measurable_const : Measurable (fun _ : Ω => (v - u) / 8))
        ((measurable_const : Measurable (fun _ : Ω => center i (Fin.last 3))).sub ht).abs)
  have hrestricted : ∀ᵐ p ∂(Γ.prod unitTime).restrict E, P p.1 := by
    filter_upwards [ae_restrict_mem he,
      ae_restrict_of_ae (s := E) (ae_good_labels Γ ha ha1)] with p hp hgood
    have hhit : heightPoint (b p.1 + sampledTime u v (t p.1) p.2 • a p.1)
        (sampledTime u v (t p.1) p.2) ∈ Metric.ball (center i) (radius i) := hp.1
    exact ⟨bush_error_lt_of_ball (a := a p.1) (b := b p.1) hgood.1 hhit,
      ball_height_separated (t := t p.1) (z := p.2) huv hgood.2 hR hhit⟩
  exact (ae_map_iff (μ := (Γ.prod unitTime).restrict E)
    measurable_fst.aemeasurable hP).mpr hrestricted

/-- Hausdorff dimension alone supplies an arbitrarily fine, arbitrarily
low-cost finite separated bush routing of any inherited occurrence measure.
The displayed branches are the canonical actual first-hit submeasures. -/
theorem exists_low_cost_separated_bush_routing
    {Ω : Type*} [MeasurableSpace Ω]
    (Γ : Measure Ω) {a b : Ω → E3} {t : Ω → ℝ}
    (ha : Measurable a) (hb : Measurable b) (ht : Measurable t)
    (ha1 : ∀ᵐ ω ∂Γ, ‖a ω‖ ≤ 1)
    {u v : ℝ} (huv : u < v) (front : Set E4) (hcompact : IsCompact front)
    (hfront : ∀ᵐ ω ∂Γ, ∀ s ∈ Icc u v, heightPoint (b ω + s • a ω) s ∈ front)
    {q : NNReal} (hdim : dimH front < (q : ENNReal))
    {rho epsilon : ℝ} (hrho : 0 < rho) (hepsilon : 0 < epsilon) :
    ∃ n : ℕ, ∃ center : Fin n → E4, ∃ radius : Fin n → ℝ,
      front ⊆ ⋃ i, Metric.ball (center i) (radius i) ∧
      (∀ i, 0 < radius i ∧ radius i < rho ∧ radius i < (v - u) / 8) ∧
      (∑ i, radius i ^ (q : ℝ)) < epsilon ∧
      Measure.sum (ballBranch Γ a b t u v center radius) = Γ ∧
      ∀ i, ballBranch Γ a b t u v center radius i ≤ Γ ∧
        ballBranch Γ a b t u v center radius i ≤
          ENNReal.ofReal (8 * radius i / (v - u)) • Γ ∧
        ∀ᵐ ω ∂ballBranch Γ a b t u v center radius i,
          ‖b ω + center i (Fin.last 3) • a ω - horizontalProjection (center i)‖ <
            2 * radius i ∧
          (v - u) / 8 ≤ |center i (Fin.last 3) - t ω| := by
  have hscale : 0 < min rho ((v - u) / 8) :=
    lt_min hrho (by linarith)
  obtain ⟨n, center, radius, hcover, hrad, hcost⟩ :=
    exists_fin_radius_cost_ball_cover_of_compact_dimH_lt front hcompact hdim hscale hepsilon
  refine ⟨n, center, radius, hcover, ?_, hcost,
    sum_ballBranch_eq Γ ha hb ht huv front hfront center radius hcover, ?_⟩
  · intro i
    exact ⟨(hrad i).1, (lt_min_iff.mp (hrad i).2).1, (lt_min_iff.mp (hrad i).2).2⟩
  · intro i
    exact ⟨ballBranch_le Γ a b t u v center radius i,
      ballBranch_le_radius_smul Γ ha hb ht huv center radius i,
      ballBranch_ae_bush_and_separated Γ ha hb ht ha1 huv center radius i
        (lt_min_iff.mp (hrad i).2).2.le⟩

/-- Original-front specialization. Compactness is derived from the actual
compact marked datum, rather than supplied for a surrogate support set. -/
theorem exists_original_front_low_cost_separated_bush_routing
    {Ω : Type*} [MeasurableSpace Ω]
    (Γ : Measure Ω) {a b : Ω → E3} {t : Ω → ℝ}
    (ha : Measurable a) (hb : Measurable b) (ht : Measurable t)
    (ha1 : ∀ᵐ ω ∂Γ, ‖a ω‖ ≤ 1)
    {u v : ℝ} (huv : u < v) (ambient : Set MarkedLine)
    (hcompact : IsCompact ambient)
    (hfront : ∀ᵐ ω ∂Γ, ∀ s ∈ Icc u v,
      heightPoint (b ω + s • a ω) s ∈ unitFront ambient)
    {q : NNReal} (hdim : dimH (unitFront ambient) < (q : ENNReal))
    {rho epsilon : ℝ} (hrho : 0 < rho) (hepsilon : 0 < epsilon) :
    ∃ n : ℕ, ∃ center : Fin n → E4, ∃ radius : Fin n → ℝ,
      unitFront ambient ⊆ ⋃ i, Metric.ball (center i) (radius i) ∧
      (∀ i, 0 < radius i ∧ radius i < rho ∧ radius i < (v - u) / 8) ∧
      (∑ i, radius i ^ (q : ℝ)) < epsilon ∧
      Measure.sum (ballBranch Γ a b t u v center radius) = Γ ∧
      ∀ i, ballBranch Γ a b t u v center radius i ≤ Γ ∧
        ballBranch Γ a b t u v center radius i ≤
          ENNReal.ofReal (8 * radius i / (v - u)) • Γ ∧
        ∀ᵐ ω ∂ballBranch Γ a b t u v center radius i,
          ‖b ω + center i (Fin.last 3) • a ω - horizontalProjection (center i)‖ <
            2 * radius i ∧
          (v - u) / 8 ≤ |center i (Fin.last 3) - t ω| :=
  exists_low_cost_separated_bush_routing Γ ha hb ht ha1 huv
    (unitFront ambient) (StickyKakeya4.IsCompact.unitFront hcompact) hfront hdim hrho hepsilon

end StickyKakeya4.HausdorffBushRouting
