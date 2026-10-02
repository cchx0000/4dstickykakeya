import Theorems.Thm_StickyKakeya4_exact_collision_identity

/-!
# All-target source fibers of a separated-time physical bush

The explicit center below strengthens the local use of manuscript Lemma 9.11:
the old target need not lie in the source cap. The inherited old collision
error `r` remains in the estimate, separately from the new bush error `R`.
The final estimate pays one bush (or one joint common-center occurrence).
It does not assert a bound after summing arbitrary varying-center bushes.
-/

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace StickyKakeya4.SeparatedBushFiber

/-- Direction center determined by the old target and the current physical
bush; no measurable choice from an individual fiber is required. -/
def fiberCenter (a' b' c : E3) (s₀ t₀ : ℝ) : E3 :=
  a' + (t₀ - s₀)⁻¹ • (b' + s₀ • a' - c)

/-- Exact two-probe identity, with the target and source kept in their original
roles. -/
theorem scaled_fiber_displacement (a b a' b' c : E3) (s₀ t₀ : ℝ)
    (hne : t₀ - s₀ ≠ 0) :
    (t₀ - s₀) • (a - fiberCenter a' b' c s₀ t₀) =
      ((b - b') + t₀ • (a - a')) - (b + s₀ • a - c) := by
  rw [fiberCenter, sub_add_eq_sub_sub, smul_sub, smul_smul,
    mul_inv_cancel₀ hne, one_smul]
  module

/-- Moving an actual collision time to its packet center costs the packet
width times the original direction separation. -/
theorem collision_at_packet_center (a b a' b' : E3) (t t₀ r δ L : ℝ)
    (hcollision : ‖(b - b') + t • (a - a')‖ ≤ r)
    (hpacket : |t - t₀| ≤ δ) (hangle : ‖a - a'‖ ≤ L) :
    ‖(b - b') + t₀ • (a - a')‖ ≤ r + δ * L := by
  have hδ : 0 ≤ δ := (abs_nonneg _).trans hpacket
  have hdecomp : (b - b') + t₀ • (a - a') =
      ((b - b') + t • (a - a')) + (t₀ - t) • (a - a') := by module
  calc
    ‖(b - b') + t₀ • (a - a')‖ ≤
        ‖(b - b') + t • (a - a')‖ + ‖(t₀ - t) • (a - a')‖ := by
      rw [hdecomp]
      exact norm_add_le _ _
    _ ≤ r + δ * L := by
      apply add_le_add hcollision
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul (by simpa only [abs_sub_comm] using hpacket)
        hangle (norm_nonneg _) hδ

/-- Every source fiber lies in one explicit direction ball. The radius includes
the inherited old error, without replacing it by an auxiliary failure scale. -/
theorem source_mem_fiber_cap (a b a' b' c : E3) (s₀ t₀ t R r δ L g : ℝ)
    (hbush : ‖b + s₀ • a - c‖ ≤ R)
    (hcollision : ‖(b - b') + t • (a - a')‖ ≤ r)
    (hpacket : |t - t₀| ≤ δ) (hangle : ‖a - a'‖ ≤ L)
    (hg : 0 < g) (hsep : g ≤ |t₀ - s₀|) :
    a ∈ Metric.closedBall (fiberCenter a' b' c s₀ t₀) ((R + r + δ * L) / g) := by
  have hne : t₀ - s₀ ≠ 0 := abs_pos.mp (hg.trans_le hsep)
  have htime := collision_at_packet_center a b a' b' t t₀ r δ L
    hcollision hpacket hangle
  have hn : ‖(t₀ - s₀) • (a - fiberCenter a' b' c s₀ t₀)‖ ≤
      (r + δ * L) + R := by
    rw [scaled_fiber_displacement a b a' b' c s₀ t₀ hne]
    exact (norm_sub_le _ _).trans (add_le_add htime hbush)
  have hp : g * ‖a - fiberCenter a' b' c s₀ t₀‖ ≤ R + r + δ * L := by
    calc
      g * ‖a - fiberCenter a' b' c s₀ t₀‖ ≤
          |t₀ - s₀| * ‖a - fiberCenter a' b' c s₀ t₀‖ :=
        mul_le_mul_of_nonneg_right hsep (norm_nonneg _)
      _ = ‖(t₀ - s₀) • (a - fiberCenter a' b' c s₀ t₀)‖ := by
        rw [norm_smul, Real.norm_eq_abs]
      _ ≤ R + r + δ * L := by linarith
  rw [Metric.mem_closedBall, dist_eq_norm]
  exact (le_div_iff₀ hg).2 (by simpa only [mul_comm] using hp)

/-- The explicit center is measurable in the old target's line data. -/
theorem measurable_fiberCenter {X : Type*} [MeasurableSpace X]
    (a b : X → E3) (ha : Measurable a) (hb : Measurable b)
    (c : E3) (s₀ t₀ : ℝ) :
    Measurable (fun z => fiberCenter (a z) (b z) c s₀ t₀) := by
  unfold fiberCenter
  fun_prop

/-- A target-dependent source cap. Both entries remain the original ordered
endpoints, and the center is allowed to depend on the old target. -/
def fiberCapSet {X : Type*} (a center : X → E3) (T : ℝ) : Set (X × X) :=
  {p | a p.1 ∈ Metric.closedBall (center p.2) T}

theorem measurableSet_fiberCapSet {X : Type*} [MeasurableSpace X]
    (a center : X → E3) (ha : Measurable a) (hc : Measurable center) (T : ℝ) :
    MeasurableSet (fiberCapSet a center T) := by
  have hm : Measurable (fun p : X × X => dist (a p.1) (center p.2)) := by fun_prop
  exact measurableSet_le hm measurable_const

/-- Tonelli in the old-target variable pays the entire target-dependent source
cap set. There is no requirement that the target lie inside its fiber's cap. -/
theorem product_fiberCapSet_le {X : Type*} [MeasurableSpace X]
    (σ : Measure X) [SFinite σ] (a center : X → E3)
    (ha : Measurable a) (hc : Measurable center) (T : ℝ) (B : ℝ≥0∞)
    (hball : ∀ x : E3, σ (a ⁻¹' Metric.closedBall x T) ≤ B) :
    (σ.prod σ) (fiberCapSet a center T) ≤ B * σ univ := by
  rw [Measure.prod_apply_symm (measurableSet_fiberCapSet a center ha hc T)]
  calc
    (∫⁻ y, σ ((fun x => (x, y)) ⁻¹' fiberCapSet a center T) ∂σ) ≤
        ∫⁻ _y, B ∂σ := by
      apply lintegral_mono
      intro y
      exact hball (center y)
    _ = B * σ univ := lintegral_const B

/-- A common-bush all-target budget follows from genuine joint domination and
fiber support, not from domination of an old-neighbor conditional kernel. -/
theorem occurrence_mass_le_fiber_cap {X : Type*} [MeasurableSpace X]
    (σ : Measure X) [SFinite σ] (Γ : Measure (X × X))
    (a center : X → E3) (ha : Measurable a) (hc : Measurable center)
    (T : ℝ) (B : ℝ≥0∞) (hdom : Γ ≤ σ.prod σ)
    (hsupport : Γ (fiberCapSet a center T)ᶜ = 0)
    (hball : ∀ x : E3, σ (a ⁻¹' Metric.closedBall x T) ≤ B) :
    Γ univ ≤ B * σ univ := by
  have hmass : Γ univ = Γ (fiberCapSet a center T) := by
    simpa only [hsupport, add_zero] using
      (measure_add_measure_compl (μ := Γ)
        (measurableSet_fiberCapSet a center ha hc T)).symm
  rw [hmass]
  exact (hdom _).trans (product_fiberCapSet_le σ a center ha hc T B hball)

/-- Without choosing a time packet, the source direction is close to a point
on one affine line through the old target direction. This is the geometric
input for the packet-free codimension-two tube estimate. -/
theorem source_near_target_line (a b a' b' c : E3) (s₀ t R r g : ℝ)
    (hbush : ‖b + s₀ • a - c‖ ≤ R)
    (hcollision : ‖(b - b') + t • (a - a')‖ ≤ r)
    (hg : 0 < g) (hsep : g ≤ |t - s₀|) :
    ∃ u : ℝ, ‖a - (a' + u • (b' + s₀ • a' - c))‖ ≤ (R + r) / g := by
  refine ⟨(t - s₀)⁻¹, ?_⟩
  have h := source_mem_fiber_cap a b a' b' c s₀ t t R r 0 ‖a - a'‖ g
    hbush hcollision (by simp) le_rfl hg hsep
  simpa only [Metric.mem_closedBall, dist_eq_norm, fiberCenter, zero_mul,
    add_zero] using h

/-- Actual physical incidences and bounded original direction density pay all
old targets for one common bush and one separated time packet. This theorem
retains the root collision error explicitly and does not normalize a node. -/
theorem physical_packet_occurrence_le_cubic
    {X : Type*} [MeasurableSpace X]
    (σ : Measure X) [SFinite σ] (Γ : Measure (X × X))
    (a b : X → E3) (ha : Measurable a) (hb : Measurable b)
    (c : E3) (s₀ t₀ R r δ L g : ℝ) (C : ℝ≥0∞)
    (hR : 0 ≤ R) (hr : 0 ≤ r) (hδ : 0 ≤ δ) (hL : 0 ≤ L)
    (hg : 0 < g) (hsep : g ≤ |t₀ - s₀|)
    (hdom : Γ ≤ σ.prod σ)
    (hphysical : Γ {p : X × X | ∃ t : ℝ,
      ‖b p.1 + s₀ • a p.1 - c‖ ≤ R ∧
      ‖(b p.1 - b p.2) + t • (a p.1 - a p.2)‖ ≤ r ∧
      |t - t₀| ≤ δ ∧ ‖a p.1 - a p.2‖ ≤ L}ᶜ = 0)
    (hdensity : ∀ x : E3, ∀ T : ℝ, 0 ≤ T →
      σ (a ⁻¹' Metric.closedBall x T) ≤ C * ENNReal.ofReal T ^ 3) :
    Γ univ ≤ (C * ENNReal.ofReal ((R + r + δ * L) / g) ^ 3) * σ univ := by
  apply occurrence_mass_le_fiber_cap σ Γ a
    (fun z => fiberCenter (a z) (b z) c s₀ t₀) ha
    (measurable_fiberCenter a b ha hb c s₀ t₀)
    ((R + r + δ * L) / g) (C * ENNReal.ofReal ((R + r + δ * L) / g) ^ 3) hdom
  · apply measure_mono_null _ hphysical
    apply compl_subset_compl.mpr
    intro p hp
    obtain ⟨t, hbush, hcollision, hpacket, hangle⟩ := hp
    exact source_mem_fiber_cap (a p.1) (b p.1) (a p.2) (b p.2) c
      s₀ t₀ t R r δ L g hbush hcollision hpacket hangle hg hsep
  · intro x
    apply hdensity
    positivity

end StickyKakeya4.SeparatedBushFiber
