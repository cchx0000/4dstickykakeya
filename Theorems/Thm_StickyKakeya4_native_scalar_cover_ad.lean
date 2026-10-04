import Theorems.Thm_StickyKakeya4_native_literal_aligned_set

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000
namespace NativeScalarCoverAD
open NativeLiteralAlignedSet NativeDyadicTubeStopping ShearedGridTubeReference
open FiniteVoronoiPopulation FiniteVoronoiRealADCoarsening
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

def cell (e x : ℝ) : ℤ := ⌊x / e⌋
def coverCount (X : Finset ℝ) (e x r : ℝ) : ℝ := ((carrierBall X x r).image (cell e)).card
def CoverADBounds (X : Finset ℝ) (e C s : ℝ) : Prop :=
  ∀ x ∈ X, ∀ r : ℝ, e ≤ r → r ≤ 1 →
    (r / e) ^ s / C ≤ coverCount X e x r ∧ coverCount X e x r ≤ C * (r / e) ^ s

/-- One half-open mesh cell lies in the closed mesh ball about any member.
No separation of the scalar quotient is assumed. -/
lemma cell_capacity {X : Finset ℝ} {e C s : ℝ}
    (he : 0 < e) (heone : e ≤ 1) (hC : 0 ≤ C) (H : ADBounds X e C s) (z : ℤ) :
    ((X.filter (fun x => cell e x = z)).card : ℝ) ≤ C := by
  by_cases hne : (X.filter (fun x => cell e x = z)).Nonempty
  · obtain ⟨x, hx⟩ := hne
    have hxX := (Finset.mem_filter.mp hx).1
    have hxcell := (Finset.mem_filter.mp hx).2
    have hsub : X.filter (fun y => cell e y = z) ⊆ carrierBall X x e := by
      intro y hy
      obtain ⟨hyX, hycell⟩ := Finset.mem_filter.mp hy
      refine Finset.mem_filter.mpr ⟨hyX, ?_⟩
      rw [Real.dist_eq]
      exact (SpineColumnCounting.same_floor_scaled_close he (hycell.trans hxcell.symm)).le
    have hh := (H x hxX e le_rfl heone).2
    rw [div_self he.ne', Real.one_rpow, mul_one] at hh
    exact (show ((X.filter (fun x => cell e x = z)).card : ℝ) ≤ (carrierBall X x e).card by
      exact_mod_cast Finset.card_le_card hsub).trans hh
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
    simpa only [Finset.card_empty, Nat.cast_zero] using hC

lemma card_le_capacity_mul_image {X S : Finset ℝ} {e C s : ℝ}
    (he : 0 < e) (heone : e ≤ 1) (hC : 0 ≤ C) (H : ADBounds X e C s) (hSX : S ⊆ X) :
    (S.card : ℝ) ≤ C * ((S.image (cell e)).card : ℝ) := by
  have hsum : (S.card : ℝ) = ∑ z ∈ S.image (cell e), ((S.filter (fun x => cell e x = z)).card : ℝ) := by
    exact_mod_cast Finset.card_eq_sum_card_image (cell e) S
  rw [hsum]
  calc
    _ ≤ ∑ _z ∈ S.image (cell e), C := by
      apply Finset.sum_le_sum
      intro z _hz
      have hsub : S.filter (fun x => cell e x = z) ⊆ X.filter (fun x => cell e x = z) :=
        Finset.filter_subset_filter _ hSX
      exact (show ((S.filter (fun x => cell e x = z)).card : ℝ) ≤ (X.filter (fun x => cell e x = z)).card by
        exact_mod_cast Finset.card_le_card hsub).trans (cell_capacity he heone hC H z)
    _ = _ := by simp [mul_comm]

/-- Exact scalar conversion with cost C squared and no fixed factor. -/
theorem point_AD_to_cover_AD {X : Finset ℝ} {e C s : ℝ}
    (he : 0 < e) (heone : e ≤ 1) (hC : 1 ≤ C) (H : ADBounds X e C s) :
    CoverADBounds X e (C ^ 2) s := by
  have hCp : 0 < C := zero_lt_one.trans_le hC
  have hCsq : C ≤ C ^ 2 := by nlinarith only [hC]
  intro x hx r hrlo hrhi
  have hr : 0 < r := he.trans_le hrlo
  have hp : 0 ≤ (r / e) ^ s := by positivity
  have hh := H x hx r hrlo hrhi
  have hmass := card_le_capacity_mul_image he heone hCp.le H (Finset.filter_subset (fun y => dist y x ≤ r) X)
  change ((carrierBall X x r).card : ℝ) ≤ C * coverCount X e x r at hmass
  constructor
  · apply (div_le_iff₀ (sq_pos_of_pos hCp)).mpr
    have hl := (div_le_iff₀ hCp).mp hh.1
    have hmul := mul_le_mul_of_nonneg_right hmass hCp.le
    nlinarith only [hl, hmul]
  · have himage : coverCount X e x r ≤ ((carrierBall X x r).card : ℝ) := by
      unfold coverCount
      exact_mod_cast Finset.card_image_le (s := carrierBall X x r) (f := cell e)
    exact (himage.trans hh.2).trans (mul_le_mul_of_nonneg_right hCsq hp)

structure CoverAligned (P : Finset Plane) (e t s C : ℝ) : Prop where
  mesh_pos : 0 < e
  nonempty : P.Nonempty
  separated : ∀ p ∈ P, ∀ q ∈ P, p ≠ q →
    e ≤ dist (EuclideanAlignmentPatches.euclidean p) (EuclideanAlignmentPatches.euclidean q)
  bounded : ∀ p ∈ P, ∀ i, |p i| ≤ 1
  fibers : ∃ (angle : ℝ) (Y : Finset ℝ) (X : Y → Finset ℝ),
    |angle| ≤ 1 ∧ Y.Nonempty ∧ (∀ y ∈ Y, |y| ≤ 1) ∧ CoverADBounds Y e C (t-s) ∧
    (∀ y, (X y).Nonempty ∧ (∀ x ∈ X y, |x| ≤ 1) ∧ CoverADBounds (X y) e C s) ∧
    P = Y.attach.biUnion (fun y => (X y).image (fun x => ![x, angle*x+(y:ℝ)]))
  tubes : ∀ rho tau, e ≤ rho → rho ≤ tau → TraceBound P rho tau (C*(tau/rho)^s)

structure NearlyCoverAligned (A : Finset Plane) (e t s C : ℝ) : Prop where
  bounded : ∀ p ∈ A, ∀ i, |p i| ≤ 1
  aligned : ∃ P : Finset Plane, CoverAligned P e t s C ∧
    (∀ p ∈ A, ∃ q ∈ P,
      dist (EuclideanAlignmentPatches.euclidean p) (EuclideanAlignmentPatches.euclidean q) < e) ∧
    (∀ q ∈ P, ∃ p ∈ A,
      dist (EuclideanAlignmentPatches.euclidean p) (EuclideanAlignmentPatches.euclidean q) < e)

theorem literal_to_cover {P : Finset Plane} {e t s C : ℝ}
    (H : LiteralAligned P e t s C) (heone : e ≤ 1) (hC : 1 ≤ C) :
    CoverAligned P e t s (C ^ 2) := by
  refine ⟨H.mesh_pos, H.nonempty, H.separated, H.bounded, ?_, ?_⟩
  · obtain ⟨angle, Y, X, hangle, hY, hYbound, hYAD, hX, hgraph⟩ := H.fibers
    refine ⟨angle, Y, X, hangle, hY, hYbound, point_AD_to_cover_AD H.mesh_pos heone hC hYAD, ?_, hgraph⟩
    intro y
    exact ⟨(hX y).1, (hX y).2.1, point_AD_to_cover_AD H.mesh_pos heone hC (hX y).2.2⟩
  · intro rho tau hrho hrt T
    have hrhopos := H.mesh_pos.trans_le hrho
    have htaupos := hrhopos.trans_le hrt
    have hC2 : C ≤ C ^ 2 := by nlinarith only [hC]
    exact (H.tubes rho tau hrho hrt T).trans (mul_le_mul_of_nonneg_right hC2 (by positivity))

theorem nearly_literal_to_cover {A : Finset Plane} {e t s C : ℝ}
    (H : NearlyLiteralAligned A e t s C) (heone : e ≤ 1) (hC : 1 ≤ C) :
    NearlyCoverAligned A e t s (C ^ 2) := by
  obtain ⟨P, hP, hnear, hback⟩ := H.aligned
  exact ⟨H.bounded, P, literal_to_cover hP heone hC, hnear, hback⟩
end
end NativeScalarCoverAD
