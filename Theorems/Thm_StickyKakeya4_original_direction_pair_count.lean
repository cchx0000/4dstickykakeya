import Theorems.Thm_StickyKakeya4_original_scalar_collision_geometry
import Theorems.Thm_StickyKakeya4_original_pair_strip_physical_bridge

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2800000
open Finset
open scoped BigOperators
noncomputable section
open Classical
namespace OriginalDirectionPairCount
open OriginalScalarCollisionGeometry OriginalPairStripGeometry OriginalPairStripPhysicalBridge
open OriginalPhysicalPairTube NativeRichPairTubeFamily
abbrev Point := ℝ × ℝ

lemma original_residual_det (b b' x : Point) :
    PlanarStripIntersection.residual (normalX (b,b')) (normalY (b,b')) (offset (b,b')) x =
      det (b-b') (b-x)/‖b-b'‖ := by
  have hs : scale (b,b')=‖b-b'‖ := by
    rw [norm_sub_rev]
    simp only [scale,PlanarStripIntersection.boxDistance,Prod.norm_def,Prod.fst_sub,
      Prod.snd_sub,Real.norm_eq_abs]
  rw [← hs]
  unfold PlanarStripIntersection.residual offset normalX normalY det
  simp only [Prod.fst_sub,Prod.snd_sub,div_eq_mul_inv]
  ring

/-- Actual points whose secants are close to a common displacement lie in
one actual original pair tube, with explicit width 8 eta/s. -/
theorem near_directions_mem_physical (B : Finset Point) {b b' x w : Point}
    {eta s : ℝ} (heta : 0 < eta) (hs : 0 < s) (hw : s ≤ ‖w‖)
    (hb : b ∈ B) (hx : x ∈ B) (hne : b ≠ b')
    (hbox : ∀ p ∈ B, ‖p‖ ≤ 1)
    (hu : |det (b-b') w| ≤ 2*eta*‖b-b'‖)
    (hv : |det (b-x) w| ≤ 2*eta*‖b-x‖) :
    x ∈ physicalPairTube B (8*eta/s) (b,b') := by
  have hnorm : 0 < ‖b-b'‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  have hlen : ‖b-x‖ ≤ 2 := by
    have hh := norm_sub_le b x
    linarith [hbox b hb,hbox x hx]
  have hdet := det_two_near_directions hs hw hu hv
  have hm := mul_le_mul_of_nonneg_left hlen
    (show 0 ≤ 4*eta*‖b-b'‖ by positivity)
  have hstrip : |PlanarStripIntersection.residual (normalX (b,b')) (normalY (b,b'))
      (offset (b,b')) x| ≤ 8*eta/s := by
    rw [original_residual_det,abs_div,abs_of_pos hnorm]
    apply (div_le_div_iff₀ hnorm hs).mpr
    nlinarith only [hdet,hm]
  exact original_strip_subset_physical B (8*eta/s) (b,b') hne
    (Finset.mem_filter.mpr ⟨hx,hstrip⟩)

/-- Ordered ORIGINAL B pairs incident to one displacement. -/
def directionPairs (H : Finset (Point × Point)) (w : Point) (eta : ℝ) :=
  H.filter (fun bb => |det (bb.1-bb.2) w| ≤ 2*eta*‖bb.1-bb.2‖)

/-- A native original-pair physical tube cap bounds directional incidences
without choosing new direction labels or discarding original pair weights. -/
theorem directionPairs_card (B : Finset Point) (H : Finset (Point × Point)) (w : Point)
    {eta s cap : ℝ} (heta : 0 < eta) (hs : 0 < s) (hcap0 : 0 ≤ cap) (hw : s ≤ ‖w‖)
    (hH : H ⊆ B ×ˢ B) (hdistinct : ∀ bb ∈ H, bb.1 ≠ bb.2)
    (hbox : ∀ b ∈ B, ‖b‖ ≤ 1)
    (hcap : ∀ bb ∈ H, ((physicalPairTube B (8*eta/s) bb).card : ℝ) ≤ cap*B.card) :
    ((directionPairs H w eta).card : ℝ) ≤ cap*(B.card : ℝ)^2 := by
  let P := directionPairs H w eta
  have hfib : ∀ b ∈ B, ((P.filter (fun bb => bb.1=b)).card : ℝ) ≤ cap*B.card := by
    intro b _hb
    by_cases hnon : (P.filter (fun bb => bb.1=b)).Nonempty
    · obtain ⟨bb,hbb⟩ := hnon
      obtain ⟨hbbP,hbb1⟩ := Finset.mem_filter.mp hbb
      obtain ⟨hbbH,hbbdir⟩ := Finset.mem_filter.mp hbbP
      have hbbB := Finset.mem_product.mp (hH hbbH)
      have hi : (P.filter (fun z => z.1=b)).card ≤
          (physicalPairTube B (8*eta/s) bb).card := by
        apply Finset.card_le_card_of_injOn Prod.snd
        · intro z hz
          obtain ⟨hzP,hz1⟩ := Finset.mem_filter.mp hz
          obtain ⟨hzH,hzdir⟩ := Finset.mem_filter.mp hzP
          have hzB := Finset.mem_product.mp (hH hzH)
          have hfirst : z.1=bb.1 := hz1.trans hbb1.symm
          have hh := near_directions_mem_physical B heta hs hw hbbB.1 hzB.2
            (hdistinct bb hbbH) hbox hbbdir (by simpa only [hfirst] using hzdir)
          exact hh
        · intro z hz z' hz' hzz'
          exact Prod.ext ((Finset.mem_filter.mp hz).2.trans (Finset.mem_filter.mp hz').2.symm) hzz'
      exact (Nat.cast_le.mpr hi).trans (hcap bb hbbH)
    · rw [Finset.not_nonempty_iff_eq_empty.mp hnon,Finset.card_empty,Nat.cast_zero]
      positivity
  have hsum : (P.card : ℝ)=∑ b ∈ B, ((P.filter (fun bb => bb.1=b)).card : ℝ) := by
    have hh : P.card=∑ b ∈ B, (P.filter (fun bb => bb.1=b)).card :=
      Finset.card_eq_sum_card_fiberwise (fun bb hbb =>
        (Finset.mem_product.mp (hH (Finset.mem_filter.mp hbb).1)).1)
    exact_mod_cast hh
  rw [hsum]
  calc
    _ ≤ ∑ _b ∈ B, cap*(B.card : ℝ) := Finset.sum_le_sum hfib
    _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]; ring
end OriginalDirectionPairCount
