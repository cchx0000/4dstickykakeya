import Theorems.Thm_StickyKakeya4_original_slope_graph_nonconcentration
import Theorems.Thm_StickyKakeya4_native_quarter_scale_parameters
import Mathlib.Analysis.Real.Sqrt
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1500000
noncomputable section
namespace OriginalEuclideanAffineAvoidance
open Classical OriginalSlopeGraphNonconcentration OriginalCoarseHeightCurve
open FinitePlaneProjectionGrid NativeQuarterScaleParameters
/-- The literal Euclidean length of the original two transverse coordinates. -/
def length2 (v : ℝ × ℝ) : ℝ := Real.sqrt (v.1^2+v.2^2)
/-- Explicit conversion from the native product sup norm. -/
theorem length2_le_twice_norm (v : ℝ × ℝ) : length2 v ≤ 2*‖v‖ := by
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity,?_⟩
  have h1 : |v.1| ≤ ‖v‖ := le_max_left _ _
  have h2 : |v.2| ≤ ‖v‖ := le_max_right _ _
  have hs1 := (sq_le_sq₀ (abs_nonneg v.1) (norm_nonneg v)).mpr h1
  have hs2 := (sq_le_sq₀ (abs_nonneg v.2) (norm_nonneg v)).mpr h2
  rw [sq_abs] at hs1 hs2
  nlinarith only [hs1,hs2,sq_nonneg ‖v‖]
/-- The unchanged original source avoidance statement supplies the native
 strict affine cap with the explicit factor-two width loss. -/
theorem original_euclidean_avoidance_sup (Z : Finset ℝ) (f : ℝ → ℝ × ℝ)
    {threshold N : ℝ}
    (havoid : ∀ r u : ℝ × ℝ,
      ((Z.filter (fun z => length2 (f z-z • r-u) < threshold)).card : ℝ) ≤ N) :
    ∀ r u : ℝ × ℝ,
      ((Z.filter (fun z => ‖f z-z • r-u‖ < threshold/2)).card : ℝ) ≤ N := by
  intro r u
  have hs : Z.filter (fun z => ‖f z-z • r-u‖ < threshold/2) ⊆
      Z.filter (fun z => length2 (f z-z • r-u) < threshold) := by
    intro z hz
    obtain ⟨hz,hzdist⟩ := Finset.mem_filter.mp hz
    exact Finset.mem_filter.mpr ⟨hz,(length2_le_twice_norm _).trans_lt (by linarith only [hzdist])⟩
  exact (Nat.cast_le.mpr (Finset.card_le_card hs)).trans (havoid r u)
/-- Original Euclidean (167) feeds the actual normalized affine graph tube.
 The effective Lip envelope includes the fixed Euclidean conversion. -/
theorem quarter_original_euclidean_affine_cap
    (Z : Finset ℝ) (f : ℝ → ℝ × ℝ) (z0 : ℝ) (f0 : ℝ × ℝ)
    {delta Lip ell s e N : ℝ} (hd : 0 < delta) (hLip0 : 0 < Lip)
    (hLip : 2*Lip ≤ delta^(-ell)) (he : e ≤ (1/8:ℝ)*delta^(2*s))
    (hsmall : delta^(3*s/4-ell) ≤ (1/4:ℝ))
    (havoid : ∀ r u : ℝ × ℝ,
      ((Z.filter (fun z => length2 (f z-z • r-u) < (quarterScale delta)^(1+s))).card : ℝ) ≤ N)
    (a1 a2 c1 c2 : ℝ) :
    ((originalAffineGraphTube Z (heightGraph (quarterScale delta) Lip z0 f0 f)
      a1 a2 c1 c2 ((delta^(2*s)+2*e)/delta^s)).card : ℝ) ≤ N := by
  have hbuffer := quarter_affine_source_buffer hd (show 0 ≤ 2*Lip by positivity) hLip he hsmall
  have hs : Lip*quarterScale delta*((delta^(2*s)+2*e)/delta^s) <
      (quarterScale delta)^(1+s)/2 := by linarith only [hbuffer]
  exact original_affine_avoidance_normalized Z f z0 f0
    (Real.rpow_pos_of_pos hd _) hLip0 hs (original_euclidean_avoidance_sup Z f havoid) a1 a2 c1 c2
end OriginalEuclideanAffineAvoidance
