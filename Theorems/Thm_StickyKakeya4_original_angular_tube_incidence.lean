import Theorems.Thm_StickyKakeya4_original_radial_sine_geometry
import Theorems.Thm_StickyKakeya4_radial_angle_bin_incidence
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000

noncomputable section
namespace OriginalAngularTubeIncidence
open Classical OriginalPairStripGeometry OriginalPhysicalPairTube NativeRadialClassPruning
open OriginalRadialSineGeometry RadialAngleBinIncidence

/-- One actual original point away from a fixed root meets a uniformly
bounded number of ORIGINAL angle-bin representatives. -/
theorem original_point_tube_incidence (P Q : Finset Point) (p v : Point)
    {rho tau : ℝ} (hrho : 0<rho) (htau : 0<tau) (htau1 : tau≤1)
    (hfar : tau≤scale (p,v)) (hne : ∀ q∈Q, p≠q)
    (hinj : Set.InjOn (fun q => ⌊radialAngle p q/rho⌋) (↑Q)) :
    ((Q.filter (fun q => v∈physicalPairTube P rho (p,q))).card : ℝ) ≤50/tau := by
  let I := Q.filter (fun q => v∈physicalPairTube P rho (p,q))
  apply native_small_sine_bin_card I (radialAngle p) hrho htau htau1
    (phi:=radialAngle p v)
  · exact Complex.abs_arg_le_pi _
  · intro q _hq
    exact Complex.abs_arg_le_pi _
  · exact hinj.mono (Finset.filter_subset _ _)
  · intro q hq
    obtain ⟨hq,hv⟩ := Finset.mem_filter.mp hq
    exact physical_tube_small_sine P p q v (hne q hq) htau hfar hv

/-- Euclidean off-root hypotheses are retained literally. The fixed
Euclidean-to-box conversion only doubles the incidence constant. -/
theorem original_point_tube_incidence_euclidean (P Q : Finset Point) (p v : Point)
    {rho tau : ℝ} (hrho : 0<rho) (htau : 0<tau) (htau1 : tau≤1)
    (hfar : tau≤PlanarFrostmanBallConversion.euclideanDistance p v)
    (hne : ∀ q∈Q, p≠q)
    (hinj : Set.InjOn (fun q => ⌊radialAngle p q/rho⌋) (↑Q)) :
    ((Q.filter (fun q => v∈physicalPairTube P rho (p,q))).card : ℝ) ≤100/tau := by
  have hbox := PlanarFrostmanBallConversion.euclidean_le_two_box p v
  have hf : tau/2≤scale (p,v) := by
    change tau/2≤PlanarStripIntersection.boxDistance p v
    linarith only [hfar,hbox]
  have h := original_point_tube_incidence P Q p v hrho (show 0<tau/2 by positivity)
    (show tau/2≤1 by linarith) hf hne hinj
  have heq : 50/(tau/2)=100/tau := by field_simp; ring
  simpa only [heq] using h

end OriginalAngularTubeIncidence
