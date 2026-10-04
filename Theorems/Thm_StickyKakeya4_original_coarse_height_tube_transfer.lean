import Theorems.Thm_StickyKakeya4_original_coarse_height_curve
import Theorems.Thm_StickyKakeya4_finite_plane_projection_perturbation
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000
noncomputable section
namespace OriginalCoarseHeightTubeTransfer
open Classical DyadicOriginalFiberSelection OriginalHeightGraphDensity OriginalCoarseHeightCurve
open FinitePlaneProjectionGrid
theorem coarse_cross_tube_original_charge (Z : Finset ℝ) (j : ℕ) {rho Lip width w : ℝ}
    (hrho : 0 < rho) (hLip : 0 < Lip) (hw : 0 < width)
    (hbin : (bin Z (coarseHeight width) j).Nonempty) (z₀ : ℝ) (f₀ : ℝ × ℝ) (f : ℝ → ℝ × ℝ)
    (hosc : ∀ z ∈ Z, ∀ z' ∈ Z, coarseHeight width z=coarseHeight width z' → ‖f z-f z'‖ ≤ Lip*width) (i k : ℤ) :
    let Z' := bin Z (coarseHeight width) j
    let Q := Z'.image (coarseHeight width)
    let sample := representative Z' hbin width
    let b := heightGraph rho Lip z₀ f₀ f
    (2^j)*((originalCrossTube Q (fun a => b (sample a)) i k w).card) ≤
      (originalCrossTube Z b (sample i) (sample k) (w+2*(width/rho))).card := by
  let Z' := bin Z (coarseHeight width) j
  let Q := Z'.image (coarseHeight width)
  let sample := representative Z' hbin width
  let b := heightGraph rho Lip z₀ f₀ f
  let Bad := originalCrossTube Q (fun a => b (sample a)) i k w
  apply bad_coarse_labels_count Z (coarseHeight width) j Bad (originalCrossTube Z b (sample i) (sample k) (w+2*(width/rho)))
  · exact Finset.filter_subset _ _
  · intro a ha z hz
    obtain ⟨haQ,hcross⟩ := Finset.mem_filter.mp ha
    obtain ⟨hzZ,hza⟩ := Finset.mem_filter.mp hz
    have hrep := representative_spec Z' hbin width a haQ
    have hrZ : sample a ∈ Z := (Finset.mem_filter.mp hrep.1).1
    have hcell : coarseHeight width z=coarseHeight width (sample a) := hza.trans hrep.2.symm
    have hnear : dist3 (b z) (b (sample a)) ≤ width/rho := by
      rw [dist3_eq_norm]
      exact same_cell_graph_error hrho hLip hw z₀ f₀ f hcell (hosc z hzZ (sample a) hrZ hcell)
    have hbad : sample a ∈ originalCrossTube Z b (sample i) (sample k) w := Finset.mem_filter.mpr ⟨hrZ,hcross⟩
    exact originalCrossTube_transport Z b hzZ hnear hbad
theorem coarse_cross_tube_fraction (Z : Finset ℝ) (j : ℕ) {rho Lip width w beta epsilon : ℝ}
    (hrho : 0 < rho) (hLip : 0 < Lip) (hw : 0 < width) (hbeta : 0 ≤ beta) (hepsilon : 0 ≤ epsilon)
    (hbin : (bin Z (coarseHeight width) j).Nonempty) (z₀ : ℝ) (f₀ : ℝ × ℝ) (f : ℝ → ℝ × ℝ)
    (hosc : ∀ z ∈ Z, ∀ z' ∈ Z, coarseHeight width z=coarseHeight width z' → ‖f z-f z'‖ ≤ Lip*width)
    (hret : beta*(Z.card : ℝ) ≤ (levelCount Z : ℝ)*((bin Z (coarseHeight width) j).card : ℝ)) (i k : ℤ)
    (hline : let Z' := bin Z (coarseHeight width) j
      let sample := representative Z' hbin width
      ((originalCrossTube Z (heightGraph rho Lip z₀ f₀ f) (sample i) (sample k) (w+2*(width/rho))).card : ℝ) ≤ epsilon*(Z.card : ℝ)) :
    let Z' := bin Z (coarseHeight width) j
    let Q := Z'.image (coarseHeight width)
    let sample := representative Z' hbin width
    let b := heightGraph rho Lip z₀ f₀ f
    beta*((originalCrossTube Q (fun a => b (sample a)) i k w).card : ℝ) ≤ 2*(levelCount Z : ℝ)*epsilon*(Q.card : ℝ) := by
  let Z' := bin Z (coarseHeight width) j
  let Q := Z'.image (coarseHeight width)
  let sample := representative Z' hbin width
  let b := heightGraph rho Lip z₀ f₀ f
  let Bad := originalCrossTube Q (fun a => b (sample a)) i k w
  have hcharge := coarse_cross_tube_original_charge Z j hrho hLip hw hbin z₀ f₀ f hosc i k (w := w)
  have hcharge' : (2^j:ℝ)*(Bad.card : ℝ) ≤ epsilon*(Z.card : ℝ) := by
    exact (show (2^j:ℝ)*(Bad.card : ℝ) ≤ ((originalCrossTube Z b (sample i) (sample k) (w+2*(width/rho))).card : ℝ) by exact_mod_cast hcharge).trans hline
  have hupper : (Z'.card : ℝ) ≤ 2*(2^j:ℝ)*(Q.card : ℝ) := by
    have hh := (OriginalHeightGraphCoarsening.dyadic_label_mass_bounds Z (coarseHeight width) j).2
    have hh' : (Z'.card : ℝ) ≤ (2^(j+1):ℝ)*(Q.card : ℝ) := by exact_mod_cast hh
    simpa only [pow_succ,mul_assoc,mul_comm,mul_left_comm] using hh'
  have hL : 0 ≤ (levelCount Z : ℝ) := by positivity
  apply (mul_le_mul_iff_left₀ (by positivity : (0:ℝ)<2^j)).mp
  calc
    _ = beta*((2^j:ℝ)*(Bad.card : ℝ)) := by ring
    _ ≤ beta*(epsilon*(Z.card : ℝ)) := mul_le_mul_of_nonneg_left hcharge' hbeta
    _ = epsilon*(beta*(Z.card : ℝ)) := by ring
    _ ≤ epsilon*((levelCount Z : ℝ)*(Z'.card : ℝ)) := mul_le_mul_of_nonneg_left hret hepsilon
    _ ≤ epsilon*((levelCount Z : ℝ)*(2*(2^j:ℝ)*(Q.card : ℝ))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hupper hL) hepsilon
    _ = _ := by ring
end OriginalCoarseHeightTubeTransfer
