import Theorems.Thm_StickyKakeya4_original_scalar_collision_mass
import Theorems.Thm_StickyKakeya4_original_angular_exponent_range
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2200000
noncomputable section
namespace OriginalHeightVertexDensity
open Classical OriginalScalarCollisionMass OriginalWWitnessCounts OriginalWCoarseEscapeMenus
variable {P T H : Type*} [DecidableEq P] [DecidableEq T] [DecidableEq H]
/-- The original height/tube incidence fiber counts exactly the original
 pointsAt labels; it is not a surrogate occupied-cell count. -/
theorem original_height_vertex_fiber (I : Finset (P × T)) (height : P → H) (v : H × T) :
    (I.filter (fun e => (height e.1,e.2)=v)).card=(pointsAt I height v.2 v.1).card := by
  apply Finset.card_bij (fun e _he => e.1)
  · intro e he
    obtain ⟨heI,heV⟩ := Finset.mem_filter.mp he
    have ht : e.2=v.2 := congrArg Prod.snd heV
    have hz : height e.1=v.1 := congrArg Prod.fst heV
    exact (mem_pointsAt I height v.2 v.1 e.1).mpr ⟨by simpa only [← ht] using heI,hz⟩
  · intro e he f hf hef
    have htE := congrArg Prod.snd (Finset.mem_filter.mp he).2
    have htF := congrArg Prod.snd (Finset.mem_filter.mp hf).2
    exact Prod.ext hef (htE.trans htF.symm)
  · intro p hp
    obtain ⟨hpI,hpz⟩ := (mem_pointsAt I height v.2 v.1 p).mp hp
    exact ⟨(p,v.2),Finset.mem_filter.mpr ⟨hpI,Prod.ext hpz rfl⟩,rfl⟩
/-- Original same-height occupancy supplies the exact incidence-to-vertex
 loss on the unchanged original incidence family. -/
theorem incidences_le_height_vertices (I : Finset (P × T)) (height : P → H) {C : ℝ}
    (_hC : 0 ≤ C) (hpoints : ∀ t z, ((pointsAt I height t z).card:ℝ) ≤ C) :
    (I.card:ℝ) ≤ C*(vertices I height).card := by
  have hh := FinePointSlabGeometry.card_le_real_mul_of_fibers I (vertices I height)
    (fun e => (height e.1,e.2)) C
    (fun e he => by rw [vertices_eq_original_incidence_image]; exact Finset.mem_image_of_mem _ he)
    (fun v _hv => by rw [original_height_vertex_fiber]; exact hpoints v.2 v.1)
  simpa only [mul_comm] using hh
/-- Consume a genuine original incidence density and height packing cap.
 No extra height selection, W-count, or graph-density certificate is used. -/
theorem original_average_height_density (I : Finset (P × T)) (height : P → H) (Z : Finset H)
    {delta C heightCap incidenceDensity : ℝ} (hd : 0 ≤ delta) (hC : 0 < C) (hH : 0 < heightCap)
    (hpoints : ∀ t z, ((pointsAt I height t z).card:ℝ) ≤ C)
    (hIncidence : incidenceDensity*(TwoTubePathCollisionCount.tubes I).card ≤ delta*(I.card:ℝ))
    (hHeight : delta*(Z.card:ℝ) ≤ heightCap) :
    (incidenceDensity/(C*heightCap))*(Z.card:ℝ)*(TwoTubePathCollisionCount.tubes I).card ≤
      (vertices I height).card := by
  have hcap := incidences_le_height_vertices I height hC.le hpoints
  have hh : incidenceDensity*(Z.card:ℝ)*(TwoTubePathCollisionCount.tubes I).card ≤
      ((vertices I height).card:ℝ)*(C*heightCap) := by
    calc
      _ = (incidenceDensity*(TwoTubePathCollisionCount.tubes I).card)*(Z.card:ℝ) := by ring
      _ ≤ (delta*(I.card:ℝ))*(Z.card:ℝ) := mul_le_mul_of_nonneg_right hIncidence (Nat.cast_nonneg _)
      _ ≤ (delta*(C*(vertices I height).card))*(Z.card:ℝ) := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hcap hd) (Nat.cast_nonneg _)
      _ = (C*(vertices I height).card)*(delta*(Z.card:ℝ)) := by ring
      _ ≤ (C*(vertices I height).card)*heightCap := mul_le_mul_of_nonneg_left hHeight (by positivity)
      _ = _ := by ring
  have hdiv := (div_le_iff₀ (mul_pos hC hH)).mpr hh
  simpa only [div_eq_mul_inv,mul_assoc,mul_comm,mul_left_comm] using hdiv
/-- The literal original delta-separated height set in [-1,1] supplies the
 height packing cap, so its only population input is original incidence mass. -/
theorem boxed_original_height_density (I : Finset (P × T)) (height : P → ℝ) (Z : Finset ℝ)
    {delta C incidenceDensity : ℝ} (hd : 0 < delta) (hd1 : delta ≤ 1) (hC : 0 < C)
    (hsep : ∀ z ∈ Z, ∀ w ∈ Z, z ≠ w → delta ≤ |z-w|) (hbox : ∀ z ∈ Z, |z| ≤ 1)
    (hpoints : ∀ t z, ((pointsAt I height t z).card:ℝ) ≤ C)
    (hIncidence : incidenceDensity*(TwoTubePathCollisionCount.tubes I).card ≤ delta*(I.card:ℝ)) :
    (incidenceDensity/(4*C))*(Z.card:ℝ)*(TwoTubePathCollisionCount.tubes I).card ≤
      (vertices I height).card := by
  have hsep' : FiniteVoronoiPopulation.Separated Z delta := by
    intro z hz w hw hzw
    simpa only [Real.dist_eq] using hsep z hz w hw hzw
  have hc := OriginalAngularExponentRange.original_angular_card_upper Z hd hd1 hsep' hbox
  have hHeight : delta*(Z.card:ℝ) ≤ 4 := by
    have hh := (le_div_iff₀ hd).mp hc
    nlinarith only [hh]
  have hh := original_average_height_density I height Z hd.le hC (by norm_num : (0:ℝ)<4) hpoints hIncidence hHeight
  simpa only [mul_comm C 4] using hh
/-- The local rho-height window supplies the sharper scale-invariant
 version, retaining its literal original interval and height labels. -/
theorem interval_original_height_density (I : Finset (P × T)) (height : P → ℝ) (Z : Finset ℝ)
    (lo : ℝ) {delta rho C incidenceDensity : ℝ} (hd : 0 < delta) (hdr : delta ≤ rho) (hC : 0 < C)
    (hsep : ∀ z ∈ Z, ∀ w ∈ Z, z ≠ w → delta ≤ |z-w|)
    (hinterval : ∀ z ∈ Z, lo ≤ z ∧ z ≤ lo+rho)
    (hpoints : ∀ t z, ((pointsAt I height t z).card:ℝ) ≤ C)
    (hIncidence : incidenceDensity*rho*(TwoTubePathCollisionCount.tubes I).card ≤ delta*(I.card:ℝ)) :
    (incidenceDensity/(3*C))*(Z.card:ℝ)*(TwoTubePathCollisionCount.tubes I).card ≤
      (vertices I height).card := by
  have hr : 0 < rho := hd.trans_le hdr
  have hc := OriginalSeparatedHeightCap.separated_interval_cap Z hd hsep lo rho hr.le
  have heq : Z.filter (fun z => lo ≤ z ∧ z ≤ lo+rho)=Z := Finset.filter_eq_self.mpr hinterval
  rw [heq] at hc
  have hHeight : delta*(Z.card:ℝ) ≤ 3*rho := by
    have hh := mul_le_mul_of_nonneg_right hc hd.le
    have hid : (rho/delta+2)*delta=rho+2*delta := by field_simp
    rw [hid] at hh
    nlinarith only [hh,hdr]
  have hh := original_average_height_density I height Z hd.le hC (show 0 < 3*rho by positivity) hpoints hIncidence hHeight
  have hid : (incidenceDensity*rho)/(C*(3*rho))=incidenceDensity/(3*C) := by field_simp
  simpa only [hid] using hh
end OriginalHeightVertexDensity
