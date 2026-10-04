import Theorems.Thm_StickyKakeya4_original_three_dimensional_slab_overlap
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3200000

noncomputable section
open scoped Matrix BigOperators
namespace OriginalThreeDimensionalNarrowSlabOverlap
open Classical Matrix OriginalThreeDimensionalBandGeometry OriginalThreeDimensionalTubeSlab
open OriginalThreeDimensionalCrossGeometry OriginalThreeDimensionalSlabOverlap

/-- Weighted Cramer identity keeps the two actual slab errors separate. -/
theorem original_weighted_cramer_bound (c v w : Point3) (Ev Ew V W : ℝ) (l : Fin 3)
    (hEv : 0≤Ev) (_hEw : 0≤Ew) (hV : 0≤V) (_hW : 0≤W)
    (hv : ∀ i, |v i|≤V) (hw : ∀ i, |w i|≤W)
    (hcv : ∀ i j, |minor3 c v i j|≤Ev)
    (hcw : ∀ i j, |minor3 c w i j|≤Ew) :
    ∀ i j, |c l| * |minor3 v w i j|≤2*Ev*W+V*Ew := by
  intro i j
  have hid : c l*minor3 v w i j=
      minor3 c v l i*w j-minor3 c v l j*w i+v l*minor3 c w i j := by dsimp [minor3]; ring
  have h1 := mul_le_mul (hcv l i) (hw j) (abs_nonneg _) hEv
  have h2 := mul_le_mul (hcv l j) (hw i) (abs_nonneg _) hEv
  have h3 := mul_le_mul (hv l) (hcw i j) (abs_nonneg _) hV
  have ht1 := abs_sub (minor3 c v l i*w j) (minor3 c v l j*w i)
  have ht2 := abs_add_le (minor3 c v l i*w j-minor3 c v l j*w i) (v l*minor3 c w i j)
  rw [← hid,abs_mul,abs_mul] at ht2
  rw [abs_mul,abs_mul] at ht1
  linarith only [h1,h2,h3,ht1,ht2]

private theorem dot_residual_difference (n p q : Point3) (c A B : ℝ)
    (hp : |n ⬝ᵥ p-c|≤A) (hq : |n ⬝ᵥ q-c|≤B) : |n ⬝ᵥ (q-p)|≤A+B := by
  rw [dotProduct_sub]
  have hh := abs_sub (n ⬝ᵥ q-c) (n ⬝ᵥ p-c)
  have he : (n ⬝ᵥ q-c)-(n ⬝ᵥ p-c)=n ⬝ᵥ q-n ⬝ᵥ p := by ring
  rw [he] at hh
  linarith only [hh,hp,hq]

/-- Endpoints belong to the ORIGINAL 3rho slabs, while x belongs to the
D enlargements. Using the actual pair length cancels its loss in the D
term; 54rho<=Dr pays the remaining endpoint error. -/
theorem original_narrow_slabs_force_pair_tube
    (p q x n m : Point3) (cn cm rho D r g : ℝ)
    (hrho : 0≤rho) (hD : 0<D) (hr : 0<r) (hg : 0<g)
    (hwidth : 3*rho≤D) (hscale : 54*rho≤D*r)
    (hn : normSq3 n=1) (hm : normSq3 m=1)
    (hp : ∀ i, |p i|≤1) (hx : ∀ i, |x i|≤1) (hsep : r≤distance3 p q)
    (hminus : g≤distance3 n m) (hplus : g≤distance3 n (-m))
    (hnp : |n ⬝ᵥ p-cn|≤3*rho) (hnq : |n ⬝ᵥ q-cn|≤3*rho) (hnx : |n ⬝ᵥ x-cn|≤D)
    (hmp : |m ⬝ᵥ p-cm|≤3*rho) (hmq : |m ⬝ᵥ q-cm|≤3*rho) (hmx : |m ⬝ᵥ x-cm|≤D) :
    x∈physicalTube3 p q (30*D/g) := by
  let v := q-p
  let w := x-p
  let c := n ⨯₃ m
  let R := distance3 p q
  have hR : 0<R := hr.trans_le hsep
  obtain ⟨l,_hmax,hgap⟩ := original_projective_gap_cross_coordinate n m g hn hm hg hminus hplus
  have hc : 0< |c l| := by dsimp [c]; nlinarith only [hgap,hg]
  have hnv : |n ⬝ᵥ v|≤2*(3*rho) := by
    have hh := dot_residual_difference n p q cn (3*rho) (3*rho) hnp hnq
    change |n ⬝ᵥ v|≤_ at hh
    linarith only [hh]
  have hmv : |m ⬝ᵥ v|≤2*(3*rho) := by
    have hh := dot_residual_difference m p q cm (3*rho) (3*rho) hmp hmq
    change |m ⬝ᵥ v|≤_ at hh
    linarith only [hh]
  have hnw : |n ⬝ᵥ w|≤2*D := by
    have hh := dot_residual_difference n p x cn (3*rho) D hnp hnx
    change |n ⬝ᵥ w|≤_ at hh
    linarith only [hh,hwidth]
  have hmw : |m ⬝ᵥ w|≤2*D := by
    have hh := dot_residual_difference m p x cm (3*rho) D hmp hmx
    change |m ⬝ᵥ w|≤_ at hh
    linarith only [hh,hwidth]
  have hcv := original_cross_normal_minor_bound n m v (3*rho) (by positivity) hn hm hnv hmv
  have hcw := original_cross_normal_minor_bound n m w D hD.le hn hm hnw hmw
  have hv (i : Fin 3) : |v i|≤R := by
    simpa only [v,R,Pi.sub_apply,abs_sub_comm] using original_coordinate_le_distance p q i
  have hw (i : Fin 3) : |w i|≤2 := by
    have hh := abs_sub (x i) (p i)
    dsimp [w]
    linarith only [hh,hx i,hp i]
  have hcramer := original_weighted_cramer_bound c v w (4*(3*rho)) (4*D) R 2 l
    (by positivity) (by positivity) hR.le (by norm_num) hv hw hcv hcw
  have hminor (i j : Fin 3) : |minor3 v w i j|≤(48*rho+4*D*R)/|c l| := by
    apply (le_div_iff₀ hc).mpr
    nlinarith only [hcramer i j]
  have hcross : ∀ i, |(v ⨯₃ w) i|≤(48*rho+4*D*R)/|c l| := by
    intro i
    fin_cases i
    · exact hminor 1 2
    · exact hminor 2 0
    · exact hminor 0 1
  obtain ⟨a,ha⟩ := original_cross_bound_physical_tube p q x R ((48*rho+4*D*R)/|c l|)
    hR (by positivity) le_rfl hcross
  have hscaleR : 54*rho≤D*R := hscale.trans (mul_le_mul_of_nonneg_left hsep hD.le)
  have hpoly : 96*rho+8*D*R≤10*D*R := by nlinarith only [hscaleR,hrho]
  have hfirst : 2*((48*rho+4*D*R)/|c l|)/R≤10*D/|c l| := by
    have he : 2*((48*rho+4*D*R)/|c l|)/R=(96*rho+8*D*R)/(|c l| * R) := by field_simp; ring
    rw [he]
    apply (div_le_div_iff₀ (mul_pos hc hR) hc).mpr
    have hh := mul_le_mul_of_nonneg_right hpoly hc.le
    nlinarith only [hh]
  have hsecond : 10*D/|c l|≤30*D/g := by
    apply (div_le_div_iff₀ hc hg).mpr
    have hh := mul_le_mul_of_nonneg_left hgap (show 0≤10*D by positivity)
    dsimp [c]
    nlinarith only [hh]
  exact ⟨a,ha.trans (hfirst.trans hsecond)⟩

/-- A shared original point outside the inner tube forces the true
unoriented normal gap below 30D/tau, with no inverse-r factor. -/
theorem original_shared_narrow_slab_point_forces_close_normals
    (p q x n m : Point3) (cn cm rho D r tau : ℝ)
    (hrho : 0≤rho) (hD : 0<D) (hr : 0<r) (htau : 0<tau)
    (hwidth : 3*rho≤D) (hscale : 54*rho≤D*r)
    (hn : normSq3 n=1) (hm : normSq3 m=1)
    (hp : ∀ i, |p i|≤1) (hx : ∀ i, |x i|≤1) (hsep : r≤distance3 p q)
    (hnp : |n ⬝ᵥ p-cn|≤3*rho) (hnq : |n ⬝ᵥ q-cn|≤3*rho) (hnx : |n ⬝ᵥ x-cn|≤D)
    (hmp : |m ⬝ᵥ p-cm|≤3*rho) (hmq : |m ⬝ᵥ q-cm|≤3*rho) (hmx : |m ⬝ᵥ x-cm|≤D)
    (hout : x∉physicalTube3 p q tau) :
    min (distance3 n m) (distance3 n (-m))<30*D/tau := by
  by_contra hh
  have hgap := le_min_iff.mp (le_of_not_gt hh)
  have hin := original_narrow_slabs_force_pair_tube p q x n m cn cm rho D r (30*D/tau)
    hrho hD hr (by positivity) hwidth hscale hn hm hp hx hsep hgap.1 hgap.2 hnp hnq hnx hmp hmq hmx
  have he : 30*D/(30*D/tau)=tau := by field_simp
  rw [he] at hin
  exact hout hin

end OriginalThreeDimensionalNarrowSlabOverlap
