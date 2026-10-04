import Theorems.Thm_StickyKakeya4_original_coarse_height_curve
import Theorems.Thm_StickyKakeya4_finite_plane_projection_original_graph
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000
noncomputable section
namespace OriginalSlopeGraphNonconcentration
open Classical OriginalCoarseHeightCurve OriginalSeparatedHeightCap FinitePlaneProjectionGrid
theorem original_affine_avoidance_normalized (Z : Finset ℝ) (f : ℝ → ℝ × ℝ) (z₀ : ℝ) (f₀ : ℝ × ℝ)
    {rho Lip width threshold N : ℝ} (hrho : 0 < rho) (hLip : 0 < Lip)
    (hscale : Lip*rho*width < threshold)
    (havoid : ∀ r u : ℝ × ℝ, ((Z.filter (fun z => ‖f z-z • r-u‖ < threshold)).card : ℝ) ≤ N)
    (a1 a2 c1 c2 : ℝ) :
    ((originalAffineGraphTube Z (heightGraph rho Lip z₀ f₀ f) a1 a2 c1 c2 width).card : ℝ) ≤ N := by
  let r : ℝ × ℝ := (Lip*a1,Lip*a2)
  let u : ℝ × ℝ := (f₀.1+Lip*rho*c1-Lip*a1*z₀,f₀.2+Lip*rho*c2-Lip*a2*z₀)
  have hf {v v0 a c z : ℝ} (hh : |(Lip*rho)⁻¹*(v-v0)-a*((z-z₀)/rho)-c| ≤ width) :
      |v-z*(Lip*a)-(v0+Lip*rho*c-Lip*a*z₀)| < threshold := by
    have hid : v-z*(Lip*a)-(v0+Lip*rho*c-Lip*a*z₀)=(Lip*rho)*((Lip*rho)⁻¹*(v-v0)-a*((z-z₀)/rho)-c) := by
      field_simp
      ring
    rw [hid,abs_mul,abs_of_pos (mul_pos hLip hrho)]
    exact (mul_le_mul_of_nonneg_left hh (mul_pos hLip hrho).le).trans_lt hscale
  have hsub : originalAffineGraphTube Z (heightGraph rho Lip z₀ f₀ f) a1 a2 c1 c2 width ⊆
      Z.filter (fun z => ‖f z-z • r-u‖ < threshold) := by
    intro z hz
    obtain ⟨hzZ,hz1,hz2⟩ := Finset.mem_filter.mp hz
    apply Finset.mem_filter.mpr
    refine ⟨hzZ,?_⟩
    exact max_lt (hf hz1) (hf hz2)
  exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans (havoid r u)
theorem original_normalized_height_cap (Z : Finset ℝ) (f : ℝ → ℝ × ℝ) (z₀ : ℝ) (f₀ : ℝ × ℝ)
    {rho Lip delta R : ℝ} (hrho : 0 < rho) (hd : 0 < delta) (hR : 0 ≤ R)
    (hsep : ∀ z ∈ Z, ∀ z' ∈ Z, z ≠ z' → delta ≤ |z-z'|) (c : ℝ) :
    ((Z.filter (fun z => |(heightGraph rho Lip z₀ f₀ f z).1-c| ≤ R)).card : ℝ) ≤ 2*rho*R/delta+2 := by
  have hsub : Z.filter (fun z => |(heightGraph rho Lip z₀ f₀ f z).1-c| ≤ R) ⊆
      Z.filter (fun z => rho*(c-R)+z₀ ≤ z ∧ z ≤ rho*(c-R)+z₀+2*rho*R) := by
    intro z hz
    obtain ⟨hzZ,hzR⟩ := Finset.mem_filter.mp hz
    change |(z-z₀)/rho-c| ≤ R at hzR
    obtain ⟨hl,hu⟩ := abs_le.mp hzR
    have hl' : c-R ≤ (z-z₀)/rho := by linarith
    have hu' : (z-z₀)/rho ≤ c+R := by linarith
    have hl'' := (le_div_iff₀ hrho).mp hl'
    have hu'' := (div_le_iff₀ hrho).mp hu'
    exact Finset.mem_filter.mpr ⟨hzZ,by nlinarith,by nlinarith⟩
  exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans
    (separated_interval_cap Z hd hsep (rho*(c-R)+z₀) (2*rho*R) (by positivity))
theorem original_slope_graph_cross_tube_bound (Z : Finset ℝ) (f : ℝ → ℝ × ℝ) (z₀ : ℝ) (f₀ : ℝ × ℝ)
    {rho Lip delta w eta threshold N kappa epsilon : ℝ}
    (hrho : 0 < rho) (hLip : 0 < Lip) (hd : 0 < delta) (hw : 0 ≤ w) (heta : 0 < eta) (heta1 : eta ≤ 1)
    (hsep : ∀ z ∈ Z, ∀ z' ∈ Z, z ≠ z' → delta ≤ |z-z'|)
    (hbounded : ∀ z ∈ Z, |(heightGraph rho Lip z₀ f₀ f z).2.1| ≤ 1 ∧ |(heightGraph rho Lip z₀ f₀ f z).2.2| ≤ 1)
    (havoid : ∀ r u : ℝ × ℝ, ((Z.filter (fun z => ‖f z-z • r-u‖ < threshold)).card : ℝ) ≤ N)
    (hscale : Lip*rho*(w/eta) < threshold)
    (hheightbudget : 2*rho*(w+2*eta)/delta+2 ≤ kappa*(Z.card : ℝ))
    (haffinebudget : N ≤ epsilon*(Z.card : ℝ)) {i k : ℝ} (hi : i ∈ Z) (hk : k ∈ Z)
    (hsecant : 0 < dist3 (heightGraph rho Lip z₀ f₀ f i) (heightGraph rho Lip z₀ f₀ f k)) :
    ((originalCrossTube Z (heightGraph rho Lip z₀ f₀ f) i k w).card : ℝ) ≤ max kappa epsilon*(Z.card : ℝ) := by
  apply originalCrossTube_card_of_height_affine_caps Z (heightGraph rho Lip z₀ f₀ f) hw heta heta1 hbounded
  · intro c
    exact (original_normalized_height_cap Z f z₀ f₀ hrho hd (by positivity) hsep c).trans hheightbudget
  · intro a1 a2 c1 c2
    exact (original_affine_avoidance_normalized Z f z₀ f₀ hrho hLip hscale havoid a1 a2 c1 c2).trans haffinebudget
  · exact hi
  · exact hk
  · exact hsecant
end OriginalSlopeGraphNonconcentration
