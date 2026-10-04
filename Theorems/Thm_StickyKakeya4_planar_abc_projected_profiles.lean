import Theorems.Thm_StickyKakeya4_finite_plane_projection_graph_final
import Theorems.Thm_StickyKakeya4_planar_abc_balanced_normalization
import Theorems.Thm_StickyKakeya4_actual_abc_image_assembly
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000
noncomputable section
namespace PlanarABCProjectedProfiles
open Classical FinitePlaneProjectionGrid PlanarABCBalancedNormalization ActualABCImageAssembly
open FiniteVoronoiPopulation
variable {X : Type*}
lemma source_injOn (S : Finset X) (p : X → Point3) (uv : ℝ × ℝ) {rho : ℝ} (hrho : 0 < rho)
    (hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → 2*rho < ‖projectionLinear uv (p i)-projectionLinear uv (p j)‖) :
    Set.InjOn (fun i => source (projectionLinear uv (p i))) (↑S) := by
  intro i hi j hj he
  by_contra hne
  have hh := hsep i hi j hj hne
  have hp := PlanarABCBalancedNormalization.source_injective he
  rw [hp,sub_self,norm_zero] at hh
  linarith
lemma direction_injOn (S : Finset X) (p : X → Point3) (uv : ℝ × ℝ) (anchor : Point3)
    {rho : ℝ} (hrho : 0 < rho)
    (hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → 2*rho < ‖projectionLinear uv (p i)-projectionLinear uv (p j)‖) :
    Set.InjOn (fun i => direction (projectionLinear uv anchor) (projectionLinear uv (p i))) (↑S) := by
  intro i hi j hj he
  by_contra hne
  have hh := hsep i hi j hj hne
  have hp := PlanarABCBalancedNormalization.direction_injective (projectionLinear uv anchor) he
  rw [hp,sub_self,norm_zero] at hh
  linarith
lemma source_image_separated (S : Finset X) (p : X → Point3) (uv : ℝ × ℝ) {rho : ℝ} (hrho : 0 < rho)
    (hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → 2*rho < ‖projectionLinear uv (p i)-projectionLinear uv (p j)‖) :
    Separated (S.image (fun i => source (projectionLinear uv (p i)))) (rho/8) := by
  intro a ha b hb hab
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hb
  have hij : i ≠ j := by intro h; subst j; exact hab rfl
  have hh := hsep i hi j hj hij
  rw [dist_eq_norm]
  change rho/8 ≤ ‖(1/8:ℝ) • projectionLinear uv (p i)-(1/8:ℝ) • projectionLinear uv (p j)‖
  rw [← smul_sub,norm_smul]
  norm_num
  linarith
lemma direction_image_separated (S : Finset X) (p : X → Point3) (uv : ℝ × ℝ) (anchor : Point3)
    {rho : ℝ} (hrho : 0 < rho)
    (hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → 2*rho < ‖projectionLinear uv (p i)-projectionLinear uv (p j)‖) :
    Separated (S.image (fun i => direction (projectionLinear uv anchor) (projectionLinear uv (p i)))) (rho/8) := by
  intro a ha b hb hab
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hb
  have hij : i ≠ j := by intro h; subst j; exact hab rfl
  have hh := hsep i hi j hj hij
  rw [dist_eq_norm]
  have hid : direction (projectionLinear uv anchor) (projectionLinear uv (p i))-
      direction (projectionLinear uv anchor) (projectionLinear uv (p j))=
      (1/4:ℝ) • (projectionLinear uv (p i)-projectionLinear uv (p j)) := by unfold direction; module
  rw [hid,norm_smul]
  norm_num
  linarith
/-- Exact actual-image population after the balanced B normalization. -/
theorem direction_image_ball_bound (S : Finset X) (p : X → Point3) (uv : ℝ × ℝ) (anchor : Point3)
    {rho K : ℝ} (hrho : 0 < rho) (hK : 0 ≤ K)
    (hinj : Set.InjOn (fun i => direction (projectionLinear uv anchor) (projectionLinear uv (p i))) (↑S))
    (hball : ∀ center : ℝ × ℝ, ∀ R : ℝ, rho ≤ R →
      ((S.filter (fun i => ‖projectionLinear uv (p i)-center‖ ≤ R)).card : ℝ) ≤ K*R/rho)
    (center : ℝ × ℝ) {R : ℝ} (hR : rho/8 ≤ R) :
    (((S.image (fun i => direction (projectionLinear uv anchor) (projectionLinear uv (p i)))).filter
      (fun b => ‖b-center‖ ≤ R)).card : ℝ) ≤ K*R/(rho/8) := by
  rw [filtered_image_card S _ hinj]
  have hR0 : 0 ≤ R := by linarith
  have hsub : S.filter (fun i => ‖direction (projectionLinear uv anchor) (projectionLinear uv (p i))-center‖ ≤ R) ⊆
      S.filter (fun i => ‖projectionLinear uv (p i)-((4:ℝ) • center+projectionLinear uv anchor)‖ ≤ max rho (4*R)) := by
    intro i hi
    obtain ⟨hiS,hiR⟩ := Finset.mem_filter.mp hi
    have hid : projectionLinear uv (p i)-((4:ℝ) • center+projectionLinear uv anchor)=
        (4:ℝ) • (direction (projectionLinear uv anchor) (projectionLinear uv (p i))-center) := by unfold direction; module
    have hh : ‖projectionLinear uv (p i)-((4:ℝ) • center+projectionLinear uv anchor)‖ ≤ 4*R := by
      rw [hid,norm_smul]
      norm_num
      linarith
    exact Finset.mem_filter.mpr ⟨hiS,hh.trans (le_max_right _ _)⟩
  have hc := (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans
    (hball ((4:ℝ) • center+projectionLinear uv anchor) (max rho (4*R)) (le_max_left _ _))
  have hm : max rho (4*R) ≤ 8*R := max_le (by linarith) (by linarith)
  calc
    _ ≤ K*(max rho (4*R))/rho := hc
    _ ≤ K*(8*R)/rho := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hm hK) hrho.le
    _ = K*R/(rho/8) := by field_simp
/-- Normalized B strip counts are the original projected strip counts at
 width4r and an explicitly translated line offset. -/
theorem direction_image_strip_bound (S : Finset X) (p : X → Point3) (uv : ℝ × ℝ) (anchor : Point3)
    {w fraction : ℝ}
    (hinj : Set.InjOn (fun i => direction (projectionLinear uv anchor) (projectionLinear uv (p i))) (↑S))
    (hline : ∀ a d c : ℝ, max |a| |d|=1 →
      ((projectedLineStrip S p uv a d c w).card : ℝ) ≤ fraction*(S.card : ℝ))
    (a d c : ℝ) (hnormal : max |a| |d|=1) :
    (((S.image (fun i => direction (projectionLinear uv anchor) (projectionLinear uv (p i)))).filter
      (fun b => |a*b.1+d*b.2-c| ≤ w/4)).card : ℝ) ≤
      fraction*((S.image (fun i => direction (projectionLinear uv anchor) (projectionLinear uv (p i)))).card : ℝ) := by
  rw [filtered_image_card S _ hinj,Finset.card_image_of_injOn hinj]
  have hsub : S.filter (fun i => |a*(direction (projectionLinear uv anchor) (projectionLinear uv (p i))).1+
      d*(direction (projectionLinear uv anchor) (projectionLinear uv (p i))).2-c| ≤ w/4) ⊆
      projectedLineStrip S p uv a d (4*c+a*(projectionLinear uv anchor).1+d*(projectionLinear uv anchor).2) w := by
    intro i hi
    obtain ⟨hiS,hiL⟩ := Finset.mem_filter.mp hi
    refine Finset.mem_filter.mpr ⟨hiS,?_⟩
    change |a*(projectionLinear uv (p i)).1+d*(projectionLinear uv (p i)).2-
      (4*c+a*(projectionLinear uv anchor).1+d*(projectionLinear uv anchor).2)| ≤ w
    change |a*((1/4)*((projectionLinear uv (p i)).1-(projectionLinear uv anchor).1))+
      d*((1/4)*((projectionLinear uv (p i)).2-(projectionLinear uv anchor).2))-c| ≤ w/4 at hiL
    have hid : a*(projectionLinear uv (p i)).1+d*(projectionLinear uv (p i)).2-
        (4*c+a*(projectionLinear uv anchor).1+d*(projectionLinear uv anchor).2)=
        4*(a*((1/4)*((projectionLinear uv (p i)).1-(projectionLinear uv anchor).1))+
          d*((1/4)*((projectionLinear uv (p i)).2-(projectionLinear uv anchor).2))-c) := by ring
    rw [hid,abs_mul]
    norm_num
    linarith
  exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans (hline a d _ hnormal)
end PlanarABCProjectedProfiles
