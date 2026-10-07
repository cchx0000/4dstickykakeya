import Theorems.Thm_StickyKakeya4_native_common_phi_metric

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 14000000
noncomputable section
namespace NativeCommonPhiGrid
open Classical Finset StickyKakeya4 NativeHorizontalGrainSlice NativeGrainQuotientInjection
open NativeReferenceXYGridLinear NativeReferenceXYGridMaps NativeReferenceXYGridMenus
open NativeReferenceXYGridAngularCap NativeGrainQuotientBins NativeCommonPhiMetric
open scoped BigOperators Matrix.Norms.Elementwise

lemma angle_grid_mem_box {r : ℝ} (hr : 0 < r) (K : ℕ) (x y : E4)
    (hxy : ‖x-y‖ ≤ (K:ℝ)*r) : angle r x∈vectorBox (angle r y) K := by
  apply Fintype.mem_piFinset.mpr
  intro j
  apply floor_neighbor hr K
  have hh : |x j.castSucc-y j.castSucc| ≤ ‖x-y‖ := by
    simpa only [PiLp.sub_apply,Real.norm_eq_abs] using PiLp.norm_apply_le (x-y) j.castSucc
  exact hh.trans hxy

/-- Two actual horizontal directions with the same tangent and normal
quotient bins have full distance≤6rho. -/
lemma double_bin_distance (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (ell : ℕ) (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hd : Module.finrank ℝ P=ell-1)
    (F : Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ) (hF : ‖F‖ ≤ (1/4:ℝ))
    {rho : ℝ} (hrho : 0 < rho) (x y : E4) (hx : x∈heightKernel) (hy : y∈heightKernel)
    (ht : label rho (tangentCoordinates P ell hd x)=label rho (tangentCoordinates P ell hd y))
    (hn : label rho (quotientMap P hP ell hell hell4 hd F x)=label rho (quotientMap P hP ell hell hell4 hd F y)) :
    ‖x-y‖ ≤ 6*rho := by
  have htb := same_label_norm_bound hrho _ _ ht
  have hnb := same_label_norm_bound hrho _ _ hn
  have hh := horizontal_inverse P hP ell hell hell4 hd F hF (heightKernel.sub_mem hx hy)
  rw [map_sub,map_sub] at hh
  have hdim : 2*((ell-1:ℕ):ℝ)+((4-ell:ℕ):ℝ) ≤ 6 := by
    exact_mod_cast (show 2*(ell-1)+(4-ell) ≤ 6 by omega)
  have hm := mul_le_mul_of_nonneg_right hdim hrho.le
  nlinarith only [htb,hnb,hh,hm]

/-- Each projected rho-grid fiber meets only a normal-dimensional number
of the actual full angular grid cells at mesh rho/8. -/
theorem inverse_projected_fiber_cap {A : Type*} (S : Finset A) (w : A → E4)
    (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (ell : ℕ) (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hd : Module.finrank ℝ P=ell-1)
    (F : Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ) (hF : ‖F‖ ≤ (1/4:ℝ))
    (xi : EuclideanSpace ℝ (Fin (4-ell))) {rho E : ℝ} (hrho : 0 < rho) (hE : 0 ≤ E)
    (hhorizontal : ∀i∈S,w i∈heightKernel)
    (hres : ∀i∈S,‖quotientMap P hP ell hell hell4 hd F (w i)-xi‖ ≤ E*rho)
    (v : Fin (ell-1) → ℤ) :
    (((S.filter (fun i => label rho (tangentCoordinates P ell hd (w i))=v)).image
      (fun i => angle (rho/8) (w i))).card:ℝ) ≤ (129:ℝ)^3*(2*E+2)^(4-ell) := by
  let I := S.filter (fun i => label rho (tangentCoordinates P ell hd (w i))=v)
  let f := fun i => label rho (quotientMap P hP ell hell hell4 hd F (w i))
  have hnormal : ((I.image f).card:ℝ) ≤ (2*E+2)^(4-ell) := by
    have hh := occupied_card I (fun i => quotientMap P hP ell hell hell4 hd F (w i)) hrho
      (mul_nonneg hE hrho.le) xi (fun i hi => hres i (mem_filter.mp hi).1)
    have he : 2*(E*rho)/rho+2=2*E+2 := by field_simp
    simpa only [he] using hh
  have hfiber : ∀b∈I.image f,(((I.filter (fun i => f i=b)).image
      (fun i => angle (rho/8) (w i))).card:ℝ) ≤ (129:ℝ)^3 := by
    intro b hb
    obtain ⟨j,hj,hjb⟩ := mem_image.mp hb
    have hsub : (I.filter (fun i => f i=b)).image (fun i => angle (rho/8) (w i))⊆
        vectorBox (angle (rho/8) (w j)) 64 := by
      intro a ha
      obtain ⟨i,hi,rfl⟩ := mem_image.mp ha
      obtain ⟨hi,hib⟩ := mem_filter.mp hi
      have hdiam := double_bin_distance P hP ell hell hell4 hd F hF hrho (w i) (w j)
        (hhorizontal i (mem_filter.mp hi).1) (hhorizontal j (mem_filter.mp hj).1)
        ((mem_filter.mp hi).2.trans (mem_filter.mp hj).2.symm) (hib.trans hjb.symm)
      apply angle_grid_mem_box (by positivity) 64 _ _
      nlinarith only [hdiam,hrho]
    have hc := card_le_card hsub
    rw [vectorBox_card] at hc
    exact_mod_cast hc
  have hh := NativeTangentGridCoarsening.image_card_le_real_mul_of_fiber_images I
    (fun i => angle (rho/8) (w i)) f ((129:ℝ)^3) hfiber
  exact hh.trans (mul_le_mul_of_nonneg_left hnormal (by positivity))

/-- Same fine angular bin implies a full Euclidean direction diameter3r.
The fourth component is exactly zero for the actual horizontal slopes. -/
lemma same_angle_distance {r : ℝ} (hr : 0 < r) (x y : E4)
    (hx : x∈heightKernel) (hy : y∈heightKernel) (he : angle r x=angle r y) :
    ‖x-y‖ ≤ 3*r := by
  have hcoord (j : Fin 3) : |x j.castSucc-y j.castSucc| ≤ r :=
    same_floor_abs hr (congrFun he j)
  have hh := euclidean_norm_le_sum (x-y)
  rw [Fin.sum_univ_castSucc] at hh
  change x (3:Fin 4)=0 at hx
  change y (3:Fin 4)=0 at hy
  simp only [PiLp.sub_apply,show (Fin.last 3:Fin 4)=3 by rfl,hx,hy,sub_self,abs_zero,add_zero] at hh
  have hs := sum_le_sum (fun j (_hj : j∈(univ:Finset (Fin 3))) => hcoord j)
  simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul] at hs
  exact hh.trans hs

/-- Forward multiplicity is a fixed3^(ell-1), independently of the field
and offset. Both alphabets consist of actual direction grid labels. -/
theorem forward_projected_fiber_cap {A : Type*} (S : Finset A) (w : A → E4)
    (P : Submodule ℝ E4) (ell : ℕ) (hd : Module.finrank ℝ P=ell-1)
    {rho : ℝ} (hrho : 0 < rho) (hhorizontal : ∀i∈S,w i∈heightKernel)
    (v : Fin 3 → ℤ) :
    ((S.filter (fun i => angle (rho/8) (w i)=v)).image
      (fun i => label rho (tangentCoordinates P ell hd (w i)))).card ≤ 3^(ell-1) := by
  let I := S.filter (fun i => angle (rho/8) (w i)=v)
  change (I.image (fun i => label rho (tangentCoordinates P ell hd (w i)))).card ≤ 3^(ell-1)
  by_cases hn : I.Nonempty
  · obtain ⟨j,hj⟩ := hn
    have hsub : I.image (fun i => label rho (tangentCoordinates P ell hd (w i)))⊆
        vectorBox (label rho (tangentCoordinates P ell hd (w j))) 1 := by
      intro a ha
      obtain ⟨i,hi,rfl⟩ := mem_image.mp ha
      apply Fintype.mem_piFinset.mpr
      intro k
      apply floor_neighbor hrho 1
      have hfull := same_angle_distance (by positivity : (0:ℝ)<rho/8) (w i) (w j)
        (hhorizontal i (mem_filter.mp hi).1) (hhorizontal j (mem_filter.mp hj).1)
        ((mem_filter.mp hi).2.trans (mem_filter.mp hj).2.symm)
      have ht := tangent_distance P ell hd (w i) (w j)
      have hc : |tangentCoordinates P ell hd (w i) k-tangentCoordinates P ell hd (w j) k| ≤
          ‖tangentCoordinates P ell hd (w i)-tangentCoordinates P ell hd (w j)‖ := by
        simpa only [PiLp.sub_apply,Real.norm_eq_abs] using PiLp.norm_apply_le
          (tangentCoordinates P ell hd (w i)-tangentCoordinates P ell hd (w j)) k
      norm_num only [Nat.cast_one,one_mul]
      linarith only [hfull,ht,hc,hrho]
    exact (card_le_card hsub).trans_eq (by rw [vectorBox_card])
  · rw [show I=∅ from not_nonempty_iff_eq_empty.mp hn,image_empty,card_empty]
    positivity

/-- Total actual angular count is bounded by the actual projected grid
count with only the normal-dimensional inverse multiplicity. -/
theorem angular_card_le_projected {A : Type*} (S : Finset A) (w : A → E4)
    (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (ell : ℕ) (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hd : Module.finrank ℝ P=ell-1)
    (F : Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ) (hF : ‖F‖ ≤ (1/4:ℝ))
    (xi : EuclideanSpace ℝ (Fin (4-ell))) {rho E : ℝ} (hrho : 0 < rho) (hE : 0 ≤ E)
    (hhorizontal : ∀i∈S,w i∈heightKernel)
    (hres : ∀i∈S,‖quotientMap P hP ell hell hell4 hd F (w i)-xi‖ ≤ E*rho) :
    ((S.image (fun i => angle (rho/8) (w i))).card:ℝ) ≤
      ((129:ℝ)^3*(2*E+2)^(4-ell))*
        (S.image (fun i => label rho (tangentCoordinates P ell hd (w i)))).card :=
  NativeTangentGridCoarsening.image_card_le_real_mul_of_fiber_images S
    (fun i => angle (rho/8) (w i)) (fun i => label rho (tangentCoordinates P ell hd (w i))) _
    (fun v _ => inverse_projected_fiber_cap S w P hP ell hell hell4 hd F hF xi hrho hE hhorizontal hres v)

end NativeCommonPhiGrid
