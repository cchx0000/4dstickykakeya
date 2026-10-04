import Theorems.Thm_StickyKakeya4_original_three_dimensional_tube_parameters
import Theorems.Thm_StickyKakeya4_original_tube_parameter_integer_count
import Theorems.Thm_StickyKakeya4_original_three_dimensional_tube_frostman
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 6000000

/- OriginalTubeGraphPairGeometry -/
noncomputable section
namespace OriginalTubeGraphPairGeometry
open OriginalThreeDimensionalBandGeometry OriginalThreeDimensionalTubeSlab

lemma original_box_distance_le_four (x y : Point3)
    (hx : ∀ j, |x j|≤1) (hy : ∀ j, |y j|≤1) : distance3 x y≤4 := by
  have hcoord (j : Fin 3) : |x j-y j|≤2 := by
    exact (abs_sub (x j) (y j)).trans (by linarith only [hx j,hy j])
  have hs (j : Fin 3) : (x j-y j)^2≤4 := by
    have hh := pow_le_pow_left₀ (abs_nonneg _) (hcoord j) 2
    nlinarith only [hh,sq_abs (x j-y j)]
  unfold distance3
  apply (Real.sqrt_le_left (by norm_num : (0:ℝ)≤4)).mpr
  linarith only [hs 0,hs 1,hs 2]

lemma graph_pair_residual (x y : Point3) (s b : Fin 3→ℝ) (i : Fin 3) (rho : ℝ)
    (hx : ∀ j, |x j-(s j*x i+b j)|≤16*rho)
    (hy : ∀ j, |y j-(s j*y i+b j)|≤16*rho) :
    ∀ j, |(y j-x j)-s j*(y i-x i)|≤32*rho := by
  intro j
  have ht := abs_sub (y j-(s j*y i+b j)) (x j-(s j*x i+b j))
  have he : (y j-(s j*y i+b j))-(x j-(s j*x i+b j))=
      (y j-x j)-s j*(y i-x i) := by ring
  rw [he] at ht
  linarith only [ht,hx j,hy j]

lemma graph_separation_large_coordinate (x y : Point3) (s b : Fin 3→ℝ)
    (i : Fin 3) (rho : ℝ) (hrho : 0 ≤ rho)
    (hs : ∀ j, |s j|≤1)
    (hx : ∀ j, |x j-(s j*x i+b j)|≤16*rho)
    (hy : ∀ j, |y j-(s j*y i+b j)|≤16*rho)
    (hfar : 128*rho≤distance3 x y) :
    distance3 x y≤4*|y i-x i| := by
  have hres := graph_pair_residual x y s b i rho hx hy
  have hcoord (j : Fin 3) : |y j-x j|≤|y i-x i|+32*rho := by
    have ht := abs_add_le ((y j-x j)-s j*(y i-x i)) (s j*(y i-x i))
    rw [sub_add_cancel,abs_mul] at ht
    have hm := mul_le_mul_of_nonneg_right (hs j) (abs_nonneg (y i-x i))
    linarith only [ht,hm,hres j]
  have hB : 0 ≤ |y i-x i|+32*rho := by positivity
  have hsquare (j : Fin 3) : (x j-y j)^2≤(|y i-x i|+32*rho)^2 := by
    have hh := pow_le_pow_left₀ (abs_nonneg _) (hcoord j) 2
    simpa only [sq_abs,sub_sq_comm (y j) (x j)] using hh
  have hd : distance3 x y≤2*(|y i-x i|+32*rho) := by
    unfold distance3
    apply (Real.sqrt_le_left (by positivity : 0 ≤ 2*(|y i-x i|+32*rho))).mpr
    nlinarith only [hsquare 0,hsquare 1,hsquare 2,sq_nonneg (|y i-x i|+32*rho)]
  linarith only [hd,hfar]

lemma graph_slope_concentration (x y : Point3) (s b : Fin 3→ℝ)
    (i : Fin 3) (rho : ℝ) (hrho : 0 < rho)
    (hs : ∀ j, |s j|≤1)
    (hx : ∀ j, |x j-(s j*x i+b j)|≤16*rho)
    (hy : ∀ j, |y j-(s j*y i+b j)|≤16*rho)
    (hfar : 128*rho≤distance3 x y) :
    ∀ j, |s j-(y j-x j)/(y i-x i)|≤128*rho/distance3 x y := by
  have hd : 0 < distance3 x y := (by positivity : 0 < 128*rho).trans_le hfar
  have hlarge := graph_separation_large_coordinate x y s b i rho hrho.le hs hx hy hfar
  have hA : 0 < |y i-x i| := by linarith only [hd,hlarge]
  have hne : y i-x i≠0 := abs_pos.mp hA
  have hres := graph_pair_residual x y s b i rho hx hy
  intro j
  have he : s j-(y j-x j)/(y i-x i)= -(((y j-x j)-s j*(y i-x i))/(y i-x i)) := by
    field_simp
    ring
  rw [he,abs_neg,abs_div]
  apply (div_le_div_of_nonneg_right (hres j) hA.le).trans
  apply (div_le_div_iff₀ hA hd).mpr
  have hm := mul_le_mul_of_nonneg_left hlarge (show 0 ≤ 32*rho by positivity)
  nlinarith only [hm]

end OriginalTubeGraphPairGeometry

end

/- OriginalThreeDimensionalTubePairCount -/
noncomputable section
namespace OriginalThreeDimensionalTubePairCount
open Classical OriginalThreeDimensionalBandGeometry OriginalThreeDimensionalHeavySlabs
open OriginalThreeDimensionalTubeSlab OriginalThreeDimensionalTubeParameters
open OriginalThreeDimensionalCapCount OriginalTubeParameterIntegerCount OriginalTubeGraphPairGeometry

lemma graph_offset_floor_residual (rho s b u v : ℝ) (k : ℤ)
    (hrho : 0 < rho) (hu : |u|≤1) (hk : ⌊s/rho⌋=k)
    (hres : |v-(s*u+b)|≤16*rho) :
    |rho*(⌊b/rho⌋:ℤ)-(v-rho*(k:ℝ)*u)|≤18*rho := by
  have hs := floor_mesh_error rho s hrho
  rw [hk] at hs
  have hb := floor_mesh_error rho b hrho
  have hm := mul_le_mul hs hu (abs_nonneg u) hrho.le
  have ht1 := abs_add_le (rho*(⌊b/rho⌋:ℤ)-b) (-(v-(s*u+b)))
  have ht2 := abs_add_le ((rho*(⌊b/rho⌋:ℤ)-b)+(-(v-(s*u+b)))) ((rho*(k:ℝ)-s)*u)
  simp only [abs_neg,abs_mul] at ht1 ht2
  have he : (rho*(⌊b/rho⌋:ℤ)-b)+(-(v-(s*u+b)))+(rho*(k:ℝ)-s)*u=
      rho*(⌊b/rho⌋:ℤ)-(v-rho*(k:ℝ)*u) := by ring
  rw [he] at ht2
  linarith only [hb,hres,hm,ht1,ht2]

lemma original_slope_self (z : Pair3) (i : Fin 3) (hne : z.2 i-z.1 i≠0) :
    slope z i i=1 := div_self hne

lemma original_offset_self (z : Pair3) (i : Fin 3) (hne : z.2 i-z.1 i≠0) :
    offset z i i=0 := by
  rw [offset,original_slope_self z i hne,one_mul,sub_self]

lemma original_offset_fiber_card (S : Finset Pair3) (rho : ℝ) (i : Fin 3)
    (x : Point3) (k : Fin 3→ℤ) (hrho : 0 < rho) (hx : ∀ j, |x j|≤1)
    (hne : ∀ z∈S, z.2 i-z.1 i≠0)
    (hcell : Set.InjOn (parameterCell rho i) (↑S : Set Pair3))
    (hslope : ∀ z∈S, (parameterCell rho i z).1=k)
    (hres : ∀ z∈S, ∀ j, |x j-(slope z i j*x i+offset z i j)|≤16*rho) :
    (S.card : ℝ)≤1444 := by
  let f : Pair3→(Fin 3→ℤ) := fun z => (parameterCell rho i z).2
  let B := S.image f
  have hinj : Set.InjOn f (↑S : Set Pair3) := by
    intro z hz v hv he
    apply hcell hz hv
    exact Prod.ext ((hslope z hz).trans (hslope v hv).symm) he
  have hcard : B.card=S.card := Finset.card_image_of_injOn hinj
  have hfixed : ∀ b∈B, b i=0 := by
    intro b hb
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hb
    dsimp [f,parameterCell]
    rw [original_offset_self z i (hne z hz)]
    simp
  have hbound : ∀ j : Fin 3, j≠i → ((B.image (fun b => b j)).card : ℝ)*1≤38 := by
    intro j _hji
    have hh := integer_interval_mass (B.image (fun b => b j)) rho (18*rho)
      (x j-rho*(k j:ℝ)*x i) hrho (by positivity) (by
        intro l hl
        obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hl
        obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hb
        exact graph_offset_floor_residual rho (slope z i j) (offset z i j) (x i) (x j) (k j)
          hrho (hx i) (congrFun (hslope z hz) j) (hres z hz j))
    have hh' : ((B.image (fun b => b j)).card : ℝ)*rho≤38*rho := by linarith only [hh]
    simpa only [mul_one] using (mul_le_mul_iff_of_pos_right hrho).mp hh'
  have hh := three_fixed_coordinate_mass B i 0 1 38 (by norm_num) (by norm_num) hfixed hbound
  rw [hcard] at hh
  norm_num at hh ⊢
  exact hh

lemma original_parameter_count_from_slope_bins (S : Finset Pair3) (rho T M : ℝ)
    (i : Fin 3) (x : Point3) (hrho : 0 < rho) (hT : 0 ≤ T) (hM : 0 ≤ M)
    (hx : ∀ j, |x j|≤1) (hne : ∀ z∈S, z.2 i-z.1 i≠0)
    (hcell : Set.InjOn (parameterCell rho i) (↑S : Set Pair3))
    (hres : ∀ z∈S, ∀ j, |x j-(slope z i j*x i+offset z i j)|≤16*rho)
    (hbins : ∀ j : Fin 3, j≠i → ((S.image (fun z => ⌊slope z i j/rho⌋)).card : ℝ)*T≤M) :
    (S.card : ℝ)*T^2≤1444*M^2 := by
  let f : Pair3→(Fin 3→ℤ) := fun z => (parameterCell rho i z).1
  let B := S.image f
  have hfixed : ∀ b∈B, b i=⌊1/rho⌋ := by
    intro b hb
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hb
    dsimp [f,parameterCell]
    rw [original_slope_self z i (hne z hz)]
  have hbound : ∀ j : Fin 3, j≠i → ((B.image (fun b => b j)).card : ℝ)*T≤M := by
    intro j hji
    simpa only [B,f,Finset.image_image,Function.comp_def,parameterCell] using hbins j hji
  have hslopes := three_fixed_coordinate_mass B i ⌊1/rho⌋ T M hT hM hfixed hbound
  have hfiber : ∀ k∈S.image f, ((S.filter (fun z => f z=k)).card : ℝ)*1≤1444 := by
    intro k _hk
    simp only [mul_one]
    apply original_offset_fiber_card (S.filter (fun z => f z=k)) rho i x k hrho hx
    · intro z hz
      exact hne z (Finset.mem_filter.mp hz).1
    · intro z hz v hv he
      exact hcell (Finset.mem_filter.mp hz).1 (Finset.mem_filter.mp hv).1 he
    · intro z hz
      exact (Finset.mem_filter.mp hz).2
    · intro z hz
      exact hres z (Finset.mem_filter.mp hz).1
  have hc := weighted_fiber_count S f 1 1444 hfiber
  have hm := mul_le_mul_of_nonneg_right hc (sq_nonneg T)
  have hn := mul_le_mul_of_nonneg_left hslopes (by norm_num : (0:ℝ)≤1444)
  change (B.card : ℝ)*T^2≤M^2 at hslopes
  change (S.card : ℝ)*1*T^2≤1444*(B.card : ℝ)*T^2 at hm
  nlinarith only [hm,hn]

/-- Exact multiplicity for distinct literal original tube-parameter cells.
Only actual pair lines and their physical 8rho-neighborhoods occur. -/
theorem original_two_point_tube_count (S : Finset Pair3) (rho : ℝ) (i : Fin 3)
    (x y : Point3) (hrho : 0 < rho) (hrho1 : rho≤1)
    (hx : ∀ j, |x j|≤1) (hy : ∀ j, |y j|≤1)
    (hne : ∀ z∈S, z.2 i-z.1 i≠0)
    (hmax : ∀ z∈S, ∀ j, |z.2 j-z.1 j|≤|z.2 i-z.1 i|)
    (hcell : Set.InjOn (parameterCell rho i) (↑S : Set Pair3))
    (hthrough : ∀ z∈S, x∈physicalTube3 z.1 z.2 (8*rho) ∧ y∈physicalTube3 z.1 z.2 (8*rho)) :
    (S.card : ℝ)*(max (distance3 x y) rho)^2≤1000000000 := by
  have hd4 := original_box_distance_le_four x y hx hy
  have hs : ∀ z∈S, ∀ j, |slope z i j|≤1 := fun z hz => original_slope_bound z i (hne z hz) (hmax z hz)
  have hresx : ∀ z∈S, ∀ j, |x j-(slope z i j*x i+offset z i j)|≤16*rho := by
    intro z hz j
    have hh := original_tube_graph_residual z i x (8*rho) (hne z hz) (hmax z hz) (hthrough z hz).1 j
    linarith only [hh]
  have hresy : ∀ z∈S, ∀ j, |y j-(slope z i j*y i+offset z i j)|≤16*rho := by
    intro z hz j
    have hh := original_tube_graph_residual z i y (8*rho) (hne z hz) (hmax z hz) (hthrough z hz).2 j
    linarith only [hh]
  by_cases hfar : 128*rho≤distance3 x y
  · have hd : 0 < distance3 x y := (by positivity : 0 < 128*rho).trans_le hfar
    have hbins : ∀ j : Fin 3, j≠i →
        ((S.image (fun z => ⌊slope z i j/rho⌋)).card : ℝ)*distance3 x y≤272 := by
      intro j _hji
      have hinterval : ∀ k∈S.image (fun z => ⌊slope z i j/rho⌋),
          |rho*(k:ℝ)-(y j-x j)/(y i-x i)|≤128*rho/distance3 x y+rho := by
        intro k hk
        obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hk
        have hclose := graph_slope_concentration x y (slope z i) (offset z i) i rho hrho
          (hs z hz) (hresx z hz) (hresy z hz) hfar j
        have hfloor := floor_mesh_error rho (slope z i j) hrho
        have ht := abs_add_le (rho*(⌊slope z i j/rho⌋:ℤ)-slope z i j)
          (slope z i j-(y j-x j)/(y i-x i))
        rw [sub_add_sub_cancel] at ht
        linarith only [ht,hclose,hfloor]
      have hh := integer_interval_mass (S.image (fun z => ⌊slope z i j/rho⌋)) rho
        (128*rho/distance3 x y+rho) ((y j-x j)/(y i-x i)) hrho (by positivity) hinterval
      have hm := mul_le_mul_of_nonneg_right hh hd.le
      have he : (2*(128*rho/distance3 x y+rho)+2*rho)*distance3 x y=
          256*rho+4*rho*distance3 x y := by field_simp; ring
      rw [he] at hm
      have hb : ((S.image (fun z => ⌊slope z i j/rho⌋)).card : ℝ)*distance3 x y*rho≤272*rho := by
        have hfour := mul_le_mul_of_nonneg_left hd4 (show 0 ≤ 4*rho by positivity)
        nlinarith only [hm,hfour]
      exact (mul_le_mul_iff_of_pos_right hrho).mp hb
    have hc := original_parameter_count_from_slope_bins S rho (distance3 x y) 272 i x hrho hd.le
      (by norm_num) hx hne hcell hresx hbins
    rw [max_eq_left (by linarith only [hfar,hrho] : rho≤distance3 x y)]
    nlinarith only [hc]
  · have hbins : ∀ j : Fin 3, j≠i →
        ((S.image (fun z => ⌊slope z i j/rho⌋)).card : ℝ)*rho≤6 := by
      intro j _hji
      have hinterval : ∀ k∈S.image (fun z => ⌊slope z i j/rho⌋), |rho*(k:ℝ)-0|≤1+rho := by
        intro k hk
        obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hk
        have hfloor := floor_mesh_error rho (slope z i j) hrho
        have ht := abs_add_le (rho*(⌊slope z i j/rho⌋:ℤ)-slope z i j) (slope z i j)
        rw [sub_add_cancel] at ht
        simp only [sub_zero]
        linarith only [ht,hfloor,hs z hz j]
      have hh := integer_interval_mass (S.image (fun z => ⌊slope z i j/rho⌋)) rho
        (1+rho) 0 hrho (by positivity) hinterval
      linarith only [hh,hrho1]
    have hc := original_parameter_count_from_slope_bins S rho rho 6 i x hrho hrho.le
      (by norm_num) hx hne hcell hresx hbins
    have hmaxbound : max (distance3 x y) rho≤128*rho := max_le (le_of_lt (lt_of_not_ge hfar))
      (by linarith only [hrho])
    have hm := pow_le_pow_left₀ (le_max_of_le_right hrho.le) hmaxbound 2
    have hn := mul_le_mul_of_nonneg_left hm (Nat.cast_nonneg S.card)
    nlinarith only [hn,hc]

def tubesThroughPair (R : Finset Pair3) (rho : ℝ) (x y : Point3) : Finset Pair3 :=
  R.filter (fun z => x∈physicalTube3 z.1 z.2 (8*rho) ∧ y∈physicalTube3 z.1 z.2 (8*rho))

/-- Divided inverse-square multiplicity for the actual original family. -/
theorem original_tubes_through_pair_card (R : Finset Pair3) (rho : ℝ) (i : Fin 3)
    (x y : Point3) (hrho : 0 < rho) (hrho1 : rho≤1)
    (hx : ∀ j, |x j|≤1) (hy : ∀ j, |y j|≤1)
    (hne : ∀ z∈R, z.2 i-z.1 i≠0)
    (hmax : ∀ z∈R, ∀ j, |z.2 j-z.1 j|≤|z.2 i-z.1 i|)
    (hcell : Set.InjOn (parameterCell rho i) (↑R : Set Pair3)) :
    ((tubesThroughPair R rho x y).card : ℝ)≤1000000000/(max (distance3 x y) rho)^2 := by
  have hm : 0 < max (distance3 x y) rho := hrho.trans_le (le_max_right _ _)
  apply (le_div_iff₀ (sq_pos_of_pos hm)).mpr
  apply original_two_point_tube_count (tubesThroughPair R rho x y) rho i x y hrho hrho1 hx hy
  · intro z hz
    exact hne z (Finset.mem_filter.mp hz).1
  · intro z hz
    exact hmax z (Finset.mem_filter.mp hz).1
  · intro z hz v hv he
    exact hcell (Finset.mem_filter.mp hz).1 (Finset.mem_filter.mp hv).1 he
  · intro z hz
    exact (Finset.mem_filter.mp hz).2

end OriginalThreeDimensionalTubePairCount

end

/- OriginalThreeDimensionalPairEnergy -/
noncomputable section
open scoped BigOperators
namespace OriginalThreeDimensionalPairEnergy
open Classical OriginalThreeDimensionalBandGeometry OriginalThreeDimensionalTubeSlab

def inverseSquareKernel (rho d : ℝ) : ℝ := 1/(max d rho)^2

def dyadicRadius (rho : ℝ) (n : ℕ) : ℝ := (2:ℝ)^n*rho

lemma dyadic_radius_pos (rho : ℝ) (n : ℕ) (hrho : 0 < rho) : 0 < dyadicRadius rho n := by
  unfold dyadicRadius
  positivity

lemma dyadic_radius_successor (rho : ℝ) (n : ℕ) :
    dyadicRadius rho (n+1)=2*dyadicRadius rho n := by
  unfold dyadicRadius
  rw [pow_succ]
  ring

lemma exists_original_dyadic_terminal (rho : ℝ) (hrho : 0 < rho) :
    ∃ N : ℕ, 4≤dyadicRadius rho N := by
  obtain ⟨N,hN⟩ := pow_unbounded_of_one_lt (4/rho) (by norm_num : (1:ℝ)<2)
  exact ⟨N,(div_le_iff₀ hrho).mp hN.le⟩

lemma inverse_square_kernel_nonneg (rho d : ℝ) : 0 ≤ inverseSquareKernel rho d := by
  unfold inverseSquareKernel
  positivity

lemma inverse_square_kernel_le_mesh (rho d : ℝ) (hrho : 0 < rho) :
    inverseSquareKernel rho d≤1/rho^2 := by
  unfold inverseSquareKernel
  exact one_div_le_one_div_of_le (sq_pos_of_pos hrho)
    (pow_le_pow_left₀ hrho.le (le_max_right _ _) 2)

lemma inverse_square_kernel_step (rho d : ℝ) (hrho : 0 < rho) :
    inverseSquareKernel rho d≤(if d≤2*rho then 1/rho^2 else 0)+inverseSquareKernel (2*rho) d := by
  by_cases hd : d≤2*rho
  · rw [if_pos hd]
    exact (inverse_square_kernel_le_mesh rho d hrho).trans
      (le_add_of_nonneg_right (inverse_square_kernel_nonneg (2*rho) d))
  · rw [if_neg hd,zero_add]
    have hlarge : 2*rho≤d := le_of_lt (lt_of_not_ge hd)
    have hr : rho≤d := by linarith only [hlarge,hrho]
    simp only [inverseSquareKernel,max_eq_left hr,max_eq_left hlarge,le_refl]

lemma inverse_square_dyadic_majorant (rho d : ℝ) (N : ℕ) (hrho : 0 < rho) :
    inverseSquareKernel rho d≤
      (∑ n∈Finset.range N, if d≤dyadicRadius rho (n+1) then 1/(dyadicRadius rho n)^2 else 0)+
        1/(dyadicRadius rho N)^2 := by
  have hstrong : inverseSquareKernel rho d≤
      (∑ n∈Finset.range N, if d≤dyadicRadius rho (n+1) then 1/(dyadicRadius rho n)^2 else 0)+
        inverseSquareKernel (dyadicRadius rho N) d := by
    induction N with
    | zero => simp [dyadicRadius]
    | succ N ih =>
      rw [Finset.sum_range_succ]
      have hh := inverse_square_kernel_step (dyadicRadius rho N) d (dyadic_radius_pos rho N hrho)
      simp only [← dyadic_radius_successor] at hh
      linarith only [ih,hh]
  exact hstrong.trans (add_le_add le_rfl (inverse_square_kernel_le_mesh (dyadicRadius rho N) d
    (dyadic_radius_pos rho N hrho)))

/-- Finite dyadic truncation of the genuine original Euclidean inverse-square
energy. Above the unit scale the proof uses only total mass. -/
theorem original_point_inverse_square_energy (P : Finset Point3) (x : Point3)
    (delta rho K : ℝ) (N : ℕ) (hd : 0 < delta) (hquery : delta≤rho) (hK : 1≤K)
    (hlastlarge : 1≤2*dyadicRadius rho N) (hx : x∈P)
    (hfrostman : ∀ p∈P, ∀ R : ℝ, delta≤R → R≤1 →
      ((P.filter (fun q => distance3 p q≤R)).card : ℝ)≤K*R^2*P.card) :
    (∑ y∈P, inverseSquareKernel rho (distance3 x y))≤4*((N:ℝ)+1)*K*P.card := by
  have hrho : 0 < rho := hd.trans_le hquery
  have hbase (n : ℕ) : rho≤dyadicRadius rho n := by
    have hp : (1:ℝ)≤(2:ℝ)^n := one_le_pow₀ (by norm_num)
    simpa only [dyadicRadius,one_mul] using mul_le_mul_of_nonneg_right hp hrho.le
  have htail (n : ℕ) (hn : 1≤2*dyadicRadius rho n) :
      (P.card : ℝ)/(dyadicRadius rho n)^2≤4*K*P.card := by
    have hnp := dyadic_radius_pos rho n hrho
    apply (div_le_iff₀ (sq_pos_of_pos hnp)).mpr
    have hs : 1≤4*(dyadicRadius rho n)^2 := by nlinarith only [hn,hnp]
    have hm := mul_le_mul_of_nonneg_right hK (show 0 ≤ 4*(dyadicRadius rho n)^2 by positivity)
    simp only [one_mul] at hm
    have hh := mul_le_mul_of_nonneg_right (hs.trans hm) (Nat.cast_nonneg P.card)
    nlinarith only [hh]
  have hterm (n : ℕ) (_hn : n∈Finset.range N) :
      (∑ y∈P, if distance3 x y≤dyadicRadius rho (n+1) then 1/(dyadicRadius rho n)^2 else 0)≤4*K*P.card := by
    have hnp : 0 < dyadicRadius rho n := dyadic_radius_pos rho n hrho
    have he : (∑ y∈P, if distance3 x y≤dyadicRadius rho (n+1) then 1/(dyadicRadius rho n)^2 else 0)=
        ((P.filter (fun y => distance3 x y≤dyadicRadius rho (n+1))).card : ℝ)/(dyadicRadius rho n)^2 := by
      rw [← Finset.sum_filter]
      simp [div_eq_mul_inv]
    rw [he]
    by_cases hsmall : dyadicRadius rho (n+1)≤1
    · have hball := hfrostman x hx (dyadicRadius rho (n+1)) (hquery.trans (hbase (n+1))) hsmall
      apply (div_le_iff₀ (sq_pos_of_pos hnp)).mpr
      rw [dyadic_radius_successor] at hball ⊢
      nlinarith only [hball]
    · have hcard : ((P.filter (fun y => distance3 x y≤dyadicRadius rho (n+1))).card : ℝ)≤P.card :=
        Nat.cast_le.mpr (Finset.card_le_card (Finset.filter_subset _ _))
      apply (div_le_div_of_nonneg_right hcard (sq_nonneg _)).trans
      apply htail n
      rw [← dyadic_radius_successor]
      exact le_of_lt (lt_of_not_ge hsmall)
  calc
    _ ≤ ∑ y∈P, ((∑ n∈Finset.range N, if distance3 x y≤dyadicRadius rho (n+1)
          then 1/(dyadicRadius rho n)^2 else 0)+1/(dyadicRadius rho N)^2) := by
      exact Finset.sum_le_sum (fun y _hy => inverse_square_dyadic_majorant rho (distance3 x y) N hrho)
    _ = (∑ n∈Finset.range N, ∑ y∈P, if distance3 x y≤dyadicRadius rho (n+1)
          then 1/(dyadicRadius rho n)^2 else 0)+(P.card : ℝ)/(dyadicRadius rho N)^2 := by
      rw [Finset.sum_add_distrib,Finset.sum_comm]
      simp [div_eq_mul_inv]
    _ ≤ (N:ℝ)*(4*K*P.card)+4*K*P.card := by
      apply add_le_add _ (htail N hlastlarge)
      calc
        _ ≤ ∑ _n∈Finset.range N, 4*K*P.card := Finset.sum_le_sum hterm
        _ = _ := by simp
    _ = _ := by ring

/-- Genuine original ordered-pair energy, including the diagonal at cutoff
rho. This uses only finite Euclidean 2-Frostman ball counts. -/
theorem original_pair_inverse_square_energy (P : Finset Point3)
    (delta eta rho : ℝ) (N : ℕ) (hd : 0 < delta) (hd1 : delta≤1) (heta : 0 ≤ eta)
    (hquery : delta≤rho) (hlastlarge : 1≤2*dyadicRadius rho N)
    (hfrostman : ∀ p∈P, ∀ R : ℝ, delta≤R → R≤1 →
      ((P.filter (fun q => distance3 p q≤R)).card : ℝ)≤delta^(-eta)*R^2*P.card) :
    (∑ x∈P, ∑ y∈P, inverseSquareKernel rho (distance3 x y))≤
      4*((N:ℝ)+1)*delta^(-eta)*(P.card : ℝ)^2 := by
  have hK : 1≤delta^(-eta) := by
    simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_ge hd hd1
      (show -eta≤0 by linarith only [heta])
  calc
    _ ≤ ∑ _x∈P, 4*((N:ℝ)+1)*delta^(-eta)*P.card := by
      apply Finset.sum_le_sum
      intro x hx
      exact original_point_inverse_square_energy P x delta rho (delta^(-eta)) N hd hquery hK
        hlastlarge hx hfrostman
    _ = _ := by simp; ring

end OriginalThreeDimensionalPairEnergy

end

/- OriginalThreeDimensionalTubeFamilyEnergy -/
noncomputable section
open scoped BigOperators
namespace OriginalThreeDimensionalTubeFamilyEnergy
open Classical OriginalThreeDimensionalBandGeometry OriginalThreeDimensionalHeavySlabs
open OriginalThreeDimensionalTubeSlab OriginalThreeDimensionalTubeParameters
open OriginalThreeDimensionalTubePairCount OriginalThreeDimensionalPairEnergy

/-- Exact ordered incidence-pair swap for the actual physical tubes. -/
lemma original_tube_square_sum_swap (P : Finset Point3) (R : Finset Pair3) (rho : ℝ) :
    (∑ z∈R, ((physicalPairTube3 P (8*rho) z).card : ℝ)^2)=
      ∑ x∈P, ∑ y∈P, ((tubesThroughPair R rho x y).card : ℝ) := by
  have hcard (z : Pair3) : ((physicalPairTube3 P (8*rho) z).card : ℝ)=
      ∑ x∈P, if x∈physicalTube3 z.1 z.2 (8*rho) then (1:ℝ) else 0 := by
    rw [← Finset.sum_filter]
    simp [physicalPairTube3]
  have hsquare (z : Pair3) : ((physicalPairTube3 P (8*rho) z).card : ℝ)^2=
      ∑ x∈P, ∑ y∈P, if x∈physicalTube3 z.1 z.2 (8*rho) ∧ y∈physicalTube3 z.1 z.2 (8*rho)
        then (1:ℝ) else 0 := by
    rw [hcard,pow_two,Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro x _hx
    apply Finset.sum_congr rfl
    intro y _hy
    by_cases hx : x∈physicalTube3 z.1 z.2 (8*rho) <;>
      by_cases hy : y∈physicalTube3 z.1 z.2 (8*rho) <;> simp [hx,hy]
  calc
    _ = ∑ z∈R, ∑ x∈P, ∑ y∈P, if x∈physicalTube3 z.1 z.2 (8*rho) ∧
          y∈physicalTube3 z.1 z.2 (8*rho) then (1:ℝ) else 0 := Finset.sum_congr rfl (fun z _hz => hsquare z)
    _ = ∑ x∈P, ∑ y∈P, ∑ z∈R, if x∈physicalTube3 z.1 z.2 (8*rho) ∧
          y∈physicalTube3 z.1 z.2 (8*rho) then (1:ℝ) else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _hx
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro x _hx
      apply Finset.sum_congr rfl
      intro y _hy
      rw [← Finset.sum_filter]
      simp [tubesThroughPair]

/-- Original physical tube square counts are controlled by the genuine
original truncated inverse-square energy. -/
theorem original_tube_family_square_energy (P : Finset Point3) (R : Finset Pair3)
    (delta eta rho : ℝ) (N : ℕ) (i : Fin 3)
    (hd : 0 < delta) (hd1 : delta≤1) (heta : 0 ≤ eta) (hquery : delta≤rho) (hrho1 : rho≤1)
    (hlastlarge : 1≤2*dyadicRadius rho N)
    (hbox : ∀ x∈P, ∀ j, |x j|≤1)
    (hne : ∀ z∈R, z.2 i-z.1 i≠0)
    (hmax : ∀ z∈R, ∀ j, |z.2 j-z.1 j|≤|z.2 i-z.1 i|)
    (hcell : Set.InjOn (parameterCell rho i) (↑R : Set Pair3))
    (hfrostman : ∀ p∈P, ∀ r : ℝ, delta≤r → r≤1 →
      ((P.filter (fun q => distance3 p q≤r)).card : ℝ)≤delta^(-eta)*r^2*P.card) :
    (∑ z∈R, ((physicalPairTube3 P (8*rho) z).card : ℝ)^2)≤
      4000000000*((N:ℝ)+1)*delta^(-eta)*(P.card : ℝ)^2 := by
  have hrho := hd.trans_le hquery
  rw [original_tube_square_sum_swap]
  calc
    _ ≤ ∑ x∈P, ∑ y∈P, 1000000000*inverseSquareKernel rho (distance3 x y) := by
      apply Finset.sum_le_sum
      intro x hx
      apply Finset.sum_le_sum
      intro y hy
      have hh := original_tubes_through_pair_card R rho i x y hrho hrho1 (hbox x hx) (hbox y hy)
        hne hmax hcell
      simpa only [inverseSquareKernel,mul_one_div] using hh
    _ = 1000000000*(∑ x∈P, ∑ y∈P, inverseSquareKernel rho (distance3 x y)) := by
      simp only [Finset.mul_sum]
    _ ≤ 1000000000*(4*((N:ℝ)+1)*delta^(-eta)*(P.card : ℝ)^2) :=
      mul_le_mul_of_nonneg_left (original_pair_inverse_square_energy P delta eta rho N hd hd1 heta
        hquery hlastlarge hfrostman) (by norm_num)
    _ = _ := by ring

/-- The actual rich representative family obeys the corresponding sharp
inverse-square family bound, with the finite dyadic loss explicit. -/
theorem original_rich_tube_family_card (P : Finset Point3) (R : Finset Pair3)
    (delta eta rho m : ℝ) (N : ℕ) (i : Fin 3)
    (hd : 0 < delta) (hd1 : delta≤1) (heta : 0 ≤ eta) (hquery : delta≤rho) (hrho1 : rho≤1)
    (hm : 0 < m) (hlastlarge : 1≤2*dyadicRadius rho N)
    (hbox : ∀ x∈P, ∀ j, |x j|≤1)
    (hne : ∀ z∈R, z.2 i-z.1 i≠0)
    (hmax : ∀ z∈R, ∀ j, |z.2 j-z.1 j|≤|z.2 i-z.1 i|)
    (hcell : Set.InjOn (parameterCell rho i) (↑R : Set Pair3))
    (hfrostman : ∀ p∈P, ∀ r : ℝ, delta≤r → r≤1 →
      ((P.filter (fun q => distance3 p q≤r)).card : ℝ)≤delta^(-eta)*r^2*P.card)
    (hrich : ∀ z∈R, m≤((physicalPairTube3 P (8*rho) z).card : ℝ)) :
    (R.card : ℝ)≤4000000000*((N:ℝ)+1)*delta^(-eta)*(P.card : ℝ)^2/m^2 := by
  apply (le_div_iff₀ (sq_pos_of_pos hm)).mpr
  have hlower : (R.card : ℝ)*m^2≤∑ z∈R, ((physicalPairTube3 P (8*rho) z).card : ℝ)^2 := by
    calc
      _ = ∑ _z∈R, m^2 := by simp
      _ ≤ _ := Finset.sum_le_sum (fun z hz => pow_le_pow_left₀ hm.le (hrich z hz) 2)
  exact hlower.trans (original_tube_family_square_energy P R delta eta rho N i hd hd1 heta hquery
    hrho1 hlastlarge hbox hne hmax hcell hfrostman)

end OriginalThreeDimensionalTubeFamilyEnergy

end

