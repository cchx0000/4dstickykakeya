import Theorems.Thm_StickyKakeya4_original_three_dimensional_cross_geometry
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3200000

noncomputable section
open scoped Matrix BigOperators
namespace OriginalThreeDimensionalSlabOverlap
open Classical Matrix OriginalThreeDimensionalBandGeometry OriginalThreeDimensionalTubeSlab
open OriginalThreeDimensionalCrossGeometry

def minor3 (a b : Point3) (i j : Fin 3) : ℝ := a i*b j-a j*b i

private theorem unit_component (n : Point3) (hn : normSq3 n=1) (i : Fin 3) : |n i|≤1 := by
  rw [norm_sq_coordinates] at hn
  have hi : (n i)^2≤1 := by
    fin_cases i <;> simp only [Fin.reduceFinMk] <;>
      nlinarith only [hn,sq_nonneg (n 0),sq_nonneg (n 1),sq_nonneg (n 2)]
  nlinarith only [hi,sq_abs (n i),abs_nonneg (n i)]

private theorem minor_bound_of_cross (a b : Point3) (B : ℝ) (hB : 0≤B)
    (hcross : ∀ i, |(a ⨯₃ b) i|≤B) : ∀ i j, |minor3 a b i j|≤B := by
  have h01 : |a 0*b 1-a 1*b 0|≤B := hcross 2
  have h12 : |a 1*b 2-a 2*b 1|≤B := hcross 0
  have h20 : |a 2*b 0-a 0*b 2|≤B := hcross 1
  intro i j
  fin_cases i <;> fin_cases j <;> simp only [minor3,Fin.reduceFinMk,sub_self,abs_zero]
  all_goals first | exact hB | exact h01 | exact h12 | exact h20 |
    simpa only [abs_sub_comm] using h01 | simpa only [abs_sub_comm] using h12 |
    simpa only [abs_sub_comm] using h20

private theorem slab_dot_difference (n p q : Point3) (c D : ℝ)
    (hp : |n ⬝ᵥ p-c|≤D) (hq : |n ⬝ᵥ q-c|≤D) : |n ⬝ᵥ (q-p)|≤2*D := by
  rw [dotProduct_sub]
  have hh := abs_sub (n ⬝ᵥ q-c) (n ⬝ᵥ p-c)
  have he : (n ⬝ᵥ q-c)-(n ⬝ᵥ p-c)=n ⬝ᵥ q-n ⬝ᵥ p := by ring
  rw [he] at hh
  linarith only [hp,hq,hh]

/-- Two actual small normal residuals control every cross-normal minor.
This is the coordinate form of the two original slab equations. -/
theorem original_cross_normal_minor_bound (n m v : Point3) (D : ℝ)
    (hD : 0≤D) (hn : normSq3 n=1) (hm : normSq3 m=1)
    (hnv : |n ⬝ᵥ v|≤2*D) (hmv : |m ⬝ᵥ v|≤2*D) :
    ∀ i j, |minor3 (n ⨯₃ m) v i j|≤4*D := by
  apply minor_bound_of_cross (n ⨯₃ m) v (4*D) (by positivity)
  intro i
  rw [cross_cross_eq_smul_sub_smul]
  simp only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
  have hh := abs_sub ((n ⬝ᵥ v)*m i) ((m ⬝ᵥ v)*n i)
  rw [abs_mul,abs_mul] at hh
  have h1 := mul_le_mul hnv (unit_component m hm i) (abs_nonneg _) (by positivity : 0≤2*D)
  have h2 := mul_le_mul hmv (unit_component n hn i) (abs_nonneg _) (by positivity : 0≤2*D)
  linarith only [hh,h1,h2]

/-- Literal Cramer identity with bounded original displacement coordinates.
No plane intersection, projection or tube-overlap hypothesis is supplied. -/
theorem original_cramer_cross_bound (c v w : Point3) (D : ℝ) (l : Fin 3)
    (hD : 0≤D) (hv : ∀ i, |v i|≤2) (hw : ∀ i, |w i|≤2)
    (hcv : ∀ i j, |minor3 c v i j|≤4*D)
    (hcw : ∀ i j, |minor3 c w i j|≤4*D) :
    ∀ i j, |c l| * |minor3 v w i j|≤24*D := by
  intro i j
  have hid : c l*minor3 v w i j=
      minor3 c v l i*w j-minor3 c v l j*w i+v l*minor3 c w i j := by
    dsimp [minor3]
    ring
  have h1 := mul_le_mul (hcv l i) (hw j) (abs_nonneg _) (by positivity : 0≤4*D)
  have h2 := mul_le_mul (hcv l j) (hw i) (abs_nonneg _) (by positivity : 0≤4*D)
  have h3 := mul_le_mul (hv l) (hcw i j) (abs_nonneg _) (by norm_num : (0:ℝ)≤2)
  have ht1 := abs_sub (minor3 c v l i*w j) (minor3 c v l j*w i)
  have ht2 := abs_add_le (minor3 c v l i*w j-minor3 c v l j*w i) (v l*minor3 c w i j)
  rw [← hid,abs_mul,abs_mul] at ht2
  rw [abs_mul,abs_mul] at ht1
  linarith only [h1,h2,h3,ht1,ht2]

/-- If two genuinely separated unit-normal slabs contain the original
p,q and x, then x has a derived Euclidean tube witness on the original
pair line. The explicit bound is 144D/(r g). -/
theorem original_two_slabs_force_pair_tube
    (p q x n m : Point3) (cn cm D r g : ℝ)
    (hD : 0≤D) (hr : 0<r) (hg : 0<g)
    (hn : normSq3 n=1) (hm : normSq3 m=1)
    (hp : ∀ i, |p i|≤1) (hq : ∀ i, |q i|≤1) (hx : ∀ i, |x i|≤1)
    (hsep : r≤distance3 p q)
    (hminus : g≤distance3 n m) (hplus : g≤distance3 n (-m))
    (hnp : |n ⬝ᵥ p-cn|≤D) (hnq : |n ⬝ᵥ q-cn|≤D) (hnx : |n ⬝ᵥ x-cn|≤D)
    (hmp : |m ⬝ᵥ p-cm|≤D) (hmq : |m ⬝ᵥ q-cm|≤D) (hmx : |m ⬝ᵥ x-cm|≤D) :
    x∈physicalTube3 p q (144*D/(r*g)) := by
  let v := q-p
  let w := x-p
  let c := n ⨯₃ m
  obtain ⟨l,_hmax,hgap⟩ := original_projective_gap_cross_coordinate n m g hn hm hg hminus hplus
  have hc : 0< |c l| := by dsimp [c]; nlinarith only [hgap,hg]
  have hcv := original_cross_normal_minor_bound n m v D hD hn hm
    (slab_dot_difference n p q cn D hnp hnq) (slab_dot_difference m p q cm D hmp hmq)
  have hcw := original_cross_normal_minor_bound n m w D hD hn hm
    (slab_dot_difference n p x cn D hnp hnx) (slab_dot_difference m p x cm D hmp hmx)
  have hv (i : Fin 3) : |v i|≤2 := by
    have hh := abs_sub (q i) (p i)
    dsimp [v]
    linarith only [hh,hq i,hp i]
  have hw (i : Fin 3) : |w i|≤2 := by
    have hh := abs_sub (x i) (p i)
    dsimp [w]
    linarith only [hh,hx i,hp i]
  have hcramer := original_cramer_cross_bound c v w D l hD hv hw hcv hcw
  have hminor (i j : Fin 3) : |minor3 v w i j|≤24*D/|c l| := by
    apply (le_div_iff₀ hc).mpr
    nlinarith only [hcramer i j]
  have hcross : ∀ i, |(v ⨯₃ w) i|≤24*D/|c l| := by
    intro i
    fin_cases i
    · exact hminor 1 2
    · exact hminor 2 0
    · exact hminor 0 1
  obtain ⟨a,ha⟩ := original_cross_bound_physical_tube p q x r (24*D/|c l|)
    hr (by positivity) hsep hcross
  refine ⟨a,ha.trans ?_⟩
  have hwidth : 2*(24*D/|c l|)/r≤144*D/(r*g) := by
    apply (le_div_iff₀ (mul_pos hr hg)).mpr
    have he : (2*(24*D/|c l|)/r)*(r*g)=48*D*g/|c l| := by field_simp; ring
    rw [he]
    apply (div_le_iff₀ hc).mpr
    have hh := mul_le_mul_of_nonneg_left hgap (show 0≤48*D by positivity)
    dsimp [c]
    nlinarith only [hh]
  exact hwidth

/-- Original off-axis points cannot lie in both slabs once the actual
unoriented normal distance reaches the displayed threshold. -/
theorem original_shared_slab_point_forces_close_normals
    (p q x n m : Point3) (cn cm D r tau : ℝ)
    (hD : 0<D) (hr : 0<r) (htau : 0<tau)
    (hn : normSq3 n=1) (hm : normSq3 m=1)
    (hp : ∀ i, |p i|≤1) (hq : ∀ i, |q i|≤1) (hx : ∀ i, |x i|≤1)
    (hsep : r≤distance3 p q)
    (hnp : |n ⬝ᵥ p-cn|≤D) (hnq : |n ⬝ᵥ q-cn|≤D) (hnx : |n ⬝ᵥ x-cn|≤D)
    (hmp : |m ⬝ᵥ p-cm|≤D) (hmq : |m ⬝ᵥ q-cm|≤D) (hmx : |m ⬝ᵥ x-cm|≤D)
    (hout : x∉physicalTube3 p q tau) :
    min (distance3 n m) (distance3 n (-m))<144*D/(r*tau) := by
  by_contra hh
  have hgap := le_min_iff.mp (le_of_not_gt hh)
  have hin := original_two_slabs_force_pair_tube p q x n m cn cm D r (144*D/(r*tau))
    hD.le hr (by positivity) hn hm hp hq hx hsep hgap.1 hgap.2 hnp hnq hnx hmp hmq hmx
  have he : 144*D/(r*(144*D/(r*tau)))=tau := by field_simp
  rw [he] at hin
  exact hout hin

end OriginalThreeDimensionalSlabOverlap
