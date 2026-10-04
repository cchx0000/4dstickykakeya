import Theorems.Thm_StickyKakeya4_original_three_dimensional_tube_slab
import Mathlib.LinearAlgebra.CrossProduct

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3200000

noncomputable section
open scoped Matrix BigOperators
namespace OriginalThreeDimensionalCrossGeometry
open Classical Matrix OriginalThreeDimensionalBandGeometry OriginalThreeDimensionalTubeSlab

def normSq3 (v : Point3) : ℝ := v ⬝ᵥ v

lemma norm_sq_coordinates (v : Point3) : normSq3 v=(v 0)^2+(v 1)^2+(v 2)^2 := by
  simp [normSq3,dotProduct,Fin.sum_univ_three,pow_two]

lemma norm_sq_nonneg (v : Point3) : 0≤normSq3 v := by rw [norm_sq_coordinates]; positivity

lemma distance_squared_dot (p q : Point3) :
    (distance3 p q)^2=normSq3 p+normSq3 q-2*(p ⬝ᵥ q) := by
  rw [distance3,Real.sq_sqrt (by positivity)]
  simp only [norm_sq_coordinates,dotProduct,Fin.sum_univ_three]
  ring

lemma distance_squared_difference (p q : Point3) :
    (distance3 p q)^2=normSq3 (p-q) := by
  rw [distance3,Real.sq_sqrt (by positivity),norm_sq_coordinates]
  rfl

/-- A positive actual unoriented Euclidean normal gap forces a large
literal cross-product coordinate. -/
theorem original_projective_gap_cross_coordinate (n m : Point3) (g : ℝ)
    (hn : normSq3 n=1) (hm : normSq3 m=1) (hg : 0<g)
    (hminus : g≤distance3 n m) (hplus : g≤distance3 n (-m)) :
    ∃ l : Fin 3, (∀ i, |(n ⨯₃ m) i|≤|(n ⨯₃ m) l|) ∧ g≤3*|(n ⨯₃ m) l| := by
  let t := n ⬝ᵥ m
  let c := n ⨯₃ m
  have hid : normSq3 c=1-t^2 := by
    dsimp [normSq3,c]
    rw [cross_dot_cross]
    change normSq3 n*normSq3 m-(n ⬝ᵥ m)*(m ⬝ᵥ n)=_
    rw [hn,hm,dotProduct_comm m n]
    dsimp [t]
    ring
  have ht1 : t≤1 := by nlinarith only [hid,norm_sq_nonneg c]
  have htm1 : -1≤t := by nlinarith only [hid,norm_sq_nonneg c]
  have hmi := pow_le_pow_left₀ hg.le hminus 2
  have hpl := pow_le_pow_left₀ hg.le hplus 2
  rw [distance_squared_dot,hn,hm] at hmi
  have hmneg : normSq3 (-m)=1 := by
    simpa only [normSq3,neg_dotProduct,dotProduct_neg,neg_neg] using hm
  rw [distance_squared_dot,hn,hmneg,dotProduct_neg] at hpl
  change g^2≤1+1-2*t at hmi
  change g^2≤1+1-2*(-t) at hpl
  have hgs : g^2≤2*normSq3 c := by
    by_cases ht : 0≤t
    · have hh := mul_nonneg ht (sub_nonneg.mpr ht1)
      nlinarith only [hmi,hid,hh]
    · have hh := mul_nonneg (show 0≤-t by linarith only [ht]) (show 0≤1+t by linarith only [htm1])
      nlinarith only [hpl,hid,hh]
  obtain ⟨l,_hl,hmax⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin 3))
    (fun i => |c i|) Finset.univ_nonempty
  have hmax' (i : Fin 3) := hmax i (Finset.mem_univ i)
  have hs (i : Fin 3) : (c i)^2≤(c l)^2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (c i)) (hmax' i) 2
  have hsum : normSq3 c≤3*(c l)^2 := by
    rw [norm_sq_coordinates]
    linarith only [hs 0,hs 1,hs 2]
  refine ⟨l,hmax',?_⟩
  change g≤3*|c l|
  nlinarith only [hgs,hsum,sq_abs (c l),abs_nonneg (c l),hg.le]

private theorem orthogonal_residual_identity (v w : Point3) (hv : normSq3 v≠0) :
    normSq3 (w-((v ⬝ᵥ w)/normSq3 v) • v)*normSq3 v=normSq3 (v ⨯₃ w) := by
  simp only [normSq3,sub_dotProduct,dotProduct_sub,smul_dotProduct,dotProduct_smul,smul_eq_mul]
  rw [cross_dot_cross,dotProduct_comm w v]
  change v ⬝ᵥ v≠0 at hv
  field_simp
  ring

/-- A bound on the actual cross product gives a genuine Euclidean tube
witness on the original pair line. The witness is the explicit orthogonal
affine parameter; no point-to-line certificate is assumed. -/
theorem original_cross_bound_physical_tube (p q x : Point3) (r B : ℝ)
    (hr : 0<r) (hB : 0≤B) (hsep : r≤distance3 p q)
    (hcross : ∀ i, |((q-p) ⨯₃ (x-p)) i|≤B) :
    x∈physicalTube3 p q (2*B/r) := by
  let v := q-p
  let w := x-p
  let L := normSq3 v
  have hrL : r^2≤L := by
    have hh := pow_le_pow_left₀ hr.le hsep 2
    rw [distance_squared_difference] at hh
    have he : normSq3 (p-q)=normSq3 v := by
      rw [norm_sq_coordinates,norm_sq_coordinates]
      simp only [v,Pi.sub_apply]
      rw [sub_sq_comm (p 0) (q 0),sub_sq_comm (p 1) (q 1),sub_sq_comm (p 2) (q 2)]
    exact hh.trans_eq he
  have hL : 0<L := (sq_pos_of_pos hr).trans_le hrL
  let a := (v ⬝ᵥ w)/L
  have hres : x-linePoint3 p q a=w-a • v := by
    funext i
    simp only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul,linePoint3,v,w]
    ring
  have hid : (distance3 x (linePoint3 p q a))^2*L=normSq3 (v ⨯₃ w) := by
    rw [distance_squared_difference,hres]
    exact orthogonal_residual_identity v w hL.ne'
  have hs (i : Fin 3) : ((v ⨯₃ w) i)^2≤B^2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (((q-p) ⨯₃ (x-p)) i)) (hcross i) 2
  have hcrossSq : normSq3 (v ⨯₃ w)≤3*B^2 := by
    rw [norm_sq_coordinates]
    linarith only [hs 0,hs 1,hs 2]
  have hprod := mul_le_mul_of_nonneg_left hrL (sq_nonneg (distance3 x (linePoint3 p q a)))
  have hdist : distance3 x (linePoint3 p q a)*r≤2*B := by
    apply le_of_sq_le_sq _ (by positivity : 0≤2*B)
    nlinarith only [hprod,hid,hcrossSq,sq_nonneg B]
  exact ⟨a,(le_div_iff₀ hr).mpr hdist⟩

end OriginalThreeDimensionalCrossGeometry
