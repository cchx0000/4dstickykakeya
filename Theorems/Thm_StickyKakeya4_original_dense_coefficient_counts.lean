import Theorems.Thm_StickyKakeya4_original_scalar_affine_packing
import Theorems.Thm_StickyKakeya4_gkz_original_gap_energy

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2200000
noncomputable section
open scoped BigOperators
namespace OriginalDenseCoefficientCounts
open Classical OriginalSeparatedPacking OriginalScalarAffinePacking GKZOriginalGapEnergy

def scalarCollision (delta xi a b c d : ℝ) : Prop :=
  |a+xi*c-(b+xi*d)| ≤ delta

def sourcePairs (A : Finset ℝ) : Finset (ℝ × ℝ) := A.product A

def collisions (A : Finset ℝ) (delta xi : ℝ) : Finset ((ℝ × ℝ) × (ℝ × ℝ)) :=
  (sourcePairs A).product (sourcePairs A) |>.filter
    (fun z => scalarCollision delta xi z.1.1 z.2.1 z.1.2 z.2.2)

def nearCollisions (A : Finset ℝ) (delta xi tau : ℝ) : Finset ((ℝ × ℝ) × (ℝ × ℝ)) :=
  (collisions A delta xi).filter (fun z => |z.1.2-z.2.2| ≤ tau)

def farCollisions (A : Finset ℝ) (delta xi tau : ℝ) : Finset ((ℝ × ℝ) × (ℝ × ℝ)) :=
  (collisions A delta xi).filter (fun z => ¬|z.1.2-z.2.2| ≤ tau)

/-- Fixing the other three original labels leaves only a bounded number
of actual b labels, by the ORIGINAL delta separation of A. -/
theorem original_collision_b_count (A : Finset ℝ) (delta xi a c d : ℝ)
    (hd : 0 < delta)
    (hsep : ∀ x∈A,∀ y∈A,x≠y → delta ≤ |x-y|) :
    ((A.filter (fun b => scalarCollision delta xi a b c d)).card : ℝ) ≤ 4 := by
  have he (b : ℝ) : |a+xi*c-(b+xi*d)|=|b-(a+xi*(c-d))| := by
    have hh : a+xi*c-(b+xi*d)=-(b-(a+xi*(c-d))) := by ring
    rw [hh,abs_neg]
  have hset : A.filter (fun b => scalarCollision delta xi a b c d)=
      A.filter (fun b => |b-(a+xi*(c-d))| ≤ delta) := by
    ext b
    simp only [Finset.mem_filter,scalarCollision,he]
  rw [hset]
  have hh := scalar_ball_card A hd hd.le hsep (a+xi*(c-d))
  norm_num [div_self hd.ne'] at hh
  exact_mod_cast hh

/-- Far original c,d pairs have few actual separated coefficient labels.
There is no product-law or coefficient-range assumption. -/
theorem original_far_coefficient_count (Xi : Finset ℝ) (delta tau a b c d : ℝ)
    (hd : 0 < delta) (htau : 0 < tau) (htau1 : tau ≤ 1)
    (hsep : ∀ x∈Xi,∀ y∈Xi,x≠y → delta ≤ |x-y|)
    (hfar : tau ≤ |c-d|) :
    ((Xi.filter (fun xi => scalarCollision delta xi a b c d)).card : ℝ) ≤ 6/tau := by
  have he (xi : ℝ) : a+xi*c-(b+xi*d)=(c-d)*xi-(b-a) := by ring
  have hset : Xi.filter (fun xi => scalarCollision delta xi a b c d)=
      Xi.filter (fun xi => |(c-d)*xi-(b-a)| ≤ delta) := by
    ext xi
    simp only [Finset.mem_filter,scalarCollision,he]
  rw [hset]
  have hh := scalar_affine_card Xi (u:=c-d) (z:=b-a) hd hd.le htau hfar hsep
  have heq : (delta/tau)/delta=1/tau := by field_simp
  rw [heq] at hh
  apply hh.trans
  apply (le_div_iff₀ htau).mpr
  have heq2 : (2*(1/tau)+2)*tau=2+2*tau := by field_simp
  rw [heq2]
  linarith only [htau1]

lemma original_collision_near_far_partition (A : Finset ℝ) (delta xi tau : ℝ) :
    ((collisions A delta xi).card : ℝ)=
      ((nearCollisions A delta xi tau).card : ℝ)+(farCollisions A delta xi tau).card := by
  exact_mod_cast (Finset.card_filter_add_card_filter_not (s:=collisions A delta xi)
    (fun z => |z.1.2-z.2.2| ≤ tau)).symm

end OriginalDenseCoefficientCounts
