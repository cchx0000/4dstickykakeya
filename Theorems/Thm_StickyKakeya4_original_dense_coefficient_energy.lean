import Theorems.Thm_StickyKakeya4_original_dense_coefficient_counts
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3200000
noncomputable section
open scoped BigOperators
namespace OriginalDenseCoefficientEnergy
open Classical OriginalDenseCoefficientCounts GKZOriginalGapEnergy

/-- The near c,d contribution uses the original b separation, retaining
only THREE free source labels rather than four. -/
theorem original_near_collision_count (A : Finset ℝ) (delta xi tau K u : ℝ)
    (hd : 0 < delta) (hquery : delta ≤ tau) (htau1 : tau ≤ 1)
    (hsep : ∀ x∈A,∀ y∈A,x≠y → delta ≤ |x-y|)
    (hprofile : ScalarFrostman A delta K u) :
    ((nearCollisions A delta xi tau).card : ℝ) ≤ 4*K*tau^u*(A.card : ℝ)^3 := by
  have hb (a c d : ℝ) :
      (∑ b∈A,if scalarCollision delta xi a b c d ∧ |c-d| ≤ tau then (1:ℝ) else 0) ≤
        (if |c-d| ≤ tau then (4:ℝ) else 0) := by
    by_cases hcd : |c-d| ≤ tau
    · simp only [hcd,and_true,if_true]
      rw [← Finset.sum_filter]
      simpa only [Finset.sum_const,nsmul_eq_mul,mul_one] using original_collision_b_count A delta xi a c d hd hsep
    · simp only [hcd,and_false,if_false,Finset.sum_const_zero]
      exact le_rfl
  have hnear (c : ℝ) : (∑ d∈A,if |c-d| ≤ tau then (4:ℝ) else 0) ≤ 4*K*tau^u*A.card := by
    have hc := hprofile c tau hquery htau1
    have he : A.filter (fun d => |c-d| ≤ tau)=A.filter (fun d => |d-c| ≤ tau) := by
      ext d
      simp only [Finset.mem_filter,abs_sub_comm]
    rw [← Finset.sum_filter,he]
    simp only [Finset.sum_const,nsmul_eq_mul]
    nlinarith only [hc]
  have hid : ((nearCollisions A delta xi tau).card : ℝ)=
      ∑ a∈A,∑ c∈A,∑ b∈A,∑ d∈A,
        if scalarCollision delta xi a b c d ∧ |c-d| ≤ tau then (1:ℝ) else 0 := by
    simp only [nearCollisions,collisions,sourcePairs,Finset.filter_filter,Finset.card_eq_sum_ones,
      Finset.sum_filter,Finset.product_eq_sprod,Finset.sum_product,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
  rw [hid]
  calc
    _ = ∑ a∈A,∑ c∈A,∑ d∈A,∑ b∈A,
        if scalarCollision delta xi a b c d ∧ |c-d| ≤ tau then (1:ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro a _ha
      apply Finset.sum_congr rfl
      intro c _hc
      rw [Finset.sum_comm]
    _ ≤ ∑ _a∈A,∑ _c∈A,4*K*tau^u*A.card := by
      apply Finset.sum_le_sum
      intro a _ha
      apply Finset.sum_le_sum
      intro c _hc
      exact (Finset.sum_le_sum (fun d _hd => hb a c d)).trans (hnear c)
    _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]; ring

/-- The far contribution is paid by the actual finite coefficient set,
using its original delta separation rather than an independent parameter law. -/
theorem original_far_collision_energy (A Xi : Finset ℝ) (delta tau : ℝ)
    (hd : 0 < delta) (htau : 0 < tau) (htau1 : tau ≤ 1)
    (hsep : ∀ x∈Xi,∀ y∈Xi,x≠y → delta ≤ |x-y|) :
    (∑ xi∈Xi,((farCollisions A delta xi tau).card : ℝ)) ≤
      6*(A.card : ℝ)^4/tau := by
  let P := (sourcePairs A).product (sourcePairs A)
  have hswap : (∑ xi∈Xi,((farCollisions A delta xi tau).card : ℝ))=
      ∑ z∈P,∑ xi∈Xi,if scalarCollision delta xi z.1.1 z.2.1 z.1.2 z.2.2 ∧
        ¬|z.1.2-z.2.2| ≤ tau then (1:ℝ) else 0 := by
    simp only [farCollisions,collisions,Finset.filter_filter,Finset.card_eq_sum_ones,
      Finset.sum_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
    rw [Finset.sum_comm]
  have hz (z : (ℝ × ℝ) × (ℝ × ℝ)) :
      (∑ xi∈Xi,if scalarCollision delta xi z.1.1 z.2.1 z.1.2 z.2.2 ∧
        ¬|z.1.2-z.2.2| ≤ tau then (1:ℝ) else 0) ≤ 6/tau := by
    by_cases hnear : |z.1.2-z.2.2| ≤ tau
    · simp only [hnear,not_true_eq_false,and_false,if_false,Finset.sum_const_zero]
      positivity
    · simp only [hnear,not_false_eq_true,and_true]
      rw [← Finset.sum_filter]
      simpa only [Finset.sum_const,nsmul_eq_mul,mul_one] using
        original_far_coefficient_count Xi delta tau z.1.1 z.2.1 z.1.2 z.2.2
          hd htau htau1 hsep (lt_of_not_ge hnear).le
  rw [hswap]
  calc
    _ ≤ ∑ _z∈P,6/tau := Finset.sum_le_sum (fun z _ => hz z)
    _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul,P,sourcePairs,
        Finset.product_eq_sprod,Finset.card_product,Nat.cast_mul]; ring

/-- Genuine original four-variable collision energy with a near/far
split. This is the source input for a dense-coefficient projection gain. -/
theorem original_dense_coefficient_collision_energy (A Xi : Finset ℝ) (delta tau K u : ℝ)
    (hd : 0 < delta) (hquery : delta ≤ tau) (htau1 : tau ≤ 1)
    (hAsep : ∀ x∈A,∀ y∈A,x≠y → delta ≤ |x-y|)
    (hXsep : ∀ x∈Xi,∀ y∈Xi,x≠y → delta ≤ |x-y|)
    (hprofile : ScalarFrostman A delta K u) :
    (∑ xi∈Xi,((collisions A delta xi).card : ℝ)) ≤
      4*K*tau^u*(A.card : ℝ)^3*Xi.card+6*(A.card : ℝ)^4/tau := by
  have hn : (∑ xi∈Xi,((nearCollisions A delta xi tau).card : ℝ)) ≤
      4*K*tau^u*(A.card : ℝ)^3*Xi.card := by
    have hh := Finset.sum_le_sum (s:=Xi) (fun xi _ => original_near_collision_count A delta xi tau K u
      hd hquery htau1 hAsep hprofile)
    simpa only [Finset.sum_const,nsmul_eq_mul,mul_comm] using hh
  have hf := original_far_collision_energy A Xi delta tau hd (hd.trans_le hquery) htau1 hXsep
  have he : (∑ xi∈Xi,((collisions A delta xi).card : ℝ))=
      (∑ xi∈Xi,((nearCollisions A delta xi tau).card : ℝ))+
        ∑ xi∈Xi,((farCollisions A delta xi tau).card : ℝ) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun xi _ => original_collision_near_far_partition A delta xi tau)
  rw [he]
  exact add_le_add hn hf

end OriginalDenseCoefficientEnergy
