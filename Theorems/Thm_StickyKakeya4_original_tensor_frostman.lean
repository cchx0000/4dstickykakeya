import Theorems.Thm_StickyKakeya4_gkz_original_gap_energy
import Mathlib.Data.Fintype.BigOperators

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000
noncomputable section
open Classical
open scoped BigOperators

namespace OriginalTensorFrostman
open GKZOriginalGapEnergy

def tensor (A : Finset ℝ) (n : ℕ) : Finset (Fin n → ℝ) :=
  Fintype.piFinset (fun _ => A)

lemma tensor_card (A : Finset ℝ) (n : ℕ) : (tensor A n).card=A.card^n := by
  exact Fintype.card_piFinset_const A n

/-- A sup-norm ball in the ORIGINAL tensor carrier is the literal product
of its original one-dimensional windows. -/
lemma original_tensor_window (A : Finset ℝ) (n : ℕ) (c : Fin n → ℝ) (r : ℝ) :
    (tensor A n).filter (fun a => ∀ i, |a i-c i| ≤ r)=
      Fintype.piFinset (fun i => A.filter (fun x => |x-c i| ≤ r)) := by
  ext a
  simp only [Finset.mem_filter,tensor,Fintype.mem_piFinset]
  constructor
  · rintro ⟨hA,hnear⟩ i
    exact ⟨hA i,hnear i⟩
  · intro h
    exact ⟨fun i => (h i).1,fun i => (h i).2⟩

/-- Weak original scalar Frostman estimates multiply under the actual tensor
construction, with no cardinality-exponent matching requirement. -/
theorem original_tensor_frostman (A : Finset ℝ) (n : ℕ)
    {delta K u : ℝ} (hprofile : ScalarFrostman A delta K u)
    (c : Fin n → ℝ) (r : ℝ) (hr : delta ≤ r) (hr1 : r ≤ 1) :
    (((tensor A n).filter (fun a => ∀ i, |a i-c i| ≤ r)).card:ℝ) ≤
      (K*r^u)^n*(tensor A n).card := by
  rw [original_tensor_window,Fintype.card_piFinset,Nat.cast_prod]
  have hc : (∏ i : Fin n, ((A.filter (fun x => |x-c i| ≤ r)).card:ℝ)) ≤
      ∏ _i : Fin n, K*r^u*(A.card:ℝ) := by
    apply Finset.prod_le_prod
    · intro i _hi
      exact Nat.cast_nonneg _
    · intro i _hi
      exact hprofile (c i) r hr hr1
  have he : (∏ _i : Fin n, K*r^u*(A.card:ℝ))=
      (K*r^u)^n*(tensor A n).card := by
    simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin,mul_pow,tensor_card,Nat.cast_pow]
  exact hc.trans_eq he

end OriginalTensorFrostman
