import Theorems.Thm_StickyKakeya4_native_finite_point_coherence

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2500000

noncomputable section
namespace NativeFixedCoherenceCost
open Classical Finset
open scoped BigOperators

lemma actual_cap_one_le {A X C B : Type*} [DecidableEq X] [DecidableEq C] [DecidableEq B]
    (S : Finset A) (hS : S.Nonempty) (point : A → X) (cell : X → C) (offset : X → B)
    (cost : ℝ) (H : ∀c,(((S.filter (fun z => cell (point z)=c)).image
      (fun z => offset (point z))).card:ℝ) ≤ cost) : 1 ≤ cost := by
  obtain ⟨z,hz⟩ := hS
  have hc : 1 ≤ ((S.filter (fun u => cell (point u)=cell (point z))).image
      (fun u => offset (point u))).card := card_pos.mpr
        ⟨offset (point z),mem_image.mpr ⟨z,mem_filter.mpr ⟨hz,rfl⟩,rfl⟩⟩
  exact (show (1:ℝ) ≤ ((S.filter (fun u => cell (point u)=cell (point z))).image
    (fun u => offset (point u))).card by exact_mod_cast hc).trans (H _)

theorem ceiling_product_bound (K : ℕ) (cost : Fin K → ℝ) (hcost : ∀j,1 ≤ cost j) :
    ((∏j,⌈cost j⌉₊:ℕ):ℝ) ≤ (2:ℝ)^K*∏j,cost j := by
  have hceil (j : Fin K) : (⌈cost j⌉₊:ℝ) ≤ 2*cost j := by
    have hh := Nat.ceil_lt_add_one (show 0 ≤ cost j by linarith only [hcost j])
    linarith only [hh,hcost j]
  rw [Nat.cast_prod]
  calc
    _ ≤ ∏j : Fin K,2*cost j := prod_le_prod (fun _ _ => Nat.cast_nonneg _) (fun j _ => hceil j)
    _ = _ := by rw [prod_mul_distrib]; simp

/-- With K fixed first, K rounds cost only K times the proved per-round
exponent. All fixed factors remain explicit for the later source cutoff. -/
theorem fixed_round_power_cost {rho A loss : ℝ} (K : ℕ) (cost : Fin K → ℝ)
    (hrho : 0 < rho) (hcost : ∀j,1 ≤ cost j)
    (H : ∀j,cost j ≤ A*rho^(-loss)) :
    ((∏j,⌈cost j⌉₊:ℕ):ℝ) ≤ (2*A)^K*rho^(-((K:ℝ)*loss)) := by
  have hprod : (∏j : Fin K,cost j) ≤ (A*rho^(-loss))^K := by
    calc
      _ ≤ ∏_j : Fin K,A*rho^(-loss) :=
        prod_le_prod (fun j _ => (by linarith only [hcost j])) (fun j _ => H j)
      _ = _ := by simp
  calc
    _ ≤ (2:ℝ)^K*(∏j : Fin K,cost j) := ceiling_product_bound K cost hcost
    _ ≤ (2:ℝ)^K*(A*rho^(-loss))^K := mul_le_mul_of_nonneg_left hprod (by positivity)
    _ = (2*A)^K*(rho^(-loss))^K := by rw [mul_pow,mul_pow]; ring
    _ = _ := by
      rw [←Real.rpow_natCast (rho^(-loss)),←Real.rpow_mul hrho.le]
      congr 2
      ring

end NativeFixedCoherenceCost
