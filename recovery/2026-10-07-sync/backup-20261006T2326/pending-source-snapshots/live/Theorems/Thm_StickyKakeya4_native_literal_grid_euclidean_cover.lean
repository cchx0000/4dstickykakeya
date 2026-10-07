import Theorems.Thm_StickyKakeya4_native_literal_grid_cover_ad
import Theorems.Thm_StickyKakeya4_native_literal_euclidean_ad

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

noncomputable section
namespace NativeLiteralGridEuclideanCover
open Classical Finset FiniteVoronoiPopulation NativeLiteralGridCoverAD NativeLiteralEuclideanAD
attribute [local instance] Classical.propDecidable

/-- Original Euclidean balls, counted by their occupied half-open cubes.
The original coordinate set is retained, including coincident cube labels. -/
def euclideanCoverCount {l : ℕ} (A : Finset (Fin l → ℝ)) (rho : ℝ) (a : Fin l → ℝ) (r : ℝ) : ℝ :=
  ((A.filter (fun x => dist (WithLp.toLp 2 x) (WithLp.toLp 2 a) ≤ r)).image (label rho)).card

def EuclideanCoverAD {l : ℕ} (A : Finset (Fin l → ℝ)) (rho K s : ℝ) : Prop :=
  ∀a∈A,∀r : ℝ,rho ≤ r → r ≤ 1 →
    (r/rho)^s/K ≤ euclideanCoverCount A rho a r ∧
      euclideanCoverCount A rho a r ≤ K*(r/rho)^s

/-- Convert sup-ball occupied-cell AD to the literal Euclidean-ball
version. The near-mesh lower uses an original occupied cell, so no AD test
is invoked below its valid radius. -/
theorem euclidean_cover_of_sup_cover {l : ℕ} (A : Finset (Fin l → ℝ))
    {rho K s : ℝ} (hrho : 0 < rho) (hK : 1 ≤ K) (hs : 0 ≤ s)
    (H : CoverADBounds A rho K s) :
    EuclideanCoverAD A rho ((max 1 (l:ℝ))^s*K) s := by
  let L : ℝ := max 1 (l:ℝ)
  have hL1 : 1 ≤ L := le_max_left _ _
  have hL : 0 < L := lt_of_lt_of_le zero_lt_one hL1
  have hKp : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hLp : 0 < L^s := Real.rpow_pos_of_pos hL _
  have hLp1 : 1 ≤ L^s := Real.one_le_rpow hL1 hs
  have hKcost : K ≤ L^s*K := le_mul_of_one_le_left hKp.le hLp1
  intro a ha r hr hr1
  have hrp : 0 < r := hrho.trans_le hr
  let B := A.filter (fun x => dist (WithLp.toLp 2 x) (WithLp.toLp 2 a) ≤ r)
  change (r/rho)^s/(L^s*K) ≤ ((B.image (label rho)).card:ℝ) ∧
    ((B.image (label rho)).card:ℝ) ≤ (L^s*K)*(r/rho)^s
  constructor
  · by_cases hquery : rho ≤ r/L
    · have hsub : carrierBall A a (r/L) ⊆ B := by
        intro x hx
        obtain ⟨hxA,hxd⟩ := mem_filter.mp hx
        apply mem_filter.mpr
        refine ⟨hxA,?_⟩
        calc
          _ ≤ L*dist x a := toLp_dist_le x a
          _ ≤ L*(r/L) := mul_le_mul_of_nonneg_left hxd hL.le
          _ = r := mul_div_cancel₀ r hL.ne'
      have hcount : coverCount A rho a (r/L) ≤ ((B.image (label rho)).card:ℝ) :=
        Nat.cast_le.mpr (card_le_card (image_subset_image (f:=label rho) hsub))
      have hlo := (H a ha (r/L) hquery ((div_le_self hrp.le hL1).trans hr1)).1
      have hid : r/rho=L*((r/L)/rho) := by field_simp
      have hp : (r/rho)^s=L^s*((r/L)/rho)^s := by
        rw [hid,Real.mul_rpow hL.le (by positivity)]
      have heq : (r/rho)^s/(L^s*K)=((r/L)/rho)^s/K := by
        rw [hp]
        exact mul_div_mul_left _ _ hLp.ne'
      rw [heq]
      exact hlo.trans hcount
    · have hsmall : r/rho ≤ L := by
        apply (div_le_iff₀ hrho).mpr
        have hh := (div_lt_iff₀ hL).mp (lt_of_not_ge hquery)
        linarith only [hh]
      have hp := Real.rpow_le_rpow (by positivity : (0:ℝ) ≤ r/rho) hsmall hs
      have hone : (r/rho)^s/(L^s*K) ≤ 1 :=
        (div_le_one (mul_pos hLp hKp)).mpr (hp.trans (le_mul_of_one_le_right hLp.le hK))
      have haB : a∈B := mem_filter.mpr ⟨ha,by simp only [dist_self]; exact hrp.le⟩
      exact hone.trans (Nat.one_le_cast.mpr (card_pos.mpr ⟨label rho a,mem_image_of_mem _ haB⟩))
  · have hsub : B ⊆ carrierBall A a r := by
      intro x hx
      obtain ⟨hxA,hxd⟩ := mem_filter.mp hx
      exact mem_filter.mpr ⟨hxA,(sup_dist_le_toLp x a).trans hxd⟩
    have hc : ((B.image (label rho)).card:ℝ) ≤ coverCount A rho a r :=
      Nat.cast_le.mpr (card_le_card (image_subset_image (f:=label rho) hsub))
    exact (hc.trans (H a ha r hr hr1).2).trans
      (mul_le_mul_of_nonneg_right hKcost (by positivity))

end NativeLiteralGridEuclideanCover
