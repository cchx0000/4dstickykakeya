import Theorems.Thm_StickyKakeya4_partitioned_collision_energy
import Theorems.Thm_StickyKakeya4_dyadic_original_fiber_selection

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

open scoped BigOperators
noncomputable section

namespace HeavyEnergyBinSelection
open TwoTubePathCollisionCount PartitionedCollisionEnergy DyadicOriginalFiberSelection

/-- A finite selection using the exact total original-label mass, with a
linear-density retained bin and a quadratic logarithmic energy loss. -/
theorem exists_heavy_energy_index (L : ℕ) (hL : 0<L)
    (p e : ℕ → ℝ) (P A nu : ℝ) (hP : 0<P) (hA : 0<A) (hnu : 0<nu)
    (hp : ∀ j∈Finset.range L, 0≤p j)
    (hsum : ∑ j∈Finset.range L, p j=P)
    (hcap : ∀ j∈Finset.range L, e j≤A*(p j)^2)
    (henergy : nu*A*P^2≤(L:ℝ)*∑ j∈Finset.range L, e j) :
    ∃ j∈Finset.range L, nu*P≤2*(L:ℝ)*p j ∧
      nu*A*P^2≤2*(L:ℝ)^2*e j := by
  have hLR : (0:ℝ)<L := by exact_mod_cast hL
  let D := nu*A*P/(2*(L:ℝ))
  let T := nu*A*P^2/(2*(L:ℝ)^2)
  have hD : 0<D := by dsimp [D]; positivity
  have hT : 0<T := by dsimp [T]; positivity
  by_contra hnone
  have hall (j : ℕ) (hj : j∈Finset.range L) : e j<D*p j+T := by
    by_cases hm : nu*P≤2*(L:ℝ)*p j
    · have he : e j<T := by
        have hn : ¬nu*A*P^2≤2*(L:ℝ)^2*e j := fun h => hnone ⟨j,hj,hm,h⟩
        apply (lt_div_iff₀ (by positivity : 0<2*(L:ℝ)^2)).mpr
        nlinarith only [lt_of_not_ge hn]
      exact he.trans_le (le_add_of_nonneg_left (mul_nonneg hD.le (hp j hj)))
    · have hjb : p j≤nu*P/(2*(L:ℝ)) := by
        apply (le_div_iff₀ (by positivity : 0<2*(L:ℝ))).mpr
        nlinarith only [le_of_lt (lt_of_not_ge hm)]
      have he : e j≤D*p j := by
        have hmul := mul_le_mul_of_nonneg_left hjb (mul_nonneg hA.le (hp j hj))
        calc
          _ ≤ A*(p j)^2 := hcap j hj
          _ ≤ (A*p j)*(nu*P/(2*(L:ℝ))) := by nlinarith only [hmul]
          _ = D*p j := by dsimp [D]; ring
      exact he.trans_lt (lt_add_of_pos_right _ hT)
  have hsumlt : (∑ j∈Finset.range L, e j)<
      ∑ j∈Finset.range L, (D*p j+T) :=
    Finset.sum_lt_sum (fun j hj => (hall j hj).le)
      ⟨0,Finset.mem_range.mpr hL,hall 0 (Finset.mem_range.mpr hL)⟩
  have heq : (∑ j∈Finset.range L, (D*p j+T))=D*P+(L:ℝ)*T := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, hsum]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [heq] at hsumlt
  have hh := mul_lt_mul_of_pos_left hsumlt hLR
  have htotal : (L:ℝ)*(D*P+(L:ℝ)*T)=nu*A*P^2 := by
    dsimp [D,T]
    field_simp
    ring
  rw [htotal] at hh
  exact (not_lt_of_ge henergy) hh

/-- On a product, partitioning original pair labels leaves every A-fiber
intact. -/
theorem product_partition_piece
    {G P : Type*} [DecidableEq G] [DecidableEq P]
    (A : Finset G) (W : Finset P) (f : P → G) (j : ℕ) :
    piece (A.product W) (fun p => level W f p.2) j = A.product (bin W f j) := by
  ext p
  simp only [piece, bin, Finset.product_eq_sprod, Finset.mem_filter, Finset.mem_product, and_assoc]

/-- This selected bin is constructed from original pair labels and actual
sum histograms. Its energy and original mass are retained simultaneously. -/
theorem exists_original_energy_bin
    {G P : Type*} [AddCommGroup G] [DecidableEq G] [DecidableEq P]
    (A : Finset G) (W : Finset P) (f : P → G)
    (hA : A.Nonempty) (hW : W.Nonempty) {nu : ℝ} (hnu : 0<nu)
    (he : nu*(A.card : ℝ)*(W.card : ℝ)^2 ≤
      ((collisions (A.product W) (fun p => p.1+f p.2)).card : ℝ)) :
    ∃ j<levelCount W, (bin W f j).Nonempty ∧
      nu*(W.card : ℝ)≤2*(levelCount W : ℝ)*(bin W f j).card ∧
      nu*(A.card : ℝ)*(W.card : ℝ)^2 ≤ 2*(levelCount W : ℝ)^2*
        ((collisions (A.product (bin W f j)) (fun p => p.1+f p.2)).card : ℝ) := by
  have hsplit := partition_collision_energy (A.product W) (fun p => p.1+f p.2)
    (fun p => level W f p.2) (levelCount W) (fun p _ => level_lt W f p.2)
  simp_rw [product_partition_piece] at hsplit
  have hsplitR : ((collisions (A.product W) (fun p => p.1+f p.2)).card : ℝ) ≤
      (levelCount W : ℝ)*∑ j∈Finset.range (levelCount W),
        ((collisions (A.product (bin W f j)) (fun p => p.1+f p.2)).card : ℝ) := by
    exact_mod_cast hsplit
  have hAc : (0:ℝ)<A.card := by exact_mod_cast hA.card_pos
  have hWc : (0:ℝ)<W.card := by exact_mod_cast hW.card_pos
  obtain ⟨j,hj,hm,he'⟩ := exists_heavy_energy_index (levelCount W) (Nat.zero_lt_succ _)
    (fun j => ((bin W f j).card : ℝ))
    (fun j => ((collisions (A.product (bin W f j)) (fun p => p.1+f p.2)).card : ℝ))
    W.card A.card nu hWc hAc hnu (fun _ _ => Nat.cast_nonneg _)
    (by exact_mod_cast bin_card_sum W f)
    (fun j _ => by exact_mod_cast translated_pair_energy_cap A (bin W f j) f)
    (he.trans hsplitR)
  have hbinpos : (0:ℝ)<(bin W f j).card := by
    have hL : (0:ℝ)<levelCount W := by exact_mod_cast (Nat.zero_lt_succ (Nat.log 2 W.card))
    nlinarith only [hm,mul_pos hnu hWc,hL]
  exact ⟨j,Finset.mem_range.mp hj,Finset.card_pos.mp (by exact_mod_cast hbinpos),hm,he'⟩

end HeavyEnergyBinSelection
