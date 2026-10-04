import Theorems.Thm_StickyKakeya4_finite_voronoi_population
import Theorems.Thm_StickyKakeya4_native_tangent_grid_coarsening
import Theorems.Thm_StickyKakeya4_actual_rounded_additive_energy

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000
noncomputable section
open Classical
open scoped BigOperators

namespace OriginalCoefficientCoverNet
open ActualRoundedAdditiveEnergy NativeTangentGridCoarsening

/-- A maximal net of the ACTUAL coefficient carrier preserves at least a
quarter of its occupied floor cells as genuinely separated original points. -/
theorem exists_original_separated_coefficient_net (P : Finset ℝ) {delta : ℝ}
    (hd : 0 < delta) :
    ∃ Xi : Finset ℝ, Xi⊆P ∧
      (∀ x∈Xi, ∀ y∈Xi, x≠y → delta ≤ |x-y|) ∧
      ((P.image (rounded delta)).card:ℝ) ≤ 4*Xi.card := by
  obtain ⟨Xi,hXi,hsep,hcover⟩ := FiniteVoronoiPopulation.exists_separated_net P hd
  let F := fun c => (P.filter (fun x => |x-c| < delta)).image (rounded delta)
  have hsub : P.image (rounded delta)⊆Xi.biUnion F := by
    intro j hj
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hj
    obtain ⟨c,hc,hnear⟩ := hcover x hx
    apply Finset.mem_biUnion.mpr
    refine ⟨c,hc,Finset.mem_image.mpr ⟨x,?_,rfl⟩⟩
    exact Finset.mem_filter.mpr ⟨hx,by simpa only [Real.dist_eq] using hnear⟩
  have hF : ∀ c∈Xi, ((F c).card:ℝ) ≤ 4 := by
    intro c _hc
    have hh := scalar_centered_grid_card (P.filter (fun x => |x-c| < delta)) id
      (c:=c) hd (by norm_num : (0:ℝ)≤1) (by
        intro x hx
        simpa only [id_eq,one_mul] using (Finset.mem_filter.mp hx).2.le)
    change (((P.filter (fun x => |x-c| < delta)).image (fun x : ℝ => ⌊x/delta⌋)).card:ℝ) ≤ 4
    simpa only [scalarCells,id_eq,show (2:ℝ)*1+2=4 by norm_num] using hh
  refine ⟨Xi,hXi,?_,?_⟩
  · intro x hx y hy hxy
    simpa only [Real.dist_eq] using hsep x hx y hy hxy
  · calc
      _ ≤ ((Xi.biUnion F).card:ℝ) := Nat.cast_le.mpr (Finset.card_le_card hsub)
      _ ≤ ∑ c∈Xi, ((F c).card:ℝ) := by exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ _c∈Xi, (4:ℝ) := Finset.sum_le_sum hF
      _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]; ring

/-- Positive original occupied density produces a nonempty actual
separated coefficient carrier, ready for the original collision count. -/
theorem exists_original_dense_coefficient_net (P : Finset ℝ) {delta L : ℝ}
    (hd : 0 < delta) (hL : 0 < L)
    (hcover : L ≤ delta*((P.image (rounded delta)).card:ℝ)) :
    ∃ Xi : Finset ℝ, Xi⊆P ∧ Xi.Nonempty ∧
      (∀ x∈Xi, ∀ y∈Xi, x≠y → delta ≤ |x-y|) ∧ L ≤ 4*delta*Xi.card := by
  obtain ⟨Xi,hXi,hsep,hcard⟩ := exists_original_separated_coefficient_net P hd
  have hh := mul_le_mul_of_nonneg_left hcard hd.le
  have hmass : L ≤ 4*delta*Xi.card := by nlinarith only [hcover,hh]
  have hN : (0:ℝ) < Xi.card := by nlinarith only [hL,hmass,hd]
  exact ⟨Xi,hXi,Finset.card_pos.mp (Nat.cast_pos.mp hN),hsep,hmass⟩

end OriginalCoefficientCoverNet
