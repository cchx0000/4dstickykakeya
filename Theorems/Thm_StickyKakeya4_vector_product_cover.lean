import Theorems.Thm_StickyKakeya4_planar_rounded_sumset_cover

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2200000
open Finset
open scoped Pointwise
noncomputable section
open Classical

namespace VectorProductCover
open PlanarShiftedNearEnergy PlanarRoundedSumsetCover

lemma rounded_grid_add_scalar {eta : ℝ} (heta : 0 < eta) (a : ℝ) (k : ℤ) :
    ActualRoundedAdditiveEnergy.rounded eta (a + eta * (k : ℝ)) =
      ActualRoundedAdditiveEnergy.rounded eta a + k := by
  have he : (a + eta * (k : ℝ)) / eta = a / eta + (k : ℝ) := by field_simp
  unfold ActualRoundedAdditiveEnergy.rounded
  rw [he, Int.floor_add_intCast]

lemma roundPoint_grid_add {eta : ℝ} (heta : 0 < eta) (a : ℝ × ℝ) (k : ℤ × ℤ) :
    roundPoint eta (a + synthesis eta k) = roundPoint eta a + k := by
  apply Prod.ext
  · exact rounded_grid_add_scalar heta a.1 k.1
  · exact rounded_grid_add_scalar heta a.2 k.2

lemma roundPoint_grid_triple {eta : ℝ} (heta : 0 < eta) (a : ℝ × ℝ) (s t : ℤ × ℤ) :
    roundPoint eta (a + synthesis eta s - synthesis eta t) = roundPoint eta a + s - t := by
  have he : a + synthesis eta s - synthesis eta t = a + synthesis eta (s - t) := by
    rw [map_sub]
    abel
  rw [he, roundPoint_grid_add heta]
  abel

/-- Rounded sums with exact coupled grid points equal the literal integer
sumset; neither coordinate is independently selected. -/
lemma grid_triple_rounding (A : Finset (ℝ × ℝ)) (S : Finset (ℤ × ℤ))
    {eta : ℝ} (heta : 0 < eta) :
    ((A + S.image (synthesis eta) - S.image (synthesis eta)).image (roundPoint eta)) =
      A.image (roundPoint eta) + S - S := by
  ext z
  constructor
  · intro hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨y, hy, t, ht, rfl⟩ := Finset.mem_sub.mp hx
    obtain ⟨a, ha, s, hs, rfl⟩ := Finset.mem_add.mp hy
    obtain ⟨si, hsi, rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨ti, hti, rfl⟩ := Finset.mem_image.mp ht
    rw [roundPoint_grid_triple heta]
    exact Finset.mem_sub.mpr ⟨roundPoint eta a + si,
      Finset.mem_add.mpr ⟨roundPoint eta a, Finset.mem_image_of_mem _ ha, si, hsi, rfl⟩,
      ti, hti, rfl⟩
  · intro hz
    obtain ⟨y, hy, t, ht, rfl⟩ := Finset.mem_sub.mp hz
    obtain ⟨a, ha, s, hs, rfl⟩ := Finset.mem_add.mp hy
    obtain ⟨a0, ha0, rfl⟩ := Finset.mem_image.mp ha
    refine Finset.mem_image.mpr ⟨a0 + synthesis eta s - synthesis eta t, ?_, roundPoint_grid_triple heta a0 s t⟩
    exact Finset.mem_sub.mpr ⟨a0 + synthesis eta s,
      Finset.mem_add.mpr ⟨a0, ha0, synthesis eta s, Finset.mem_image_of_mem _ hs, rfl⟩,
      synthesis eta t, Finset.mem_image_of_mem _ ht, rfl⟩

/-- Transfer the BSG cover from selected grid values to ACTUAL original
product values, with the explicit planar factor49 from existing rounding cover. -/
theorem actual_product_triple_cover (A V : Finset (ℝ × ℝ)) (S : Finset (ℤ × ℤ))
    {eta : ℝ} (heta : 0 < eta) (hV : V.image (roundPoint eta) = S) :
    ((A + V - V).image (roundPoint eta)).card ≤
      49 * ((A + S.image (synthesis eta) - S.image (synthesis eta)).image (roundPoint eta)).card := by
  have hh := actual_planar_iterated_cover V A heta 1 1
  norm_num only [one_nsmul, Nat.reduceAdd, Nat.reduceMul, Nat.reducePow] at hh
  rw [hV, ← grid_triple_rounding A S heta] at hh
  exact hh

end VectorProductCover
