import Theorems.Thm_StickyKakeya4_original_height_window_macro_cells
import Theorems.Thm_StickyKakeya4_original_literal_macro_slice_upper
import Theorems.Thm_StickyKakeya4_original_whole_macro_window
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
noncomputable section
namespace OriginalLiteralDenseMacroHeight
open Classical Finset NativeTangentGridCoarsening OriginalWGrainDrift OriginalPhaseCellPopulation
open OriginalMacroGrainReadback OriginalLiteralGrainProfiles OriginalWeightedMacroSelection
open OriginalLiteralMacroDensity OriginalLiteralHeightWindow OriginalWholeMacroWindow
open scoped BigOperators
variable {P : Type*}
private theorem local_points_upper (E : Finset P) (height x : P → ℝ) (y : P → ℝ × ℝ)
    (F : ℝ → ℝ →L[ℝ] ℝ × ℝ) (k : ℤ × (ℤ × (ℤ × ℤ))) {delta q K t : ℝ}
    (hd : 0 < delta) (hdq : delta ≤ q) (hq1 : 4*q ≤ 1) (hK : 0 ≤ K) (ht2 : t ≤ 2)
    (hsep : ∀ p ∈ E, ∀ p0 ∈ E, p ≠ p0 → delta ≤
      dist (OriginalTubeSliceOccupancy.embedding height x y p) (OriginalTubeSliceOccupancy.embedding height x y p0))
    (hF : ∀ z ∈ E.image height, ‖F z‖ ≤ 1)
    (hY : ∀ z ∈ E.image height, LiteralCoverAD (grains E height (grainCoordinate height x y F) z) delta K t) :
    ((localPoints E (physicalCell q height x y) k).card:ℝ) ≤
      155520*K*(q/delta)^(t+1)*(localHeights E (physicalCell q height x y) height k).card := by
  let Q := localPoints E (physicalCell q height x y) k
  have hQ : Q ⊆ E := filter_subset _ _
  have hf : ∀ z ∈ Q.image height, ((Q.filter (fun p => height p=z)).card:ℝ) ≤ 155520*K*(q/delta)^(t+1) := by
    intro z hz
    have hzE : z ∈ E.image height := image_subset_image hQ hz
    exact OriginalLiteralMacroSliceUpper.original_macro_height_point_upper E (Q.filter (fun p => height p=z))
      ((filter_subset _ _).trans hQ) height x y F z k hd hdq hq1 hK ht2 hsep
      (fun p hp => (mem_filter.mp hp).2) (fun p hp => (mem_filter.mp (mem_filter.mp hp).1).2)
      (hF z hzE) (hY z hzE)
  have hs : (Q.card:ℝ)=∑ z ∈ Q.image height, ((Q.filter (fun p => height p=z)).card:ℝ) := by
    exact_mod_cast card_eq_sum_card_image height Q
  change (Q.card:ℝ) ≤ 155520*K*(q/delta)^(t+1)*(Q.image height).card
  rw [hs]
  calc
    _ ≤ ∑ _z ∈ Q.image height, 155520*K*(q/delta)^(t+1) := sum_le_sum hf
    _ = _ := by simp [mul_comm]
private theorem exists_window_dense_macro (E : Finset P) (hE : E.Nonempty)
    (height x : P → ℝ) (y : P → ℝ × ℝ) (F : ℝ → ℝ →L[ℝ] ℝ × ℝ)
    (z0 : ℝ) (j : ℤ) {delta q K t L : ℝ}
    (hd : 0 < delta) (hdq : delta ≤ q) (hq1 : 4*q ≤ 1) (hK : 1 ≤ K) (ht : 0 ≤ t) (ht2 : t ≤ 2)
    (hL : 0 ≤ L) (hheight : ∀ p ∈ E, ⌊height p/q⌋=j)
    (hheightmass : q ≤ 4*K*delta*((E.image height).card:ℝ))
    (hx : ∀ p ∈ E, |x p| ≤ 1) (hF0 : ‖F z0‖ ≤ 1)
    (hF : ∀ z ∈ E.image height, ‖F z‖ ≤ 1)
    (hosc : ∀ p ∈ E, ‖F (height p)-F z0‖ ≤ L*q)
    (hsep : ∀ p ∈ E, ∀ p0 ∈ E, p ≠ p0 → delta ≤
      dist (OriginalTubeSliceOccupancy.embedding height x y p) (OriginalTubeSliceOccupancy.embedding height x y p0))
    (hYbox : ∀ z ∈ E.image height, ∀ g ∈ grains E height (grainCoordinate height x y F) z, ‖g‖ ≤ 1)
    (hY : ∀ z ∈ E.image height, LiteralCoverAD (grains E height (grainCoordinate height x y F) z) delta K t)
    (hX : ∀ z ∈ E.image height, ∀ g ∈ grains E height (grainCoordinate height x y F) z,
      1 ≤ K*delta*((scalarCells (tangentFiber E height (grainCoordinate height x y F) z g) x delta).card:ℝ))
    (hUnion : LiteralCoverAD (E.image (grainCoordinate height x y F)) q K t) :
    ∃ k ∈ E.image (physicalCell q height x y), (localPoints E (physicalCell q height x y) k).Nonempty ∧
      q^(t+1)*(localHeights E (physicalCell q height x y) height k).card ≤
        79626240000*K^4*delta^(t+1)*(localPoints E (physicalCell q height x y) k).card ∧
      ((localPoints E (physicalCell q height x y) k).card:ℝ) ≤
        155520*K*(q/delta)^(t+1)*(localHeights E (physicalCell q height x y) height k).card ∧
      q ≤ 124416000*K^5*(2*L+4)^2*delta*(localHeights E (physicalCell q height x y) height k).card := by
  have hq : 0 < q := hd.trans_le hdq
  have hqone : q ≤ 1 := by linarith
  have hK0 : 0 < K := lt_of_lt_of_le (by norm_num) hK
  have hUbox : ∀ g ∈ E.image (grainCoordinate height x y F), ‖g‖ ≤ 1 := by
    intro g hg
    obtain ⟨p,hp,rfl⟩ := mem_image.mp hg
    exact hYbox (height p) (mem_image_of_mem _ hp) _ (mem_image_of_mem _ (mem_filter.mpr ⟨hp,rfl⟩))
  have hmacros := OriginalHeightWindowMacroCells.original_window_macro_grid_mass E height x y F z0 j
    hq hqone hL hK0.le hheight hx hF0 hosc hUbox hUnion
  have hmacro_read : physicalCells E q height x y=E.image (physicalCell q height x y) := by
    ext k
    simp only [physicalCells,mem_image]
  rw [hmacro_read] at hmacros
  have hglobal := original_literal_global_point_mass E height x (grainCoordinate height x y F)
    hd (hdq.trans hqone) hK0 hY hX
  have hden := original_literal_Y_macro_denominator E height x y F hd hdq hqone hK ht ht2 hF hx hYbox hY
  obtain ⟨k,hk,hkn,hmass,hweight⟩ := exists_physical_weighted_macro E height x y q hE
  have hupper := local_points_upper E height x y F k hd hdq hq1 hK0.le ht2 hsep hF hY
  have hpow : delta^(t+1)*(q/delta)^(t+1)=q^(t+1) := by
    have hp := Real.rpow_pos_of_pos hd (t+1)
    rw [Real.div_rpow hq.le hd.le]
    field_simp
  have hZ : ((E.image height).card:ℝ) ≤
      31104000*K^4*(2*L+4)^2*(localHeights E (physicalCell q height x y) height k).card := by
    calc
      _ ≤ K^2*delta^(t+1)*(E.card:ℝ) := hglobal
      _ ≤ K^2*delta^(t+1)*(2*((E.image (physicalCell q height x y)).card:ℝ)*
          (localPoints E (physicalCell q height x y) k).card) :=
        mul_le_mul_of_nonneg_left hmass (by positivity)
      _ ≤ K^2*delta^(t+1)*(2*((E.image (physicalCell q height x y)).card:ℝ)*
          (155520*K*(q/delta)^(t+1)*(localHeights E (physicalCell q height x y) height k).card)) := by
        gcongr
      _ = 311040*K^3*(delta^(t+1)*(q/delta)^(t+1))*
          ((E.image (physicalCell q height x y)).card:ℝ)*(localHeights E (physicalCell q height x y) height k).card := by ring
      _ = 311040*K^3*(q^(t+1)*((E.image (physicalCell q height x y)).card:ℝ))*
          (localHeights E (physicalCell q height x y) height k).card := by rw [hpow]; ring
      _ ≤ 311040*K^3*(100*K*(2*L+4)^2)*(localHeights E (physicalCell q height x y) height k).card := by
        gcongr
      _ = _ := by ring
  refine ⟨k,hk,hkn,?_,hupper,?_⟩
  · have hE0 : (0:ℝ)<E.card := Nat.cast_pos.mpr hE.card_pos
    apply (mul_le_mul_iff_left₀ hE0).mp
    have h1 := mul_le_mul_of_nonneg_left hweight (Real.rpow_pos_of_pos hq (t+1)).le
    have h2 := mul_le_mul_of_nonneg_right hden
      (show 0 ≤ 2*((localPoints E (physicalCell q height x y) k).card:ℝ) by positivity)
    have h3 := mul_le_mul_of_nonneg_right hglobal
      (show 0 ≤ 79626240000*K^2*((localPoints E (physicalCell q height x y) k).card:ℝ) by positivity)
    nlinarith only [h1,h2,h3]
  · have hh := hheightmass.trans (mul_le_mul_of_nonneg_left hZ (show 0 ≤ 4*K*delta by positivity))
    nlinarith only [hh]
/-- Select a genuine original macro-cell with BOTH its point/height ratio
 and an absolute height population. The height window, its union-Y count,
 and the local height-fiber upper bound are all derived on original labels.
 The only coarse Y input is the literal scheduled union law of Definition
 17.2(3), read as the exact original grain image in each height interval. -/
theorem exists_original_macro_with_height_population
    (E : Finset P) (height x : P → ℝ) (y : P → ℝ × ℝ) (F : ℝ → ℝ →L[ℝ] ℝ × ℝ)
    {delta q K t L : ℝ} (hd : 0 < delta) (hdq : delta ≤ q) (hq1 : 4*q ≤ 1)
    (hK : 1 ≤ K) (ht : 0 ≤ t) (ht2 : t ≤ 2) (hL : 0 ≤ L)
    (hZbox : ∀ z ∈ E.image height, |z| ≤ 1)
    (hZmass : 1 ≤ K*delta*((E.image height).card:ℝ))
    (hx : ∀ p ∈ E, |x p| ≤ 1)
    (hMat : ∀ z ∈ E.image height, |(F z 1).1| ≤ 1 ∧ |(F z 1).2| ≤ 1)
    (hosc : ∀ z ∈ E.image height, ∀ z0 ∈ E.image height,
      ⌊z/q⌋=⌊z0/q⌋ → ‖F z-F z0‖ ≤ L*q)
    (hsep : ∀ p ∈ E, ∀ p0 ∈ E, p ≠ p0 → delta ≤
      dist (OriginalTubeSliceOccupancy.embedding height x y p) (OriginalTubeSliceOccupancy.embedding height x y p0))
    (hYbox : ∀ z ∈ E.image height, ∀ g ∈ grains E height (grainCoordinate height x y F) z, ‖g‖ ≤ 1)
    (hY : ∀ z ∈ E.image height, LiteralCoverAD (grains E height (grainCoordinate height x y F) z) delta K t)
    (hX : ∀ z ∈ E.image height, ∀ g ∈ grains E height (grainCoordinate height x y F) z,
      1 ≤ K*delta*((scalarCells (tangentFiber E height (grainCoordinate height x y F) z g) x delta).card:ℝ))
    (hUnion : ∀ j : ℤ, (window E height q j).Nonempty →
      LiteralCoverAD ((window E height q j).image (grainCoordinate height x y F)) q K t) :
    ∃ k ∈ E.image (physicalCell q height x y), (localPoints E (physicalCell q height x y) k).Nonempty ∧
      q^(t+1)*(localHeights E (physicalCell q height x y) height k).card ≤
        79626240000*K^4*delta^(t+1)*(localPoints E (physicalCell q height x y) k).card ∧
      ((localPoints E (physicalCell q height x y) k).card:ℝ) ≤
        155520*K*(q/delta)^(t+1)*(localHeights E (physicalCell q height x y) height k).card ∧
      q ≤ 124416000*K^5*(2*L+4)^2*delta*(localHeights E (physicalCell q height x y) height k).card := by
  have hq : 0 < q := hd.trans_le hdq
  have hqone : q ≤ 1 := by linarith
  have hK0 : 0 < K := lt_of_lt_of_le (by norm_num) hK
  obtain ⟨j,_hj,hWne,hWmass⟩ := exists_populated_height_window E height hd hq hqone hK0 hZbox hZmass
  let W := window E height q j
  let grain := grainCoordinate height x y F
  have hWE : W ⊆ E := filter_subset _ _
  have hr : ∀ z ∈ W.image height, z ∈ E.image height ∧
      grains W height grain z=grains E height grain z ∧
      ∀ g, tangentFiber W height grain z g=tangentFiber E height grain z g :=
    fun z hz => actual_grain_fiber_readback E height grain q j z hz
  have hWF : ∀ z ∈ W.image height, ‖F z‖ ≤ 1 := fun z hz =>
    matrix_entry_operator_bound (F z) (hMat z (hr z hz).1).1 (hMat z (hr z hz).1).2
  have hWYbox : ∀ z ∈ W.image height, ∀ g ∈ grains W height grain z, ‖g‖ ≤ 1 := by
    intro z hz g hg
    rw [(hr z hz).2.1] at hg
    exact hYbox z (hr z hz).1 g hg
  have hWY : ∀ z ∈ W.image height, LiteralCoverAD (grains W height grain z) delta K t := by
    intro z hz
    rw [(hr z hz).2.1]
    exact hY z (hr z hz).1
  have hWX : ∀ z ∈ W.image height, ∀ g ∈ grains W height grain z,
      1 ≤ K*delta*((scalarCells (tangentFiber W height grain z g) x delta).card:ℝ) := by
    intro z hz g hg
    rw [(hr z hz).2.1] at hg
    rw [(hr z hz).2.2 g]
    exact hX z (hr z hz).1 g hg
  obtain ⟨p0,hp0⟩ := hWne
  have hoscW : ∀ p ∈ W, ‖F (height p)-F (height p0)‖ ≤ L*q := by
    intro p hp
    exact hosc (height p) (mem_image_of_mem _ (hWE hp)) (height p0) (mem_image_of_mem _ (hWE hp0))
      ((mem_filter.mp hp).2.trans (mem_filter.mp hp0).2.symm)
  obtain ⟨k,hk,hkn,hpoint,hupper,hheight⟩ := exists_window_dense_macro W ⟨p0,hp0⟩ height x y F (height p0) j
    hd hdq hq1 hK ht ht2 hL (fun p hp => (mem_filter.mp hp).2) hWmass
    (fun p hp => hx p (hWE hp)) (hWF (height p0) (mem_image_of_mem _ hp0)) hWF hoscW
    (fun p hp p1 hp1 hne => hsep p (hWE hp) p1 (hWE hp1) hne) hWYbox hWY hWX (hUnion j ⟨p0,hp0⟩)
  dsimp only [W] at hpoint hupper hheight
  have hread := actual_macro_readback E height x y q j k hk
  refine ⟨k,image_subset_image hWE hk,?_,?_,?_,?_⟩
  · rwa [hread.2.1] at hkn
  · simpa only [hread.2.1,hread.2.2] using hpoint
  · simpa only [hread.2.1,hread.2.2] using hupper
  · simpa only [hread.2.2] using hheight
end OriginalLiteralDenseMacroHeight
