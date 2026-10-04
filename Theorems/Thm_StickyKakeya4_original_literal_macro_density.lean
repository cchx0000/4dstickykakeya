import Theorems.Thm_StickyKakeya4_original_macro_grain_readback
import Theorems.Thm_StickyKakeya4_original_literal_grain_profiles
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000
noncomputable section
namespace OriginalLiteralMacroDensity
open Classical Finset NativeTangentGridCoarsening OriginalMacroGrainReadback OriginalLiteralGrainProfiles
open OriginalWeightedMacroSelection OriginalMacroSliceCellCount OriginalWGrainDrift OriginalPhaseCellPopulation
open scoped BigOperators
variable {P : Type*}
/-- Immediately before Definition 17.2, Mat(k,l) is defined to have all
 entries in [-1,1]. For l=1 and the product sup norm, this is exactly an
 operator norm bound of one. -/
theorem matrix_entry_operator_bound (F : ℝ →L[ℝ] ℝ × ℝ)
    (h1 : |(F 1).1| ≤ 1) (h2 : |(F 1).2| ≤ 1) : ‖F‖ ≤ 1 := by
  have hnorm : ‖F 1‖ ≤ 1 := max_le h1 h2
  apply F.opNorm_le_bound (by norm_num)
  intro v
  have heq : F v=v • F 1 := by simpa using F.map_smul v (1:ℝ)
  rw [heq,norm_smul,one_mul]
  exact (mul_le_mul_of_nonneg_left hnorm (norm_nonneg v)).trans_eq (mul_one _)

/-- Original tangent-fiber populations and LITERAL Euclidean cover AD give
 global point mass. No separation or point-count AD of original Y is assumed. -/
theorem original_literal_global_point_mass (E : Finset P) (height x : P → ℝ) (grain : P → ℝ × ℝ)
    {delta K t : ℝ} (hd : 0 < delta) (hd1 : delta ≤ 1) (hK : 0 < K)
    (hY : ∀ z ∈ E.image height, LiteralCoverAD (grains E height grain z) delta K t)
    (hX : ∀ z ∈ E.image height, ∀ g ∈ grains E height grain z,
      1 ≤ K*delta*((scalarCells (tangentFiber E height grain z g) x delta).card:ℝ)) :
    ((E.image height).card:ℝ) ≤ K^2*delta^(t+1)*(E.card:ℝ) := by
  have hslices : ∑ z ∈ E.image height, ((slice E height z).card:ℝ)=(E.card:ℝ) := by
    exact_mod_cast (card_eq_sum_card_image height E).symm
  have hlocal : ∀ z ∈ E.image height, 1 ≤ K^2*delta^(t+1)*((slice E height z).card:ℝ) := by
    intro z hz
    have hlow' := OriginalLiteralGrainProfiles.original_grain_mass_lower
      (grains E height grain z) (grains_nonempty E height grain hz) hd hd1 hK (hY z hz)
    have hfibers : ∑ g ∈ grains E height grain z, ((tangentFiber E height grain z g).card:ℝ)=
        ((slice E height z).card:ℝ) := by
      exact_mod_cast (card_eq_sum_card_image grain (slice E height z)).symm
    have hXcard : ∀ g ∈ grains E height grain z, 1 ≤ K*delta*((tangentFiber E height grain z g).card:ℝ) := by
      intro g hg
      have hc : ((scalarCells (tangentFiber E height grain z g) x delta).card:ℝ) ≤
          (tangentFiber E height grain z g).card := by exact_mod_cast card_image_le
      exact (hX z hz g hg).trans (mul_le_mul_of_nonneg_left hc (mul_nonneg hK.le hd.le))
    have hgrain : ((grains E height grain z).card:ℝ) ≤ K*delta*(slice E height z).card := by
      calc
        _ = ∑ _g ∈ grains E height grain z, (1:ℝ) := by simp
        _ ≤ ∑ g ∈ grains E height grain z, K*delta*((tangentFiber E height grain z g).card:ℝ) := sum_le_sum hXcard
        _ = K*delta*(∑ g ∈ grains E height grain z, ((tangentFiber E height grain z g).card:ℝ)) := (mul_sum _ _ _).symm
        _ = _ := by rw [hfibers]
    calc
      _ ≤ K*delta^t*(grains E height grain z).card := hlow'
      _ ≤ K*delta^t*(K*delta*(slice E height z).card) := mul_le_mul_of_nonneg_left hgrain (by positivity)
      _ = _ := by rw [Real.rpow_add hd,Real.rpow_one]; ring
  calc
    _ = ∑ _z ∈ E.image height, (1:ℝ) := by simp
    _ ≤ ∑ z ∈ E.image height, K^2*delta^(t+1)*((slice E height z).card:ℝ) := sum_le_sum hlocal
    _ = K^2*delta^(t+1)*(∑ z ∈ E.image height, ((slice E height z).card:ℝ)) := (mul_sum _ _ _).symm
    _ = _ := by rw [hslices]
/-- The exact macro-cell denominator is bounded from the literal source
 cover profiles on the unchanged original grain and point sets. -/
theorem original_literal_Y_macro_denominator (E : Finset P) (height x : P → ℝ) (y : P → ℝ × ℝ)
    (F : ℝ → ℝ →L[ℝ] ℝ × ℝ) {delta q K t : ℝ}
    (hd : 0 < delta) (hdq : delta ≤ q) (hq1 : q ≤ 1) (hK : 1 ≤ K) (ht : 0 ≤ t) (ht2 : t ≤ 2)
    (hF : ∀ z ∈ E.image height, ‖F z‖ ≤ 1) (hx : ∀ p ∈ E, |x p| ≤ 1)
    (hYbox : ∀ z ∈ E.image height, ∀ g ∈ grains E height (grainCoordinate height x y F) z, ‖g‖ ≤ 1)
    (hY : ∀ z ∈ E.image height, LiteralCoverAD (grains E height (grainCoordinate height x y F) z) delta K t) :
    q^(t+1)*(∑ k ∈ E.image (physicalCell q height x y),
      ((localHeights E (physicalCell q height x y) height k).card:ℝ)) ≤
      39813120000*K^2*(E.image height).card := by
  have hq : 0 < q := hd.trans_le hdq
  have hden := original_macro_denominator E height x y F hq hq1 hF hx
  have hgrid : ∀ z ∈ E.image height,
      q^t*((grainCells (slice E height z) q height x y F).card:ℝ) ≤ 207360000*K^2 := by
    intro z hz
    rw [grain_grid_readback]
    exact OriginalLiteralGrainProfiles.original_literal_grain_grid_mass _ (grains_nonempty E height _ hz)
      hd hdq hq1 hK ht ht2 (hYbox z hz) (hY z hz)
  have hsum : q^t*(∑ z ∈ E.image height, ((grainCells (slice E height z) q height x y F).card:ℝ)) ≤
      (207360000*K^2)*(E.image height).card := by
    rw [mul_sum]
    calc
      _ ≤ ∑ _z ∈ E.image height, 207360000*K^2 := sum_le_sum hgrid
      _ = _ := by simp [mul_comm]
  have hid : q^(t+1)*(192/q)=192*q^t := by
    rw [Real.rpow_add hq,Real.rpow_one]
    field_simp
  calc
    _ ≤ q^(t+1)*((192/q)*∑ z ∈ E.image height, ((grainCells (slice E height z) q height x y F).card:ℝ)) :=
      mul_le_mul_of_nonneg_left hden (Real.rpow_pos_of_pos hq _).le
    _ = (192)*(q^t*(∑ z ∈ E.image height, ((grainCells (slice E height z) q height x y F).card:ℝ))) := by rw [←mul_assoc,hid]; ring
    _ ≤ (192)*((207360000*K^2)*(E.image height).card) := mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by ring
/-- A genuine source macro-cell for the lower population part of Eq. (146).
 Every AD premise is the literal ORIGINAL Euclidean cover law. -/
theorem exists_literal_dense_macro_of_slope_bound (E : Finset P) (hE : E.Nonempty) (height x : P → ℝ) (y : P → ℝ × ℝ)
    (F : ℝ → ℝ →L[ℝ] ℝ × ℝ) {delta q K t : ℝ}
    (hd : 0 < delta) (hdq : delta ≤ q) (hq1 : q ≤ 1) (hK : 1 ≤ K) (ht : 0 ≤ t) (ht2 : t ≤ 2)
    (hF : ∀ z ∈ E.image height, ‖F z‖ ≤ 1) (hx : ∀ p ∈ E, |x p| ≤ 1)
    (hYbox : ∀ z ∈ E.image height, ∀ g ∈ grains E height (grainCoordinate height x y F) z, ‖g‖ ≤ 1)
    (hY : ∀ z ∈ E.image height, LiteralCoverAD (grains E height (grainCoordinate height x y F) z) delta K t)
    (hX : ∀ z ∈ E.image height, ∀ g ∈ grains E height (grainCoordinate height x y F) z,
      1 ≤ K*delta*((scalarCells (tangentFiber E height (grainCoordinate height x y F) z g) x delta).card:ℝ)) :
    ∃ k ∈ E.image (physicalCell q height x y), (localPoints E (physicalCell q height x y) k).Nonempty ∧
      q^(t+1)*(localHeights E (physicalCell q height x y) height k).card ≤
        79626240000*K^4*delta^(t+1)*(localPoints E (physicalCell q height x y) k).card := by
  have hq : 0 < q := hd.trans_le hdq
  have hK0 : 0 < K := lt_of_lt_of_le (by norm_num) hK
  have hglobal := original_literal_global_point_mass E height x (grainCoordinate height x y F)
    hd (hdq.trans hq1) hK0 hY hX
  have hden := original_literal_Y_macro_denominator E height x y F hd hdq hq1 hK ht ht2 hF hx hYbox hY
  obtain ⟨k,hk,hkn,_hm,hweight⟩ := exists_physical_weighted_macro E height x y q hE
  have hE0 : (0:ℝ)<E.card := Nat.cast_pos.mpr hE.card_pos
  refine ⟨k,hk,hkn,?_⟩
  apply (mul_le_mul_iff_left₀ hE0).mp
  have h1 := mul_le_mul_of_nonneg_left hweight (Real.rpow_pos_of_pos hq (t+1)).le
  have h2 := mul_le_mul_of_nonneg_right hden
    (show 0 ≤ 2*((localPoints E (physicalCell q height x y) k).card:ℝ) by positivity)
  have h3 := mul_le_mul_of_nonneg_right hglobal
    (show 0 ≤ 79626240000*K^2*((localPoints E (physicalCell q height x y) k).card:ℝ) by positivity)
  nlinarith only [h1,h2,h3]
/-- The literal Mat(2,1) entry bound supplies the operator bound. No
point-count AD, separation of Y, or auxiliary source slope estimate is used. -/
theorem exists_literal_source_dense_macro (E : Finset P) (hE : E.Nonempty)
    (height x : P → ℝ) (y : P → ℝ × ℝ) (F : ℝ → ℝ →L[ℝ] ℝ × ℝ)
    {delta q K t : ℝ} (hd : 0 < delta) (hdq : delta ≤ q) (hq1 : q ≤ 1)
    (hK : 1 ≤ K) (ht : 0 ≤ t) (ht2 : t ≤ 2)
    (hMat : ∀ z ∈ E.image height, |(F z 1).1| ≤ 1 ∧ |(F z 1).2| ≤ 1)
    (hx : ∀ p ∈ E, |x p| ≤ 1)
    (hYbox : ∀ z ∈ E.image height, ∀ g ∈ grains E height (grainCoordinate height x y F) z, ‖g‖ ≤ 1)
    (hY : ∀ z ∈ E.image height, LiteralCoverAD (grains E height (grainCoordinate height x y F) z) delta K t)
    (hX : ∀ z ∈ E.image height, ∀ g ∈ grains E height (grainCoordinate height x y F) z,
      1 ≤ K*delta*((scalarCells (tangentFiber E height (grainCoordinate height x y F) z g) x delta).card:ℝ)) :
    ∃ k ∈ E.image (physicalCell q height x y), (localPoints E (physicalCell q height x y) k).Nonempty ∧
      q^(t+1)*(localHeights E (physicalCell q height x y) height k).card ≤
        79626240000*K^4*delta^(t+1)*(localPoints E (physicalCell q height x y) k).card := by
  have hF : ∀ z ∈ E.image height, ‖F z‖ ≤ 1 := fun z hz =>
    matrix_entry_operator_bound (F z) (hMat z hz).1 (hMat z hz).2
  obtain ⟨k,hk,hkn,hbound⟩ := exists_literal_dense_macro_of_slope_bound E hE height x y F
    hd hdq hq1 hK ht ht2 hF hx hYbox hY hX
  exact ⟨k,hk,hkn,hbound⟩
end OriginalLiteralMacroDensity
