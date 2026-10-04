import Theorems.Thm_StickyKakeya4_original_shading_representatives
import Theorems.Thm_StickyKakeya4_planar_frostman_ball_conversion
import Mathlib.Data.Int.Interval

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2600000

noncomputable section
namespace OriginalSeparatedPointPacking
open Classical PlanarFrostmanBallConversion PlanarStripIntersection
open OriginalShadingGridGeometry OriginalShadingRepresentatives

/-- Euclidean separation of the actual original points makes the literal
floor grid at mesh delta/4 injective. -/
theorem original_separated_floor_injective (Pts : Finset (ℝ×ℝ)) (delta : ℝ)
    (hd : 0<delta)
    (hsep : ∀ p∈Pts, ∀ q∈Pts, p≠q → delta≤euclideanDistance p q) :
    Set.InjOn (grid (delta/4)) (↑Pts : Set (ℝ×ℝ)) := by
  intro p hp q hq heq
  by_contra hne
  have hc := same_cell_close (by positivity : 0<delta/4) p q heq
  have hbox : boxDistance p q≤delta/4 := max_le
    (by simpa only [abs_sub_comm] using hc.1) (by simpa only [abs_sub_comm] using hc.2)
  have he := euclidean_le_two_box p q
  have hs := hsep p hp q hq hne
  linarith only [hbox,he,hs,hd]

/-- Original Euclidean delta-separation in the unit square derives the
actual source population bound; no cardinality certificate is supplied. -/
theorem original_separated_square_packing (Pts : Finset (ℝ×ℝ)) (delta : ℝ)
    (hd : 0<delta) (hd1 : delta≤1)
    (hbox : ∀ p∈Pts, |p.1|≤1 ∧ |p.2|≤1)
    (hsep : ∀ p∈Pts, ∀ q∈Pts, p≠q → delta≤euclideanDistance p q) :
    (Pts.card : ℝ)*delta^2≤100 := by
  let h := delta/4
  let A : ℤ := ⌊(-1:ℝ)/h⌋
  let B : ℤ := ⌊(1:ℝ)/h⌋
  let I := Finset.Icc A B
  have hh : 0<h := by dsimp [h]; positivity
  have hAB : A≤B := Int.floor_mono (div_le_div_of_nonneg_right (by norm_num : (-1:ℝ)≤1) hh.le)
  have hI : (I.card : ℝ)=(B:ℝ)+1-(A:ℝ) := by
    exact_mod_cast (Int.card_Icc_of_le A B (by omega : A≤B+1))
  have hIB : (I.card : ℝ)≤8/delta+2 := by
    have hB := Int.floor_le ((1:ℝ)/h)
    have hA := Int.lt_floor_add_one ((-1:ℝ)/h)
    change (B:ℝ)≤1/h at hB
    change -1/h<(A:ℝ)+1 at hA
    rw [hI]
    dsimp [h] at hB hA
    have h1 : (1:ℝ)/(delta/4)=4/delta := by ring
    have h2 : (-1:ℝ)/(delta/4)= -(4/delta) := by ring
    rw [h1] at hB
    rw [h2] at hA
    rw [show 8/delta=2*(4/delta) by ring]
    linarith only [hB,hA]
  have hId : (I.card : ℝ)*delta≤10 := by
    have hh := mul_le_mul_of_nonneg_right hIB hd.le
    have he : (8/delta+2)*delta=8+2*delta := by field_simp
    rw [he] at hh
    linarith only [hh,hd1]
  have hmap : ∀ p∈Pts, grid h p∈I.product I := by
    intro p hp
    obtain ⟨hp1,hp2⟩ := hbox p hp
    obtain ⟨hpl1,hpu1⟩ := abs_le.mp hp1
    obtain ⟨hpl2,hpu2⟩ := abs_le.mp hp2
    exact Finset.mem_product.mpr
      ⟨Finset.mem_Icc.mpr ⟨Int.floor_mono (div_le_div_of_nonneg_right hpl1 hh.le),
        Int.floor_mono (div_le_div_of_nonneg_right hpu1 hh.le)⟩,
       Finset.mem_Icc.mpr ⟨Int.floor_mono (div_le_div_of_nonneg_right hpl2 hh.le),
        Int.floor_mono (div_le_div_of_nonneg_right hpu2 hh.le)⟩⟩
  have hcard : Pts.card≤I.card*I.card := by
    have hh := Finset.card_le_card_of_injOn (grid h) hmap
      (original_separated_floor_injective Pts delta hd hsep)
    simpa only [Finset.product_eq_sprod,Finset.card_product] using hh
  have hreal : (Pts.card : ℝ)≤(I.card : ℝ)^2 := by
    rw [pow_two]
    exact_mod_cast hcard
  have hmul := mul_le_mul_of_nonneg_right hreal (sq_nonneg delta)
  have hsq := pow_le_pow_left₀ (show 0≤(I.card : ℝ)*delta by positivity) hId 2
  nlinarith only [hmul,hsq]

end OriginalSeparatedPointPacking
