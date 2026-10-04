import Theorems.Thm_StickyKakeya4_original_three_dimensional_heavy_cube_shading
import Theorems.Thm_StickyKakeya4_original_three_dimensional_tube_incidence_energy
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3200000

noncomputable section
open scoped BigOperators
namespace OriginalThreeDimensionalShadeLocalCount
open Classical OriginalThreeDimensionalBandGeometry OriginalThreeDimensionalHeavySlabs
open OriginalThreeDimensionalTubeSlab OriginalThreeDimensionalTubeParameters
open OriginalThreeDimensionalTubeCells

/-- The actual global-cube-injective shade has its true one-dimensional
local count inside any axial interval of length at least rho. -/
theorem original_shade_interval_count (Q : Finset Point3) (z : Pair3) (i : Fin 3)
    (rho t0 L : ℝ) (hrho : 0<rho) (hL : rho≤L)
    (hne : z.2 i-z.1 i≠0) (hmax : ∀ j, |z.2 j-z.1 j|≤|z.2 i-z.1 i|)
    (hinj : Set.InjOn (cell rho) Q)
    (htube : ∀ x∈Q, x∈physicalTube3 z.1 z.2 (4*rho))
    (hinterval : ∀ x∈Q, t0≤x i ∧ x i≤t0+L) :
    (Q.card : ℝ)*rho≤1200*L := by
  let a : Fin 2→ℝ := fun j => slope z i (i.succAbove j)
  let b : Fin 2→ℝ := fun j => offset z i (i.succAbove j)
  have hc := GraphTubeGridCover.occupied_cells_bound Q (GraphTubeGridCover.chart i)
    rho t0 L 8 a b hrho hL
    (fun j => original_slope_bound z i hne hmax (i.succAbove j))
    (fun x hx => hinterval x hx)
    (fun x hx j => by
      have hh := original_tube_graph_residual z i x (4*rho) hne hmax (htube x hx) (i.succAbove j)
      change |x (i.succAbove j)-offset z i (i.succAbove j)-slope z i (i.succAbove j)*x i|≤8*rho
      have he : x (i.succAbove j)-offset z i (i.succAbove j)-slope z i (i.succAbove j)*x i=
          x (i.succAbove j)-(slope z i (i.succAbove j)*x i+offset z i (i.succAbove j)) := by ring
      rw [he]
      linarith only [hh])
  have heq : Q.image (fun x => GraphTubeGridCover.gridBin rho (GraphTubeGridCover.chart i x))=
      (Q.image (cell rho)).image (GraphTubeGridCover.integerChart i) := by
    rw [Finset.image_image]
    rfl
  rw [heq,Finset.card_image_of_injective _ (GraphTubeGridCover.integerChart_injective i),
    Finset.card_image_of_injOn hinj] at hc
  norm_num at hc
  exact hc

/-- A short ball in an actual tube shade has a derived linear population
bound. The center need not be on the tube. -/
theorem original_shade_ball_count (Q : Finset Point3) (z : Pair3) (i : Fin 3)
    (rho a : ℝ) (hrho : 0<rho) (ha : rho≤a)
    (hne : z.2 i-z.1 i≠0) (hmax : ∀ j, |z.2 j-z.1 j|≤|z.2 i-z.1 i|)
    (hinj : Set.InjOn (cell rho) Q)
    (htube : ∀ x∈Q, x∈physicalTube3 z.1 z.2 (4*rho)) (c : Point3) :
    ((Q.filter (fun x => distance3 c x≤a)).card : ℝ)*rho≤2400*a := by
  let B := Q.filter (fun x => distance3 c x≤a)
  have hBQ : B⊆Q := Finset.filter_subset _ _
  have hb := original_shade_interval_count B z i rho (c i-a) (2*a) hrho
    (by linarith only [ha,hrho]) hne hmax (hinj.mono hBQ)
    (fun x hx => htube x (hBQ hx)) (by
      intro x hx
      have he := (original_coordinate_le_distance c x i).trans (Finset.mem_filter.mp hx).2
      have he' : |x i-c i|≤a := by simpa only [abs_sub_comm] using he
      exact ⟨by linarith only [(abs_le.mp he').1],by linarith only [(abs_le.mp he').2]⟩)
  dsimp [B] at hb
  linarith only [hb]

def farPairs (Q : Finset Point3) (a : ℝ) : Finset Pair3 :=
  (Q.product Q).filter (fun z => a≤distance3 z.1 z.2)

/-- A rich actual tube shade has quadratically many separated original
shade pairs. This derives the two-ends count from its actual cube geometry. -/
theorem original_shade_far_pairs (Q : Finset Point3) (z : Pair3) (i : Fin 3)
    (rho b : ℝ) (hrho : 0<rho) (hb : 0<b) (hsmall : rho≤b/4800)
    (hne : z.2 i-z.1 i≠0) (hmax : ∀ j, |z.2 j-z.1 j|≤|z.2 i-z.1 i|)
    (hinj : Set.InjOn (cell rho) Q)
    (htube : ∀ x∈Q, x∈physicalTube3 z.1 z.2 (4*rho))
    (hmass : b≤rho*Q.card) :
    b^2≤2*rho^2*(farPairs Q (b/4800)).card := by
  let a := b/4800
  have hnear (x : Point3) : ((Q.filter (fun y => distance3 x y<a)).card : ℝ)≤Q.card/2 := by
    have hsub : Q.filter (fun y => distance3 x y<a)⊆Q.filter (fun y => distance3 x y≤a) := by
      intro y hy
      obtain ⟨hyQ,hy⟩ := Finset.mem_filter.mp hy
      exact Finset.mem_filter.mpr ⟨hyQ,hy.le⟩
    have hc := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Finset.card_le_card hsub)) hrho.le
    have hh := original_shade_ball_count Q z i rho a hrho hsmall hne hmax hinj htube x
    apply (mul_le_mul_iff_of_pos_right hrho).mp
    dsimp [a] at hh
    nlinarith only [hc,hh,hmass]
  let B := (Q.product Q).filter (fun z => ¬a≤distance3 z.1 z.2)
  have hsum : B.card=∑ x∈Q,(Q.filter (fun y => distance3 x y<a)).card := by
    simp only [B,not_le,Finset.card_eq_sum_ones,Finset.sum_filter,
      Finset.product_eq_sprod,Finset.sum_product]
  have hB : (B.card : ℝ)≤(Q.card : ℝ)^2/2 := by
    have hs : (B.card : ℝ)=∑ x∈Q,((Q.filter (fun y => distance3 x y<a)).card : ℝ) := by exact_mod_cast hsum
    rw [hs]
    calc
      _ ≤ ∑ _x∈Q, (Q.card : ℝ)/2 := Finset.sum_le_sum (fun x _hx => hnear x)
      _ = _ := by simp; ring
  have hpart := Finset.card_filter_add_card_filter_not (s:=Q.product Q)
    (fun z => a≤distance3 z.1 z.2)
  have hpartR : ((farPairs Q a).card : ℝ)+B.card=(Q.card : ℝ)^2 := by
    simpa only [farPairs,B,Finset.product_eq_sprod,Finset.card_product,Nat.cast_mul,pow_two] using
      (show (((Q.product Q).filter (fun z => a≤distance3 z.1 z.2)).card : ℝ)+
        (((Q.product Q).filter (fun z => ¬a≤distance3 z.1 z.2)).card : ℝ)=
          ((Q.product Q).card : ℝ) by exact_mod_cast hpart)
  have hfar : (Q.card : ℝ)^2≤2*(farPairs Q a).card := by linarith only [hB,hpartR]
  have hs := pow_le_pow_left₀ hb.le hmass 2
  have hm := mul_le_mul_of_nonneg_left hfar (sq_nonneg rho)
  dsimp [a] at hm
  nlinarith only [hs,hm]

end OriginalThreeDimensionalShadeLocalCount
