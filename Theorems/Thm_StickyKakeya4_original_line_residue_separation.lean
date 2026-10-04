import Theorems.Thm_StickyKakeya4_original_clipped_tube_parameter_inverse
import Mathlib.Data.Int.ModEq

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2800000

noncomputable section
namespace OriginalLineResidueSeparation
open Classical OriginalPairStripGeometry OriginalUnitLineParameters OriginalUnitLineGrid
open OriginalClippedUnitTube OriginalClippedTubeParameterInverse

abbrev LineColor := Fin 4×LineCell

def lineColor (rho : ℝ) (M : ℕ) (z : Pair) : LineColor :=
  (normalChart z,(lineCell rho z).1%(M:ℤ),
    (lineCell rho z).2.1%(M:ℤ),(lineCell rho z).2.2%(M:ℤ))

def lineColors (M : ℕ) : Finset LineColor :=
  (Finset.univ : Finset (Fin 4)).product ((Finset.Ico (0:ℤ) M).product
    ((Finset.Ico (0:ℤ) M).product (Finset.Ico (0:ℤ) M)))

theorem line_colors_card (M : ℕ) : (lineColors M).card=4*M^3 := by
  simp only [lineColors,Finset.product_eq_sprod,Finset.card_product,
    Finset.card_univ,Fintype.card_fin,Int.card_Ico,sub_zero,Int.toNat_natCast]
  ring

theorem original_line_color_mem (rho : ℝ) (M : ℕ) (hM : 0<M) (z : Pair) :
    lineColor rho M z∈lineColors M := by
  have hm : 0<(M:ℤ) := by exact_mod_cast hM
  have hmem (a : ℤ) : a%(M:ℤ)∈Finset.Ico (0:ℤ) M :=
    Finset.mem_Ico.mpr ⟨Int.emod_nonneg _ hm.ne',Int.emod_lt_of_pos _ hm⟩
  exact Finset.mem_product.mpr ⟨Finset.mem_univ _,Finset.mem_product.mpr
    ⟨hmem _,Finset.mem_product.mpr ⟨hmem _,hmem _⟩⟩⟩

private theorem same_mod_small_difference (a b : ℤ) (M : ℕ) (hM : 0<M)
    (heq : a%(M:ℤ)=b%(M:ℤ)) (hlt : |a-b|<(M:ℤ)) : a=b := by
  have hm : 0<(M:ℤ) := by exact_mod_cast hM
  obtain ⟨k,hk⟩ := Int.modEq_iff_dvd.mp heq
  obtain ⟨hlo,hhi⟩ := abs_lt.mp hlt
  by_cases hk0 : k=0
  · simp only [hk0,mul_zero] at hk
    omega
  · have hkcases : k≤ -1 ∨ 1≤k := by omega
    rcases hkcases with hkn|hkp
    · have hmul := mul_le_mul_of_nonneg_left hkn hm.le
      nlinarith only [hk,hlo,hhi,hmul]
    · have hmul := mul_le_mul_of_nonneg_left hkp hm.le
      nlinarith only [hk,hlo,hhi,hmul]

private theorem same_residue_close_floor (x y rho : ℝ) (M : ℕ)
    (hrho : 0<rho) (hM : 0<M)
    (heq : ⌊x/rho⌋%(M:ℤ)=⌊y/rho⌋%(M:ℤ))
    (hclose : |x-y|<((M:ℝ)-1)*rho) : ⌊x/rho⌋=⌊y/rho⌋ := by
  have hd : |x/rho-y/rho|<(M:ℝ)-1 := by
    rw [← sub_div,abs_div,abs_of_pos hrho]
    exact (div_lt_iff₀ hrho).mpr hclose
  have hlo := Int.floor_le (x/rho)
  have hhi := Int.lt_floor_add_one (x/rho)
  have hylo := Int.floor_le (y/rho)
  have hyhi := Int.lt_floor_add_one (y/rho)
  obtain ⟨hdlo,hdhi⟩ := abs_lt.mp hd
  apply same_mod_small_difference _ _ M hM heq
  exact_mod_cast (show |(⌊x/rho⌋:ℝ)-(⌊y/rho⌋:ℝ)|<(M:ℝ) from
    abs_lt.mpr ⟨by linarith,by linarith⟩)

/-- A fixed residue color separates actual line parameters unless the
original fine cells are equal. -/
theorem original_same_color_close_cell
    (rho : ℝ) (M : ℕ) (z u : Pair) (hrho : 0<rho) (hM : 0<M)
    (heq : lineColor rho M z=lineColor rho M u)
    (hx : |unitX z-unitX u|<((M:ℝ)-1)*rho)
    (hy : |unitY z-unitY u|<((M:ℝ)-1)*rho)
    (hc : |unitOffset z-unitOffset u|<((M:ℝ)-1)*rho) :
    lineCell rho z=lineCell rho u := by
  apply Prod.ext
  · exact same_residue_close_floor _ _ rho M hrho hM
      (congrArg (fun c : LineColor => c.2.1) heq) hx
  · apply Prod.ext
    · exact same_residue_close_floor _ _ rho M hrho hM
        (congrArg (fun c : LineColor => c.2.2.1) heq) hy
    · exact same_residue_close_floor _ _ rho M hrho hM
        (congrArg (fun c : LineColor => c.2.2.2) heq) hc

/-- Distinct actual cells of one chart/color cannot have one clipped
physical rectangle contained in the other's doubled-width strip. -/
theorem original_same_color_clipped_distinct
    (rho w : ℝ) (M : ℕ) (z u : Pair)
    (hrho : 0<rho) (hw : 0≤w) (hM : 0<M)
    (hmesh : 36*w<((M:ℝ)-1)*rho)
    (hz : z.1≠z.2) (hu : u.1≠u.2)
    (hroot : |z.1.1|≤1 ∧ |z.1.2|≤1)
    (hcolor : lineColor rho M z=lineColor rho M u)
    (hcell : lineCell rho z≠lineCell rho u) :
    ∃ p∈clippedTube z w, 2*w< |scaledResidual u p| := by
  by_contra hh
  have hcontain : ∀ p∈clippedTube z w, |scaledResidual u p|≤2*w := by
    intro p hp
    by_contra hp'
    exact hh ⟨p,hp,lt_of_not_ge hp'⟩
  obtain ⟨hx,hy,hc⟩ := original_clipped_containment_parameter_close z u w hw hz hu hroot
    (congrArg (fun c : LineColor => c.1) hcolor) hcontain
  exact hcell (original_same_color_close_cell rho M z u hrho hM hcolor
    (by linarith only [hx,hw,hmesh]) (by linarith only [hy,hw,hmesh]) (hc.trans_lt hmesh))

end OriginalLineResidueSeparation
