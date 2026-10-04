import Theorems.Thm_StickyKakeya4_native_local_parent_cells
import Theorems.Thm_StickyKakeya4_native_padded_cell_fiber_count
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2500000
noncomputable section
namespace NativeLocalParentCapacity
open Classical Finset MeasureTheory StickyKakeya4 NativeOriginalParentSelection NativeCommonCubicalMesh
open NativePaddedCellFiberCount NativeLocalParentCells
open scoped BigOperators ENNReal

/-- The actual local cell image has at most8N original time rows, with the
proved21952 original per-tube occupancy in each row. -/
theorem output_cell_fiber_card_le {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i) ∈ Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (N : ℕ) (hN : 0 < N) (p : Parent) (i : Fin n) (q : Index) :
    ((original i).filter (fun k => cellLabel D a N p i k=q)).card ≤ 175616*N := by
  let S := (original i).filter (fun k => cellLabel D a N p i k=q)
  let b : ℤ := 8*(N:ℤ)
  let rs := Icc (b*q (3:Fin 4)) (b*q (3:Fin 4)+b-1)
  have hb : 0 < b := by dsimp [b]; positivity
  have hm : ∀k∈S,k (3:Fin 4)-shift D a∈rs := by
    intro k hk
    have he := congrFun (mem_filter.mp hk).2 (3:Fin 4)
    rw [cellLabel_height h.1.2.1 a N hN] at he
    have he' : (k (3:Fin 4)-shift D a)/b=q (3:Fin 4) := by
      simpa only [b,Nat.cast_mul,Nat.cast_ofNat] using he
    apply mem_Icc.mpr
    have hlo := (Int.le_ediv_iff_mul_le hb).mp he'.ge
    have hhi := (Int.ediv_lt_iff_lt_mul hb).mp (show (k (3:Fin 4)-shift D a)/b<q (3:Fin 4)+1 by omega)
    constructor <;> nlinarith
  have hc : ∀r∈rs,(S.filter (fun k => k (3:Fin 4)-shift D a=r)).card ≤ 21952 := by
    intro r _hr
    exact (card_le_card (filter_subset_filter _ (filter_subset _ _))).trans
      (original_row_card_le h original horiginal ha i r)
  have H := card_le_mul_card_image_of_maps_to hm 21952 hc
  have hrs : rs.card=8*N := by
    have hh : (rs.card:ℤ)=8*(N:ℤ) := by
      dsimp [rs]
      rw [Int.card_Icc_of_le _ _ (by nlinarith)]
      dsimp [b] at *
      omega
    exact_mod_cast hh
  rw [hrs] at H
  simpa only [←Nat.mul_assoc,show 21952*8=175616 by norm_num] using H

lemma original_card_le_output_card {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (N : ℕ) (hN : 0 < N) (p : Parent) (i : Fin n) :
    (original i).card ≤ (175616*N)*(cells D original a N p i).card := by
  exact card_le_mul_card_image (original i) (175616*N)
    (fun q _ => output_cell_fiber_card_le h original horiginal ha N hN p i q)

/-- Actual local cubical shading mass has the correct N^3 volume factor.
This is a per-tube upper capacity statement, with no per-tube density premise. -/
theorem shading_mass_scale {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (N : ℕ) (hN : 0 < N) (p : Parent) (i : Fin n) :
    (N:ℝ)^3*(volume (D.shading i)).toReal ≤ (175616*64^4:ℝ)*
      (volume (wzCellShading ((N:ℝ)*D.thickness/128) (cells D original a N p) i)).toReal := by
  have hd:=h.1.2.1
  have hm : 0 < mesh D := half_pos hd
  have he : 0 < (N:ℝ)*D.thickness/128 := by positivity
  have hc : ((original i).card:ℝ) ≤ (175616*(N:ℝ))*(cells D original a N p i).card := by
    exact_mod_cast original_card_le_output_card h original horiginal ha N hN p i
  rw [horiginal i,volume_wzCellShading hm,volume_wzCellShading he]
  simp only [ENNReal.toReal_mul,ENNReal.toReal_natCast,ENNReal.toReal_pow,
    ENNReal.toReal_ofReal hm.le,ENNReal.toReal_ofReal he.le]
  calc
    _ ≤ (N:ℝ)^3*((175616*(N:ℝ))*(cells D original a N p i).card*(mesh D)^4) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hc (by positivity)) (by positivity)
    _ = _ := by dsimp [mesh]; ring
end NativeLocalParentCapacity
