import Theorems.Thm_StickyKakeya4_native_rank_one_slope_cap
import Theorems.Thm_StickyKakeya4_native_point_angular_parent_fibers
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000
noncomputable section

namespace NativeRankOneParentCap
open Classical Finset StickyKakeya4 NativeDirectionRankDichotomy NativeRankOneSlopeCap
open NativeOriginalCellChartGeometry NativeOriginalParentSelection NativeCommonCubicalMesh
open NativeCubicalIncidenceCounts NativePointAngularParentFibers
open scoped BigOperators

/-- The neighboring angular cells around one genuine retained parent label. -/
def angularMenu (q : Fin 3 → ℤ) : Finset (Fin 3 → ℤ) :=
  Fintype.piFinset (fun j => Icc (q j - 1) (q j + 1))

lemma angularMenu_card (q : Fin 3 → ℤ) : (angularMenu q).card = 27 := by
  have hi (j : Fin 3) : (Icc (q j - 1) (q j + 1)).card = 3 := by
    have hh : ((Icc (q j - 1) (q j + 1)).card : ℤ) = 3 := by
      rw [Int.card_Icc_of_le _ _ (by omega)]
      omega
    exact_mod_cast hh
  norm_num only [angularMenu, Fintype.card_piFinset, hi, prod_const, card_univ,
    Fintype.card_fin]

/-- Rank-one concentration on actual retained edges supplies an actual anchor
and a 27-element angular menu whenever `48Nr ≤ 1`. -/
theorem actual_near_angular_menu {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (A : Finset (Fin n × Index))
    (P : Submodule ℝ E4) (hP : Module.finrank ℝ P ≤ 1) (r : ℝ)
    (hr : 0 < r) (hrsmall : r ≤ 1 / 4) (a : ℝ) (N : ℕ)
    (hNr : 48 * (N : ℝ) * r ≤ 1)
    (hne : (nearLabels A (fun z => slopeVector D z.1) r P).Nonempty) :
    ∃ z ∈ nearLabels A (fun z => slopeVector D z.1) r P,
      ∀ w ∈ nearLabels A (fun z => slopeVector D z.1) r P,
        (parentLabel D a N w.1).1 ∈ angularMenu ((parentLabel D a N z.1).1) := by
  obtain ⟨z, hz, hcap⟩ := near_labels_cap A (fun z => slopeVector D z.1) P hP 2 r hr hrsmall
    (fun z _hz => slopeVector_last D z.1) (fun z _hz => slopeVector_norm_le_two h z.1) hne
  refine ⟨z, hz, ?_⟩
  intro w hw
  have hcap' : ‖slopeVector D w.1 - slopeVector D z.1‖ ≤ 48 * r := by
    convert hcap w hw using 1
    norm_num
  apply Fintype.mem_piFinset.mpr
  intro j
  have hcoord : |slope (D.line w.1) j - slope (D.line z.1) j| ≤ 48 * r := by
    simpa only [PiLp.sub_apply, slopeVector, ActualSlopeSource.heightPoint_castSucc] using
      (coordinate_abs_le_norm (slopeVector D w.1 - slopeVector D z.1) j.castSucc).trans hcap'
  have hs : |(N : ℝ) * slope (D.line w.1) j - (N : ℝ) * slope (D.line z.1) j| ≤ 1 := by
    calc
      _ = (N : ℝ) * |slope (D.line w.1) j - slope (D.line z.1) j| := by
        rw [← mul_sub, abs_mul, abs_of_nonneg (Nat.cast_nonneg N)]
      _ ≤ (N : ℝ) * (48 * r) := mul_le_mul_of_nonneg_left hcoord (Nat.cast_nonneg N)
      _ ≤ 1 := by nlinarith only [hNr]
  have hlo := Int.floor_mono
    (show (N : ℝ) * slope (D.line z.1) j - 1 ≤ (N : ℝ) * slope (D.line w.1) j by
      linarith [(abs_le.mp hs).1])
  have hhi := Int.floor_mono
    (show (N : ℝ) * slope (D.line w.1) j ≤ (N : ℝ) * slope (D.line z.1) j + 1 by
      linarith [(abs_le.mp hs).2])
  rw [Int.floor_sub_one] at hlo
  rw [Int.floor_add_one] at hhi
  exact mem_Icc.mpr ⟨hlo, hhi⟩

/-- At one actual old cell, a rank-one concentration meets at most 9261
original full parameter parents. The count combines the proved 27 angular
cells with the original physical incidence bound of 343 intercept cells. -/
theorem actual_near_parent_card_le {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀ i, D.shading i = wzCellShading (mesh D) original i)
    (ha : ∀ i, wzGraphTime (D.line i) a - mark (D.line i) ∈
      Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ))
    (E : Finset (Fin n × Index)) (hE : E ⊆ incidences original) (k : Index)
    (P : Submodule ℝ E4) (hP : Module.finrank ℝ P ≤ 1) (r : ℝ)
    (hr : 0 < r) (hrsmall : r ≤ 1 / 4) (N : ℕ)
    (hNr : 48 * (N : ℝ) * r ≤ 1) (hscale : (N : ℝ) * D.thickness ≤ 1) :
    ((nearLabels (E.filter (fun z => z.2 = k)) (fun z => slopeVector D z.1) r P).image
      (fun z => parentLabel D a N z.1)).card ≤ 9261 := by
  let A := nearLabels (E.filter (fun z => z.2 = k)) (fun z => slopeVector D z.1) r P
  change (A.image (fun z => parentLabel D a N z.1)).card ≤ 9261
  by_cases hne : A.Nonempty
  · obtain ⟨z, _hz, hmenu⟩ := actual_near_angular_menu h (E.filter (fun z => z.2 = k))
      P hP r hr hrsmall a N hNr hne
    have hfilter : A.filter (fun z => z.2 = k) = A := by
      apply filter_eq_self.mpr
      intro z hz
      exact (mem_filter.mp (mem_filter.mp hz).1).2
    have hAE : A ⊆ incidences original := by
      intro z hz
      exact hE (mem_filter.mp (mem_filter.mp hz).1).1
    have hangular : (pointAngular D a N A k).card ≤ 27 := by
      calc
        _ ≤ (angularMenu ((parentLabel D a N z.1).1)).card := by
          apply card_le_card
          rw [pointAngular_readback, hfilter]
          intro q hq
          obtain ⟨w, hw, rfl⟩ := mem_image.mp hq
          exact hmenu w hw
        _ = 27 := angularMenu_card _
    calc
      _ ≤ 343 * (pointAngular D a N A k).card := by
        simpa only [pointParents, hfilter] using
          pointParents_card_le_angular h original horiginal ha N hscale A hAE k
      _ ≤ 343 * 27 := Nat.mul_le_mul_left 343 hangular
      _ = 9261 := by norm_num
  · have hempty : A = ∅ := not_nonempty_iff_eq_empty.mp hne
    simp only [hempty, image_empty, card_empty, zero_le]

end NativeRankOneParentCap
