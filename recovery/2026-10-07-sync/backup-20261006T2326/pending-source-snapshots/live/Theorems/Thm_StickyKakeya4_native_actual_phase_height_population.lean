/- UNVERIFIED source-derived full phase support on the same E1 reference. -/
import Theorems.Thm_StickyKakeya4_native_actual_relative_coarse_admission
import Theorems.Thm_StickyKakeya4_native_coarse_pruning_budget
import Theorems.Thm_StickyKakeya4_native_middle_window_balance

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 2200000
noncomputable section
namespace NativeActualPhaseHeightPopulation
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeLocalParentSource NativeActualRelativeCoarseAdmission NativeCoarsePruningBudget

/-- Full occupied phase count is derived from original HB populations and
the same admitted E1-parent source. The selected shading is irrelevant. -/
theorem actual_full_phase_card {n : ℕ} {D : FiniteScaleSource n} {eta localEta a zeta profile : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (Rfull : Finset (Fin n)) (level : ℕ) (hzeta : 0 ≤ zeta)
    (HB : NativeMiddleWindowBalance.HasOriginalBackbone D original Rfull a level zeta)
    (Eref : Finset (Fin n × Index)) (m c : ℕ) (hm : m ≤ level) (hc : c ≤ level-m+6) (p : Parent)
    (href : IsWangZakharovNativeFiniteInput (source h Rfull Eref a m p) localEta)
    (hbudget : (64:ℝ)^3*(source h Rfull Eref a m p).thickness^profile ≤ D.thickness^zeta) :
    let Sref := source h Rfull Eref a m p
    (((univ : Finset (Fin (parentLabels D Rfull a (2^m) p).card)).image
      (parentLabel Sref 0 (2^c))).card:ℝ) ≤
        373248*Sref.thickness^(-profile)*(((2^c:ℕ):ℝ))^3 := by
  intro Sref
  obtain ⟨_horiginal,hdy,_ha,_hR,_hcard,_hshade,_hden,_hCW,Hpop⟩ := HB
  have Hlocal := source_population_law h Rfull Eref a zeta profile hzeta level hdy Hpop m hm p href hbudget
  exact original_occupied_count href univ (2^c) (by positivity)
    (fun q hq => (Hlocal ⟨c,by omega⟩ q hq).1)

/-- Every current old relative phase is literally an occupied phase of
that same reference source; no active tube count is replaced by the full one. -/
theorem relative_parent_mem_full {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (Rfull : Finset (Fin n))
    (Eref : Finset (Fin n × Index)) (a : ℝ) (m c : ℕ) (p : Parent)
    (i : Fin n) (hi : i∈parentLabels D Rfull a (2^m) p) :
    NativeRelativeParentLabels.relativeLabel D a (2^m) p (2^c) i∈
      (univ : Finset (Fin (parentLabels D Rfull a (2^m) p).card)).image
        (parentLabel (source h Rfull Eref a m p) 0 (2^c)) := by
  have hrange : i∈Set.range (NativePaddedCellSource.originalLabel (parentLabels D Rfull a (2^m) p)) := by
    rw [NativePaddedCellSource.originalLabel_range]
    exact hi
  obtain ⟨j,rfl⟩ := hrange
  exact mem_image.mpr ⟨j,mem_univ j,NativeRelativeParentProfiles.source_parentLabel h Rfull Eref a m p (2^c) j⟩

end NativeActualPhaseHeightPopulation
