/- UNVERIFIED draft after the 2026-10-06 10:03 reset.
Counts actual full-reference phase parents through their original slope grid. -/
import Theorems.Thm_StickyKakeya4_native_reference_angular_parent_cap
import Theorems.Thm_StickyKakeya4_native_normalized_cell_angular_menu
import Theorems.Thm_StickyKakeya4_canonical_grid_recoding

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 2500000
noncomputable section
namespace NativeActualAngularParentCount
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeOriginalCellChartGeometry NativeCoarseDirectionThinning NativeCoarseRepresentativeGeometry
open NativeFullReferenceSlopeCap NativeLocalParentSource NativeLocalParentGeometry
open NativeReferenceAngularParentCap
open scoped BigOperators

/-- The analytic angular query is eight times finer than the prepared
base support cell. Its physical labels have exact integer ancestry. -/
theorem physicalCell_coarsen_eight {n : ℕ} (D : FiniteScaleSource n)
    (a : ℝ) (N M : ℕ) (hM : 0 < M) (p : Parent) (k : Index) (j : Fin 4) :
    NativeNormalizedCellRelativeMenu.physicalCell D a N (8*M) p k j / 8 =
      NativeNormalizedCellRelativeMenu.physicalCell D a N M p k j := by
  let x := NativeNormalizedCellRelativeMenu.physicalPoint D a N p k j
  have hMr : (M : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hM)
  have he : x / (64 / (M : ℝ)) = (x / (64 / ((8*M : ℕ) : ℝ))) / 8 := by
    push_cast
    field_simp [hMr]
  change ⌊x / (64 / ((8*M : ℕ) : ℝ))⌋ / 8 = ⌊x / (64 / (M : ℝ))⌋
  rw [he]
  have hh := Int.floor_div_natCast (x / (64 / ((8*M : ℕ) : ℝ))) 8
  norm_num only [Nat.cast_ofNat] at hh
  exact hh.symm

/-- All old preimages of a configured point lying in one prepared base
cell occupy at most8^4 cells at the actual finer angular-query radius.
This is a cover of the original indices and makes no further selection. -/
theorem physicalCell_refinement_card {n : ℕ} (D : FiniteScaleSource n)
    (a : ℝ) (N M : ℕ) (hM : 0 < M) (p : Parent)
    (I : Finset Index) (q : Index)
    (hq : ∀ k ∈ I, NativeNormalizedCellRelativeMenu.physicalCell D a N M p k = q) :
    (I.image (NativeNormalizedCellRelativeMenu.physicalCell D a N (8*M) p)).card ≤ 8^4 := by
  calc
    _ ≤ (CanonicalGridRecoding.preimageBox 8 q).card := by
      apply card_le_card
      intro z hz
      obtain ⟨k, hk, rfl⟩ := mem_image.mp hz
      apply CanonicalGridRecoding.mem_preimageBox 8 (by norm_num)
      intro j
      norm_num only [Nat.cast_ofNat]
      rw [physicalCell_coarsen_eight D a N M hM p k j, hq k hk]
    _ = _ := CanonicalGridRecoding.preimageBox_card 8 q

/-- Exact old-angular label readback at final phase depth u+12. The packet
query is u+9, since its angular mesh is one eighth of its spatial radius. -/
theorem source_cell_readback {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (Eref : Finset (Fin n × Index)) (a : ℝ) (m u : ℕ) (p : Parent)
    (i : Fin (parentLabels D R a (2^m) p).card) :
    slopeCell (source h R Eref a m p) (2^(u+12)) i =
      NativeNormalizedCellAngularMenu.angularCell D (2^m) (2^(u+9)) p
        (NativePaddedCellSource.originalLabel (parentLabels D R a (2^m) p) i) := by
  ext j
  simp only [slopeCell, NativeNormalizedCellAngularMenu.angularCell, source_line, slope_line]
  congr 1
  have hpow : ((2^(u+12):ℕ):ℝ) = 8 * ((2^(u+9):ℕ):ℝ) := by
    rw [show u+12=(u+9)+3 by omega, pow_add]
    push_cast
    ring
  rw [hpow]
  have hM : (((2^(u+9):ℕ):ℝ)) ≠ 0 := by positivity
  field_simp [hM]
  ring

/-- The final form is on unchanged original tube indices and the exact
relative phase key used by geometricPairKey. It consumes the same E1-parent
admission and derives all representative populations from the same HB. -/
theorem same_original_parent_count {n : ℕ} {D : FiniteScaleSource n}
    {eta localEta a zeta e : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta)
    (original : Fin n → Finset Index) (R : Finset (Fin n)) (level : ℕ)
    (HB : NativeMiddleWindowBalance.HasOriginalBackbone D original R a level zeta)
    (Eref : Finset (Fin n × Index)) (m u : ℕ) (hmb : m + (u+12) ≤ level) (p : Parent)
    (hReferenceNative : IsWangZakharovNativeFiniteInput (source h R Eref a m p) localEta)
    (hbudget : (64 : ℝ)^3 * (source h R Eref a m p).thickness ^ e ≤ D.thickness ^ zeta)
    (I : Finset (Fin n)) (hI : I ⊆ parentLabels D R a (2^m) p) :
    ((I.image (NativeRelativeParentLabels.relativeLabel D a (2^m) p (2^(u+12)))).card : ℝ) ≤
      ((5832 * 130 ^ 3 : ℝ) * (source h R Eref a m p).thickness ^ (-e)) *
        (I.image (NativeNormalizedCellAngularMenu.angularCell D (2^m) (2^(u+9)) p)).card := by
  let S := source h R Eref a m p
  let old := NativePaddedCellSource.originalLabel (parentLabels D R a (2^m) p)
  let A := (univ : Finset (Fin (parentLabels D R a (2^m) p).card)).filter (fun i => old i ∈ I)
  have hAI : A.image old = I := by
    ext i
    constructor
    · rintro hi
      obtain ⟨j, hj, rfl⟩ := mem_image.mp hi
      exact (mem_filter.mp hj).2
    · intro hi
      have hrange : i ∈ Set.range old := by
        dsimp only [old]
        rw [NativePaddedCellSource.originalLabel_range]
        exact hI hi
      obtain ⟨j, rfl⟩ := hrange
      exact mem_image.mpr ⟨j, mem_filter.mpr ⟨mem_univ j, hi⟩, rfl⟩
  have hparents : A.image (parentLabel S 0 (2^(u+12))) =
      I.image (NativeRelativeParentLabels.relativeLabel D a (2^m) p (2^(u+12))) := by
    rw [← hAI, image_image]
    apply image_congr
    intro i _hi
    exact NativeRelativeParentProfiles.source_parentLabel h R Eref a m p (2^(u+12)) i
  have hangles : A.image (slopeCell S (2^(u+12))) =
      I.image (NativeNormalizedCellAngularMenu.angularCell D (2^m) (2^(u+9)) p) := by
    rw [← hAI, image_image]
    apply image_congr
    intro i _hi
    exact source_cell_readback h R Eref a m u p i
  have hh := same_reference_phase_card h original R level HB Eref m (u+12) hmb p
    hReferenceNative hbudget A
  change ((A.image (parentLabel S 0 (2^(u+12)))).card : ℝ) ≤
    ((5832 * 130 ^ 3 : ℝ) * S.thickness ^ (-e)) * (A.image (slopeCell S (2^(u+12)))).card at hh
  rw [hparents, hangles] at hh
  exact hh

end NativeActualAngularParentCount
