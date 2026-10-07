/- UNVERIFIED draft after the 2026-10-06 10:03 reset.
Counts actual full-reference phase parents through their original slope grid. -/
import Theorems.Thm_StickyKakeya4_native_full_reference_slope_cap
import Theorems.Thm_StickyKakeya4_native_same_reference_chart_bounds
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
open scoped BigOperators

/-- This cell has the actual final tube width 64/N in all three full slopes. -/
def slopeCell {n : ℕ} (D : FiniteScaleSource n) (N : ℕ) (i : Fin n) : Fin 3 → ℤ :=
  fun j => ⌊slope (D.line i) j / (64 / (N : ℝ))⌋

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
    ring
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
      rw [physicalCell_coarsen_eight D a N M hM p k j, hq k hk]
    _ = _ := CanonicalGridRecoding.preimageBox_card 8 q

/-- One complete old angular cell can meet only a bounded number of
occupied phase parents, with the explicit fine-reference population loss.
The representative box is derived from its actual same-parent witness. -/
theorem single_cell {n : ℕ} {D : FiniteScaleSource n} {eta e : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (N : ℕ) (hN : 0 < N)
    (hscale : (N : ℝ) * D.thickness ≤ 1)
    (H : ∀ p : Parent,
      ((univ : Finset (Fin n)).filter (fun i => parentLabel D 0 N i = p)).Nonempty →
        D.thickness ^ e * ((1 / (N : ℝ)) / D.thickness) ^ 3 ≤
          (((univ : Finset (Fin n)).filter (fun i => parentLabel D 0 N i = p)).card : ℝ))
    (I : Finset (Fin n)) (q : Fin 3 → ℤ) (hq : ∀ i ∈ I, slopeCell D N i = q) :
    ((I.image (parentLabel D 0 N)).card : ℝ) ≤
      (5832 * 130 ^ 3 : ℝ) * D.thickness ^ (-e) := by
  let Q := I.image (parentLabel D 0 N)
  let delta : ℝ := 64 / (N : ℝ)
  let rep := representative h univ 0 N
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hd : 0 < delta := by dsimp only [delta]; positivity
  have hQ : Q ⊆ (univ : Finset (Fin n)).image (parentLabel D 0 N) :=
    image_subset_image (subset_univ I)
  have hrep (p : Parent) (hp : p ∈ Q) : parentLabel D 0 N (rep p) = p :=
    (representative_spec h univ 0 N (hQ hp)).2
  have hbox (p : Parent) (hp : p ∈ Q) (j : Fin 3) :
      (q j : ℝ) * delta - delta / 2 ≤ slope (D.line (rep p)) j ∧
      slope (D.line (rep p)) j ≤ ((q j : ℝ) * delta - delta / 2) + 2 * delta := by
    obtain ⟨i, hi, hip⟩ := mem_image.mp hp
    have he : parentLabel D 0 N i = parentLabel D 0 N (rep p) := hip.trans (hrep p hp).symm
    have hclose := NativeNormalizedParentCarrierMetric.same_floor_mul_close
      (slope (D.line i) j) (slope (D.line (rep p)) j) N hN
      (congrFun (congrArg Prod.fst he) j)
    have hang : ⌊slope (D.line i) j / delta⌋ = q j := congrFun (hq i hi) j
    have hlo := (le_div_iff₀ hd).mp (Int.floor_le (slope (D.line i) j / delta))
    have hhi := (div_lt_iff₀ hd).mp (Int.lt_floor_add_one (slope (D.line i) j / delta))
    rw [hang] at hlo hhi
    have hgap : 1 / (N : ℝ) ≤ delta / 2 := by
      dsimp only [delta]
      have hpos : 0 < 1 / (N : ℝ) := by positivity
      linarith
    obtain ⟨hc0, hc1⟩ := abs_le.mp hclose
    constructor <;> nlinarith only [hlo, hhi, hc0, hc1, hgap]
  have hh := representative_cube_card h univ N hN hscale H Q hQ rep hrep
    (show 0 ≤ 2 * delta by positivity) (fun j => (q j : ℝ) * delta - delta / 2) hbox
  have hside : (N : ℝ) * (2 * delta) + 2 = 130 := by
    dsimp only [delta]
    field_simp [hNr.ne']
    ring
  rw [hside] at hh
  nlinarith only [hh]

/-- Sum the genuine one-cell count over the old full angular union. No
choice of one original point or of one tube per angle is made. -/
theorem phase_card_le_angular_card {n : ℕ} {D : FiniteScaleSource n} {eta e : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (N : ℕ) (hN : 0 < N)
    (hscale : (N : ℝ) * D.thickness ≤ 1)
    (H : ∀ p : Parent,
      ((univ : Finset (Fin n)).filter (fun i => parentLabel D 0 N i = p)).Nonempty →
        D.thickness ^ e * ((1 / (N : ℝ)) / D.thickness) ^ 3 ≤
          (((univ : Finset (Fin n)).filter (fun i => parentLabel D 0 N i = p)).card : ℝ))
    (I : Finset (Fin n)) :
    ((I.image (parentLabel D 0 N)).card : ℝ) ≤
      ((5832 * 130 ^ 3 : ℝ) * D.thickness ^ (-e)) * (I.image (slopeCell D N)).card := by
  let angles := I.image (slopeCell D N)
  let parents := fun q => (I.filter (fun i => slopeCell D N i = q)).image (parentLabel D 0 N)
  have he : I.image (parentLabel D 0 N) = angles.biUnion parents := by
    ext p
    constructor
    · rintro hp
      obtain ⟨i, hi, rfl⟩ := mem_image.mp hp
      exact mem_biUnion.mpr ⟨slopeCell D N i, mem_image_of_mem _ hi,
        mem_image.mpr ⟨i, mem_filter.mpr ⟨hi, rfl⟩, rfl⟩⟩
    · rintro hp
      obtain ⟨q, _hq, hp⟩ := mem_biUnion.mp hp
      obtain ⟨i, hi, rfl⟩ := mem_image.mp hp
      exact mem_image_of_mem _ (mem_filter.mp hi).1
  calc
    _ = ((angles.biUnion parents).card : ℝ) := by rw [he]
    _ ≤ (∑ q ∈ angles, (parents q).card : ℕ) := by
      exact_mod_cast card_biUnion_le
    _ = ∑ q ∈ angles, ((parents q).card : ℝ) := by simp only [Nat.cast_sum]
    _ ≤ ∑ _q ∈ angles, (5832 * 130 ^ 3 : ℝ) * D.thickness ^ (-e) := by
      apply sum_le_sum
      intro q _hq
      exact single_cell h N hN hscale H (I.filter (fun i => slopeCell D N i = q)) q
        (fun i hi => (mem_filter.mp hi).2)
    _ = _ := by simp only [sum_const, nsmul_eq_mul, angles]; ring

/-- Same admitted E1-parent reader. Its entire population premise is
constructed from the original HB; the incidence set remains arbitrary. -/
theorem same_reference_phase_card {n : ℕ} {D : FiniteScaleSource n}
    {eta localEta a zeta e : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta)
    (original : Fin n → Finset Index) (R : Finset (Fin n)) (level : ℕ)
    (HB : NativeMiddleWindowBalance.HasOriginalBackbone D original R a level zeta)
    (Eref : Finset (Fin n × Index)) (m b : ℕ) (hmb : m + b ≤ level) (p : Parent)
    (hReferenceNative : IsWangZakharovNativeFiniteInput (source h R Eref a m p) localEta)
    (hbudget : (64 : ℝ)^3 * (source h R Eref a m p).thickness ^ e ≤ D.thickness ^ zeta)
    (I : Finset (Fin (parentLabels D R a (2^m) p).card)) :
    let S := source h R Eref a m p
    ((I.image (parentLabel S 0 (2^b))).card : ℝ) ≤
      ((5832 * 130 ^ 3 : ℝ) * S.thickness ^ (-e)) * (I.image (slopeCell S (2^b))).card := by
  intro S
  have hdy := HB.2.1
  have hscale := NativeSameReferenceChartBounds.source_scale_guard h R Eref level m b p hdy hmb
  have Hpop := NativeSameReferenceChartBounds.population_through h original R level HB Eref m b hmb p hbudget
  exact phase_card_le_angular_card hReferenceNative (2^b) (by positivity) hscale
    (fun q hq => (Hpop ⟨b, by omega⟩ q hq).1) I

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
