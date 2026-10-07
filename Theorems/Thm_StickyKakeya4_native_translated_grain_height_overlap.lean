import Theorems.Thm_StickyKakeya4_native_weighted_grain_quotient_density
import Theorems.Thm_StickyKakeya4_native_phase_height_population

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 10000000
noncomputable section
namespace NativeTranslatedGrainHeightOverlap
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeSpatialAngularGeometry
open NativeOriginalCellChartGeometry NativeOriginalParentSelection NativePhaseHeightPopulation
open NativeAnisotropicShortRowGeometry

/-- The two original-center height partitions differ by one floor carry. -/
lemma floor_shift_carry (x s R : ℝ) :
    ⌊s/R⌋ ≤ ⌊x/R⌋-⌊(x-s)/R⌋ ∧ ⌊x/R⌋-⌊(x-s)/R⌋ ≤ ⌊s/R⌋+1 := by
  have he : (x-s)/R+s/R=x/R := by ring
  have hlo := Int.le_floor_add ((x-s)/R) (s/R)
  have hhi := Int.le_floor_add_floor ((x-s)/R) (s/R)
  rw [he] at hlo hhi
  omega

lemma two_integer_card (z : ℤ) : (Icc z (z+1)).card=2 := by
  have hh : ((Icc z (z+1)).card:ℤ)=2 := by rw [Int.card_Icc_of_le _ _ (by omega)]; omega
  exact_mod_cast hh

/-- A raw cell meets at most two translated cells, for the SAME points. -/
theorem raw_cell_translated_card {A : Type*} (S : Finset A) (x : A → ℝ)
    (s R : ℝ) (u : ℤ) (hraw : ∀z∈S,⌊x z/R⌋=u) :
    (S.image (fun z => ⌊(x z-s)/R⌋)).card ≤ 2 := by
  let k := ⌊s/R⌋
  have hsub : S.image (fun z => ⌊(x z-s)/R⌋)⊆Icc (u-k-1) ((u-k-1)+1) := by
    intro t ht
    obtain ⟨z,hz,rfl⟩ := mem_image.mp ht
    have hh := floor_shift_carry (x z) s R
    rw [hraw z hz] at hh
    apply mem_Icc.mpr
    dsimp [k]
    omega
  exact (card_le_card hsub).trans_eq (two_integer_card _)

/-- A translated cell meets at most two raw cells, for the SAME points. -/
theorem translated_cell_raw_card {A : Type*} (S : Finset A) (x : A → ℝ)
    (s R : ℝ) (t : ℤ) (htrans : ∀z∈S,⌊(x z-s)/R⌋=t) :
    (S.image (fun z => ⌊x z/R⌋)).card ≤ 2 := by
  let k := ⌊s/R⌋
  have hsub : S.image (fun z => ⌊x z/R⌋)⊆Icc (t+k) ((t+k)+1) := by
    intro u hu
    obtain ⟨z,hz,rfl⟩ := mem_image.mp hu
    have hh := floor_shift_carry (x z) s R
    rw [htrans z hz] at hh
    apply mem_Icc.mpr
    dsimp [k]
    omega
  exact (card_le_card hsub).trans_eq (two_integer_card _)

/-- This label uses the ORIGINAL microcell center, not a raw phase center. -/
def rawHeight {n : ℕ} (D : FiniteScaleSource n) (m : ℕ) (k : Index) : ℤ :=
  spatialLabel D (2^m) k (3:Fin 4)

/-- The actual translated reference-height label. -/
def translatedHeight {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m : ℕ) (k : Index) : ℤ :=
  heightLabel D a (64/((2^m:ℕ):ℝ)) k

lemma rawHeight_readback {n : ℕ} (D : FiniteScaleSource n) (m : ℕ) (k : Index) :
    rawHeight D m k=⌊cellCenter (mesh D) k (3:Fin 4)/(64/((2^m:ℕ):ℝ))⌋ := rfl

lemma translatedHeight_readback {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m : ℕ) (k : Index) :
    translatedHeight D a m k=
      ⌊(cellCenter (mesh D) k (3:Fin 4)-(shift D a:ℝ)*mesh D)/(64/((2^m:ℕ):ℝ))⌋ := by
  unfold translatedHeight heightLabel cellCenter
  congr 1
  push_cast
  ring

/-- Exact column-label height readback at arbitrary horizontal width. -/
lemma translatedHeight_column {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m N : ℕ)
    (p : Parent) (sigma : ℝ) (k : Index) :
    translatedHeight D a m k=columnLabel D a N p sigma (64/((2^m:ℕ):ℝ)) k (3:Fin 4) :=
  (column_height_readback D a N p sigma (64/((2^m:ℕ):ℝ)) k).symm

lemma actual_raw_cell_card {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m : ℕ)
    (S : Finset (Fin n × Index)) (u : ℤ) (hraw : ∀z∈S,rawHeight D m z.2=u) :
    (S.image (fun z => translatedHeight D a m z.2)).card ≤ 2 := by
  simpa only [translatedHeight_readback] using raw_cell_translated_card S
    (fun z => cellCenter (mesh D) z.2 (3:Fin 4)) ((shift D a:ℝ)*mesh D)
    (64/((2^m:ℕ):ℝ)) u hraw

lemma actual_translated_cell_card {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m : ℕ)
    (S : Finset (Fin n × Index)) (t : ℤ) (htrans : ∀z∈S,translatedHeight D a m z.2=t) :
    (S.image (fun z => rawHeight D m z.2)).card ≤ 2 := by
  have hh : ∀z∈S,⌊(cellCenter (mesh D) z.2 (3:Fin 4)-(shift D a:ℝ)*mesh D)/(64/((2^m:ℕ):ℝ))⌋=t := by
    intro z hz
    simpa only [translatedHeight_readback] using htrans z hz
  simpa only [rawHeight_readback] using translated_cell_raw_card S
    (fun z => cellCenter (mesh D) z.2 (3:Fin 4)) ((shift D a:ℝ)*mesh D)
    (64/((2^m:ℕ):ℝ)) t hh

/-- Distances between the two integer alphabets are compared, not identified. -/
lemma floor_shift_distance (x y s R : ℝ) :
    |(⌊x/R⌋:ℝ)-⌊y/R⌋| ≤ |(⌊(x-s)/R⌋:ℝ)-⌊(y-s)/R⌋|+2 := by
  have hx := floor_shift_carry x s R
  have hy := floor_shift_carry y s R
  have hdiff : (-1:ℤ) ≤ (⌊x/R⌋-⌊y/R⌋)-(⌊(x-s)/R⌋-⌊(y-s)/R⌋) ∧
      (⌊x/R⌋-⌊y/R⌋)-(⌊(x-s)/R⌋-⌊(y-s)/R⌋) ≤ 1 := by omega
  have hdiffR : |((⌊x/R⌋:ℝ)-⌊y/R⌋)-((⌊(x-s)/R⌋:ℝ)-⌊(y-s)/R⌋)| ≤ 1 := by
    apply abs_le.mpr
    exact_mod_cast hdiff
  have ht := abs_sub_le ((⌊x/R⌋:ℝ)-⌊y/R⌋) ((⌊(x-s)/R⌋:ℝ)-⌊(y-s)/R⌋) 0
  simp only [sub_zero] at ht
  linarith

lemma actual_height_distance {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m : ℕ) (k l : Index) :
    |(rawHeight D m k:ℝ)-rawHeight D m l| ≤
      |(translatedHeight D a m k:ℝ)-translatedHeight D a m l|+2 := by
  rw [rawHeight_readback,rawHeight_readback,translatedHeight_readback,translatedHeight_readback]
  exact floor_shift_distance _ _ _ _

/-- Distinct actual integer heights turn the additive discrepancy into the
fixed multiplicative metric cost3. -/
lemma actual_height_metric {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m : ℕ) (k l : Index)
    (hne : translatedHeight D a m k≠translatedHeight D a m l) :
    |(rawHeight D m k:ℝ)-rawHeight D m l| ≤
      3*|(translatedHeight D a m k:ℝ)-translatedHeight D a m l| := by
  have hi : (1:ℝ) ≤ |(translatedHeight D a m k:ℝ)-translatedHeight D a m l| := by
    have hh : (1:ℤ) ≤ |translatedHeight D a m k-translatedHeight D a m l| := by
      have hn : translatedHeight D a m k-translatedHeight D a m l≠0 := sub_ne_zero.mpr hne
      exact Int.one_le_abs hn
    exact_mod_cast hh
  have hh := actual_height_distance D a m k l
  linarith

end NativeTranslatedGrainHeightOverlap
