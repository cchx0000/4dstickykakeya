import Theorems.Thm_StickyKakeya4_native_relative_parent_tail_profiles
import Theorems.Thm_StickyKakeya4_native_same_source_coarse_admission

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

noncomputable section
namespace NativeActualRelativeCoarseAdmission
open Classical Finset MeasureTheory StickyKakeya4 NativeOriginalParentSelection
open NativeCommonCubicalMesh NativeCubicalIncidenceCounts NativeLocalParentSource
open NativeRelativeParentTailProfiles NativeUnitParentNormalization
open scoped BigOperators ENNReal

/-- The original reference law already constructed by compact admission. -/
def OriginalPopulationLaw {n : ℕ} (D : FiniteScaleSource n) (R : Finset (Fin n))
    (a zeta : ℝ) (level : ℕ) : Prop :=
  ∀ k : Fin (level+1), ∀ q : Parent,
    (R.filter (fun i => parentLabel D a (2^k.val) i = q)).Nonempty →
      D.thickness^zeta*((1/((2^k.val:ℕ):ℝ))/D.thickness)^3 ≤
        ((R.filter (fun i => parentLabel D a (2^k.val) i = q)).card : ℝ) ∧
      ((R.filter (fun i => parentLabel D a (2^k.val) i = q)).card : ℝ) ≤
        D.thickness^(-zeta)*((1/((2^k.val:ℕ):ℝ))/D.thickness)^3

/-- The local source's literal selected cells already use its common mesh. -/
lemma source_common_mesh {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (E : Finset (Fin n × Index)) (a : ℝ) (m : ℕ) (p : Parent)
    (i : Fin (parentLabels D R a (2^m) p).card) :
    (source h R E a m p).shading i =
      wzCellShading (mesh (source h R E a m p)) (sourceCells D R E a (2^m) p) i := by
  rw [source_shading]
  congr 1
  change (((2^m:ℕ):ℝ)*D.thickness/128) = (((2^m:ℕ):ℝ)*D.thickness/64)/2
  ring

/-- Zero is the actual common center height of every local marked segment. -/
lemma source_common_height_zero {n : ℕ} {D : FiniteScaleSource n} {eta localEta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (E : Finset (Fin n × Index)) (a : ℝ) (m : ℕ) (p : Parent)
    (hlocal : IsWangZakharovNativeFiniteInput (source h R E a m p) localEta)
    (i : Fin (parentLabels D R a (2^m) p).card) :
    wzGraphTime ((source h R E a m p).line i) 0-mark ((source h R E a m p).line i) ∈
      Set.Icc (-(1/2:ℝ)) (1/2:ℝ) := by
  have hd : direction ((source h R E a m p).line i) (3:Fin 4) ≠ 0 := by
    have hh := hlocal.2.1.1 i
    linarith
  rw [wzGraphTime_sub_mark_eq _ _ hd,source_center_height_zero]
  norm_num

/-- All original cells on all actual local-source labels are retained.
The relative coarse step therefore pays the exact incidence factor one. -/
lemma incidences_retained_univ {n : ℕ} (cells : Fin n → Finset Index) :
    NativeOriginalParentDensityCore.retained cells univ = incidences cells := by
  simp [NativeOriginalParentDensityCore.retained]

/-- Derive the complete local population law from the original R, including
the last six dyadic levels. The local reference is all existing source labels. -/
theorem source_population_law {n : ℕ} {D : FiniteScaleSource n}
    {eta localEta : ℝ} (h : IsWangZakharovNativeFiniteInput D eta)
    (R : Finset (Fin n)) (E : Finset (Fin n × Index)) (a zeta e : ℝ)
    (hzeta : 0 ≤ zeta) (level : ℕ) (hdy : D.thickness=(2:ℝ)⁻¹^level)
    (H : OriginalPopulationLaw D R a zeta level) (m : ℕ) (hm : m ≤ level) (p : Parent)
    (hlocal : IsWangZakharovNativeFiniteInput (source h R E a m p) localEta)
    (hbudget : (64:ℝ)^3*(source h R E a m p).thickness^e ≤ D.thickness^zeta) :
    OriginalPopulationLaw (source h R E a m p) univ 0 e (level-m+6) := by
  intro ell q hq
  exact source_all_dyadic_population_power h R E a zeta hzeta level hdy H m hm p
    hlocal hbudget ell q hq

/-- Deterministic relative coarse admission on the literal already-admitted
local source. Its reference is univ, its height is zero, and its incidence
set consists of ALL literal sourceCells. No new original R or shading is
selected and the local population premise is derived internally. -/
theorem actual_local_relative_coarse_admission {e window : ℝ}
    (he : 0 < e) (hw : 0 < window) :
    ∃ eps0 : ℝ, 0 < eps0 ∧
      ∀ (n : ℕ) (D : FiniteScaleSource n) (eta : ℝ)
        (h : IsWangZakharovNativeFiniteInput D eta)
        (R : Finset (Fin n)) (E : Finset (Fin n × Index)) (a zeta : ℝ),
        0 ≤ zeta → ∀ level : ℕ, D.thickness=(2:ℝ)⁻¹^level →
        OriginalPopulationLaw D R a zeta level →
        ∀ m : ℕ, m ≤ level → ∀ (p : Parent) (localEta : ℝ)
          (hlocal : IsWangZakharovNativeFiniteInput (source h R E a m p) localEta),
          (∀i,(source h R E a m p).line i∈fixedCompactClass) →
          (source h R E a m p).thickness ≤ eps0 → localEta ≤ window*e/512 →
          (64:ℝ)^3*(source h R E a m p).thickness^(window*e/32) ≤ D.thickness^zeta →
          ∀ ell : ℕ,
            1/((2^ell:ℕ):ℝ) ≤ (source h R E a m p).thickness^window →
            (source h R E a m p).thickness/(1/((2^ell:ℕ):ℝ)) ≤
              (source h R E a m p).thickness^window →
            let S := source h R E a m p
            let Eall := incidences (sourceCells D R E a (2^m) p)
            let rep := NativeCoarseDirectionThinning.representative hlocal univ 0 (2^ell)
            ∃ (Q : Finset Parent)
              (hsep : ∀u∈Q,∀v∈Q,u≠v → 64/((2^ell:ℕ):ℝ) ≤
                dist (direction (S.line (rep u))) (direction (S.line (rep v)))),
              Q⊆parents S 0 (2^ell) ∧ Q.Nonempty ∧
              let C := NativeCoarseCellSource.source hlocal 0 (level-m+6) ell Q rep Eall hsep
              IsWangZakharovNativeFiniteInput C e ∧ (∀i,C.line i∈fixedCompactClass) ∧
              C.thickness=64/((2^ell:ℕ):ℝ) ∧
              (ENNReal.ofReal S.thickness).rpow (7*(window*e/32))*
                NativeFiniteKakeyaCounts.multiplicity
                  (NativeFullCoarseShadow.fullSource hlocal univ 0 (level-m+6) ell Eall) ≤
                    NativeFiniteKakeyaCounts.multiplicity C ∧
              S.thickness^(5*(window*e/32)) ≤ (wzTotalShadingVolume C).toReal := by
  obtain ⟨eps0,heps0,hadmit⟩ :=
    NativeSameSourceCoarseAdmission.same_source_coarse_admission he hw 1 (by norm_num)
  refine ⟨eps0,heps0,?_⟩
  intro n D eta h R E a zeta hzeta level hdy H m hm p localEta hlocal hfixed hsmall heta
    hbudget ell hcoarse hfine
  let S := source h R E a m p
  let cells := sourceCells D R E a (2^m) p
  let Eall := incidences cells
  have hR : (univ : Finset (Fin (parentLabels D R a (2^m) p).card)).Nonempty := by
    apply card_pos.mp
    simpa using hlocal.1.1
  have hE : Eall ⊆ NativeOriginalParentDensityCore.retained cells univ := by
    rw [incidences_retained_univ]
  have hret : (incidences cells).card ≤ 1*Eall.card := by simp [Eall]
  have hH := source_population_law h R E a zeta (window*e/32) hzeta level hdy H m hm p hlocal hbudget
  obtain ⟨Q,hsep,hQ,hQne,hC,hCK,htransfer,hshade⟩ :=
    hadmit _ S localEta hlocal hfixed hsmall heta cells 0 (level-m+6) univ Eall
      (source_common_mesh h R E a m p) (source_thickness_dyadic h R E a level m hdy hm p)
      (source_common_height_zero h R E a m p hlocal) hR hE hret hH ell hcoarse hfine
  exact ⟨Q,hsep,hQ,hQne,hC,hCK,rfl,htransfer,hshade⟩

/-- Relative full-coarse multiplicity upper on the exact admitted S. The
caller provides only its already-derived native admission, original R law,
and an explicit scalar budget. No relative output profile is postulated. -/
theorem actual_local_relative_full_coarse_upper {epsilon window : ℝ}
    (hepsilon : 0 < epsilon) (hw : 0 < window) :
    ∃ e eta0 eps0 : ℝ, 0 < e ∧ 0 < eta0 ∧ 0 < eps0 ∧
      ∀ (n : ℕ) (D : FiniteScaleSource n) (eta : ℝ)
        (h : IsWangZakharovNativeFiniteInput D eta)
        (R : Finset (Fin n)) (E : Finset (Fin n × Index)) (a zeta : ℝ),
        0 ≤ zeta → ∀ level : ℕ, D.thickness=(2:ℝ)⁻¹^level →
        OriginalPopulationLaw D R a zeta level →
        ∀ m : ℕ, m ≤ level → ∀ (p : Parent) (localEta : ℝ)
          (hlocal : IsWangZakharovNativeFiniteInput (source h R E a m p) localEta),
          (∀i,(source h R E a m p).line i∈fixedCompactClass) →
          (source h R E a m p).thickness ≤ eps0 → localEta ≤ eta0 →
          (64:ℝ)^3*(source h R E a m p).thickness^(window*e/32) ≤ D.thickness^zeta →
          ∀ ell : ℕ,
            1/((2^ell:ℕ):ℝ) ≤ (source h R E a m p).thickness^window →
            (source h R E a m p).thickness/(1/((2^ell:ℕ):ℝ)) ≤
              (source h R E a m p).thickness^window →
            let S := source h R E a m p
            let Eall := incidences (sourceCells D R E a (2^m) p)
            (ENNReal.ofReal S.thickness).rpow (7*(window*e/32))*
              NativeFiniteKakeyaCounts.multiplicity
                (NativeFullCoarseShadow.fullSource hlocal univ 0 (level-m+6) ell Eall) ≤
              (ENNReal.ofReal (64/((2^ell:ℕ):ℝ))).rpow
                (-NativeFixedCompactKakeyaExponent.extremalExponent-epsilon) := by
  obtain ⟨e,eta0,eps0,he,heta0,heps0,hupper⟩ :=
    NativeSameSourceCoarseAdmission.same_source_full_coarse_upper hepsilon hw 1 (by norm_num)
  refine ⟨e,eta0,eps0,he,heta0,heps0,?_⟩
  intro n D eta h R E a zeta hzeta level hdy H m hm p localEta hlocal hfixed hsmall heta
    hbudget ell hcoarse hfine
  let S := source h R E a m p
  let cells := sourceCells D R E a (2^m) p
  let Eall := incidences cells
  have hR : (univ : Finset (Fin (parentLabels D R a (2^m) p).card)).Nonempty := by
    apply card_pos.mp
    simpa using hlocal.1.1
  have hE : Eall ⊆ NativeOriginalParentDensityCore.retained cells univ := by
    rw [incidences_retained_univ]
  have hret : (incidences cells).card ≤ 1*Eall.card := by simp [Eall]
  have hH := source_population_law h R E a zeta (window*e/32) hzeta level hdy H m hm p hlocal hbudget
  exact hupper _ S localEta hlocal hfixed hsmall heta cells 0 (level-m+6) univ Eall
    (source_common_mesh h R E a m p) (source_thickness_dyadic h R E a level m hdy hm p)
    (source_common_height_zero h R E a m p hlocal) hR hE hret hH ell hcoarse hfine

/-- The two normalization scales multiply with the full factor4096.
This scalar identity makes no identification of relative coarse labels or
shadings with an original global coarse source. -/
lemma two_step_scale_trace {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (E : Finset (Fin n × Index)) (a : ℝ) (m ell : ℕ) (p : Parent) :
    (64/((2^m:ℕ):ℝ))*(source h R E a m p).thickness = D.thickness ∧
    (64/((2^m:ℕ):ℝ))*(64/((2^ell:ℕ):ℝ)) = 4096/((2^(m+ell):ℕ):ℝ) := by
  constructor
  · rw [source_thickness]
    field_simp
  · simp only [pow_add,Nat.cast_mul]
    ring

/-- The relative chart still reads the original MN parameter label through
the exact slope shear and intercept division by512. No six-level scale
adjustment is silently applied to this label identity. -/
lemma actual_relative_parameter_trace {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (E : Finset (Fin n × Index)) (a : ℝ) (m ell : ℕ) (p : Parent)
    (i : Fin (parentLabels D R a (2^m) p).card) :
    parentLabel (source h R E a m p) 0 (2^ell) i =
      NativeRelativeParentLabels.projection p (2^ell)
        (parentLabel D a (2^(m+ell))
          (NativePaddedCellSource.originalLabel (parentLabels D R a (2^m) p) i)) := by
  rw [NativeRelativeParentProfiles.source_parentLabel,
    NativeRelativeParentLabels.relativeLabel_eq_projection]
  rw [pow_add,Nat.mul_comm (2^m) (2^ell)]

/-- Preselecting zeta below alpha times the required relative-profile
exponent yields the scalar budget from the original power window. This
cutoff is uniform in the original source and the selected integer scale. -/
theorem exists_relative_population_budget (alpha window e zeta : ℝ)
    (hw : 0 < window) (he : 0 < e) (hzeta : 0 ≤ zeta)
    (hgap : zeta < alpha*(window*e/32)) :
    ∃ d0 : ℝ, 0 < d0 ∧ d0 ≤ 1 ∧ ∀ delta : ℝ,
      0 < delta → delta ≤ d0 → ∀ N : ℕ, 0 < N →
      (N:ℝ)*delta ≤ delta^alpha →
        (64:ℝ)^3*((N:ℝ)*delta/64)^(window*e/32) ≤ delta^zeta := by
  obtain ⟨d0,hd0,hd01,hcoeff⟩ := NativeLocalParentAD.exists_native_coefficient_cutoff
    alpha (window*e/32) zeta (by positivity) hzeta hgap
  refine ⟨d0,hd0,hd01,?_⟩
  intro delta hd hsmall N hN hwindow
  have hh := (hcoeff delta hd hsmall N hN hwindow).1
  have hp : 0 ≤ delta^zeta := Real.rpow_nonneg hd.le zeta
  calc
    _ ≤ (64:ℝ)^3*(delta^zeta/(2048:ℝ)^3) :=
      mul_le_mul_of_nonneg_left hh (by positivity)
    _ = delta^zeta/32768 := by ring
    _ ≤ delta^zeta := by linarith

end NativeActualRelativeCoarseAdmission
