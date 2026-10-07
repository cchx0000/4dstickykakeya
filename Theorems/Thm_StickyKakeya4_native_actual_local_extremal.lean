import Theorems.Thm_StickyKakeya4_native_actual_local_admission
import Theorems.Thm_StickyKakeya4_native_fixed_compact_multiplicity

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000

noncomputable section
namespace NativeActualLocalExtremal
open Classical Finset MeasureTheory StickyKakeya4 NativeOriginalParentSelection
open NativeCommonCubicalMesh NativeCubicalIncidenceCounts NativeLocalParentSource
open NativeOriginalParentDensityCore NativeUnitParentNormalization NativeActualLocalAdmission
open NativeFixedCompactKakeyaExponent
open scoped ENNReal BigOperators

/-- A cutoff chosen before D makes every actual local scale in the relative
window small enough for the fixed-compact extremal theorem. -/
theorem exists_relative_window_cutoff {alpha target : ℝ}
    (halpha : 0 < alpha) (htarget : 0 < target) :
    ∃ delta0 : ℝ, 0 < delta0 ∧ ∀ delta : ℝ, 0 < delta → delta ≤ delta0 →
      ∀ N : ℕ, 0 < N → (N:ℝ)*delta ≤ delta^alpha → (N:ℝ)*delta/64 ≤ target := by
  obtain ⟨delta0,hdelta0,_hdelta01,hcut⟩ := exists_positive_rpow_absorption_threshold
    halpha (show (0:ℝ) ≤ 1 by norm_num) htarget
  refine ⟨delta0,hdelta0,?_⟩
  intro delta hd hsmall N hN hwindow
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  have hlocal : (N:ℝ)*delta/64 ≤ (N:ℝ)*delta := by nlinarith [mul_pos hNr hd]
  exact (hlocal.trans hwindow).trans (by simpa only [one_mul] using hcut delta hd hsmall)

/-- The fixed-compact extremal upper estimate is applied to each actual
admitted source on the same R and E. No output admission certificate is an
assumption: the original compact native input constructs all of them.
The last inequality combines the geometric parent transfer with this actual
source upper bound, while preserving the original eta and finite-menu costs. -/
theorem compact_original_scheduled_local_extremal_upper
    (K : Set MarkedLine) (hK : IsCompact K) (epsilon alpha : ℝ)
    (hepsilon : 0 < epsilon) (halpha : 0 < alpha) (d g : ℕ) (hdg : 0 < d+g) :
    ∃ (e zeta : ℝ) (L : ℕ) (eta0 delta0 : ℝ),
      0 < e ∧ 0 < zeta ∧ 0 < L ∧ 0 < eta0 ∧ 0 < delta0 ∧
      ∀ (n : ℕ) (D : FiniteScaleSource n) (eta : ℝ)
        (h : IsWangZakharovNativeFiniteInput D eta),
        (∀i,D.line i ∈ K) → D.thickness ≤ delta0 → eta ≤ eta0 →
        ∃ (a : ℝ) (level : ℕ) (R : Finset (Fin n)) (original : Fin n → Finset Index),
          (∀i,D.shading i = wzCellShading (mesh D) original i) ∧
          D.thickness = (2:ℝ)⁻¹^level ∧
          (∀i,wzGraphTime (D.line i) a-mark (D.line i) ∈ Set.Icc (-(1/2:ℝ)) (1/2:ℝ)) ∧
          R.Nonempty ∧ n ≤ 2*R.card ∧
          wzTotalShadingVolume D ≤ 2*NativeOriginalPrunedMass.shadingMass D R ∧
          (ENNReal.ofReal D.thickness).rpow zeta*NativeOriginalPrunedMass.tubeMass D R ≤
            NativeOriginalPrunedMass.shadingMass D R ∧
          (∀ U : Set E4, Convex ℝ U →
            ((R.filter (fun i => markedUnitTube (D.line i) D.thickness ⊆ U)).card:ℝ≥0∞) ≤
              (ENNReal.ofReal D.thickness).rpow (-zeta)*volume U*R.card) ∧
          (∀ (ell : Fin (level+1)) (p : Parent),
            (R.filter (fun i => parentLabel D a (2^ell.val) i=p)).Nonempty →
              D.thickness^zeta*((1/((2^ell.val:ℕ):ℝ))/D.thickness)^3 ≤
                ((R.filter (fun i => parentLabel D a (2^ell.val) i=p)).card:ℝ) ∧
              ((R.filter (fun i => parentLabel D a (2^ell.val) i=p)).card:ℝ) ≤
                D.thickness^(-zeta)*((1/((2^ell.val:ℕ):ℝ))/D.thickness)^3) ∧
          ∀ (Rel : Fin d → (Fin n × Index) → (Fin n × Index) → Prop),
            (∀j x,Rel j x x) → (∀j x y,Rel j x y → Rel j y x) →
            ∀ schedule : Fin g → Fin (level+1),
              (∀j,((2^(schedule j).val:ℕ):ℝ)*D.thickness ≤ D.thickness^alpha) →
              ∃ E, IsCore D original R a eta zeta d g L Rel
                (fun j => 2^(schedule j).val) E ∧
                ∀j p,(parentEdges D a (2^(schedule j).val) E p).Nonempty →
                  let Ep := parentEdges D a (2^(schedule j).val) E p
                  let S := source h R Ep a (schedule j).val p
                  IsWangZakharovNativeFiniteInput S e ∧
                    (∀i,S.line i ∈ fixedCompactClass) ∧
                    HasExactTrace h R Ep a (schedule j).val p ∧
                    NativeFiniteKakeyaCounts.multiplicity S ≤
                      (ENNReal.ofReal S.thickness).rpow (-extremalExponent-epsilon) ∧
                    (Ep.card:ℝ)/(Ep.image Prod.snd).card ≤
                      (125*175616*16384:ℝ)*(factor d g L:ℝ)*(coreRadix original R L:ℝ)^2*
                        D.thickness^(-eta)*(NativeFiniteKakeyaCounts.multiplicity S).toReal ∧
                    (Ep.card:ℝ)/(Ep.image Prod.snd).card ≤
                      (125*175616*16384:ℝ)*(factor d g L:ℝ)*(coreRadix original R L:ℝ)^2*
                        D.thickness^(-eta)*S.thickness^(-extremalExponent-epsilon) := by
  obtain ⟨e,he,dm,hdm,hupper⟩ :=
    NativeFixedCompactMultiplicity.fixed_compact_multiplicity_upper hepsilon
  obtain ⟨dw,hdw,hwindowCut⟩ := exists_relative_window_cutoff halpha hdm
  obtain ⟨zeta,L,eta0,da,hzeta,hL,heta0,hda,hadmission⟩ :=
    compact_original_scheduled_native_admission K hK e alpha he halpha d g hdg
  refine ⟨e,zeta,L,eta0,min da dw,he,hzeta,hL,heta0,lt_min hda hdw,?_⟩
  intro n D eta h hDK hsmall heta
  obtain ⟨a,level,R,original,horiginal,hdy,ha,hR,hhalf,hshade,hdensity,hCW,H,hcore⟩ :=
    hadmission n D eta h hDK (hsmall.trans (min_le_left _ _)) heta
  refine ⟨a,level,R,original,horiginal,hdy,ha,hR,hhalf,hshade,hdensity,hCW,H,?_⟩
  intro Rel hrefl hsym schedule hwindow
  obtain ⟨E,hEcore,hparents⟩ := hcore Rel hrefl hsym schedule hwindow
  refine ⟨E,hEcore,?_⟩
  intro j p hp
  let Ep := parentEdges D a (2^(schedule j).val) E p
  let S := source h R Ep a (schedule j).val p
  obtain ⟨hinput,hfixed,htrace,htransfer⟩ := hparents j p hp
  have hlocalSmall : S.thickness ≤ dm := hwindowCut D.thickness h.1.2.1
    (hsmall.trans (min_le_right _ _)) (2^(schedule j).val) (by positivity) (hwindow j)
  have hmu := hupper (parentLabels D R a (2^(schedule j).val) p).card S hlocalSmall hinput hfixed
  have heps : 0 < S.thickness := hinput.1.2.1
  have hfinite : (ENNReal.ofReal S.thickness).rpow (-extremalExponent-epsilon) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_ne_zero (ENNReal.ofReal_ne_zero_iff.mpr heps) ENNReal.ofReal_ne_top
  have hmuReal : (NativeFiniteKakeyaCounts.multiplicity S).toReal ≤
      S.thickness^(-extremalExponent-epsilon) := by
    have hh := ENNReal.toReal_mono hfinite hmu
    simpa only [ENNReal.rpow_eq_pow,←ENNReal.toReal_rpow,ENNReal.toReal_ofReal heps.le] using hh
  refine ⟨hinput,hfixed,htrace,hmu,htransfer,?_⟩
  have hnonneg : 0 ≤ D.thickness^(-eta) := Real.rpow_nonneg h.1.2.1.le _
  exact htransfer.trans (mul_le_mul_of_nonneg_left hmuReal (by positivity))

end NativeActualLocalExtremal
