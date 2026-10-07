import Theorems.Thm_StickyKakeya4_native_actual_local_extremal
import Theorems.Thm_StickyKakeya4_native_local_transfer_budget

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000

noncomputable section
namespace NativeActualLocalPowerUpper
open Classical Finset MeasureTheory StickyKakeya4 NativeOriginalParentSelection
open NativeCommonCubicalMesh NativeCubicalIncidenceCounts NativeLocalParentSource
open NativeOriginalParentDensityCore NativeUnitParentNormalization NativeActualLocalAdmission
open NativeFixedCompactKakeyaExponent NativeActualLocalExtremal
open scoped ENNReal BigOperators

/-- Source-facing local upper estimate with an arbitrarily prescribed small
original-scale loss theta. Every finite-core factor is absorbed using the
actual source incidence/radix bound, with all choices made before D.
The same R and E support admission, exact trace and the extremal upper bound. -/
theorem compact_original_scheduled_local_power_upper
    (K : Set MarkedLine) (hK : IsCompact K) (epsilon alpha theta : ℝ)
    (hepsilon : 0 < epsilon) (halpha : 0 < alpha) (htheta : 0 < theta)
    (d g : ℕ) (hdg : 0 < d+g) :
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
                (125*175616*16384:ℝ)*(factor d g L:ℝ)*(coreRadix original R L:ℝ)^2*
                  D.thickness^(-eta) ≤ D.thickness^(-theta) ∧
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
                      D.thickness^(-theta)*S.thickness^(-extremalExponent-epsilon) := by
  obtain ⟨eu,heu,dm,hdm,hupper⟩ :=
    NativeFixedCompactMultiplicity.fixed_compact_multiplicity_upper hepsilon
  let e := min eu (theta/alpha)
  have he : 0 < e := lt_min heu (div_pos htheta halpha)
  have heeu : e ≤ eu := min_le_left _ _
  have hbeta : 0 < alpha*e := mul_pos halpha he
  have hbetatheta : alpha*e ≤ theta := by
    have hh := (le_div_iff₀ halpha).mp (show e ≤ theta/alpha from min_le_right _ _)
    nlinarith only [hh]
  obtain ⟨zeta,L,eta0,db,hzdef,hzeta,hL,hLlarge,heta0,hetaz,hdb,_hdbsmall,hbudget⟩ :=
    NativeLocalAdmissionBudget.exists_uniform_source_budget e alpha he halpha d g
  have hLp : (0:ℝ) < L := by exact_mod_cast hL
  have hradixexp : 8/(L:ℝ) ≤ alpha*e/32 := by
    have hh := (div_lt_iff₀ hbeta).mp hLlarge
    apply (div_le_iff₀ hLp).mpr
    nlinarith only [hh]
  have hgap : eta0+8/(L:ℝ) ≤ theta/2 := by
    rw [hzdef] at hetaz
    linarith
  obtain ⟨dt,hdt,_hdt1,htransferCut⟩ :=
    NativeLocalTransferBudget.exists_parent_transfer_cutoff theta htheta d g L hL eta0 hgap
  obtain ⟨dw,hdw,hwindowCut⟩ := exists_relative_window_cutoff halpha hdm
  obtain ⟨dc,hdc,hbase⟩ := compact_original_scheduled_parent_density_core K hK hzeta
  let delta0 := min db (min dc (min dw dt))
  have hd0 : 0 < delta0 := lt_min hdb (lt_min hdc (lt_min hdw hdt))
  refine ⟨e,zeta,L,eta0,delta0,he,hzeta,hL,heta0,hd0,?_⟩
  intro n D eta h hDK hsmall heta
  have hDdb : D.thickness ≤ db := hsmall.trans (min_le_left _ _)
  have hDdc : D.thickness ≤ dc := hsmall.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hDdw : D.thickness ≤ dw :=
    hsmall.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hDdt : D.thickness ≤ dt :=
    hsmall.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  obtain ⟨a,level,R,original,horiginal,hdy,ha,hR,hhalf,hshade,hdensity,hCW,H,hcore⟩ :=
    hbase n D eta h hDK hDdc (heta.trans hetaz)
  refine ⟨a,level,R,original,horiginal,hdy,ha,hR,hhalf,hshade,hdensity,hCW,H,?_⟩
  intro Rel hrefl hsym schedule hwindow
  obtain ⟨E,hEcore⟩ := hcore d g L hdg hL Rel hrefl hsym schedule
  have hEA : E ⊆ retained original R := hEcore.1
  have hEne : E.Nonempty := hEcore.2.1
  have hA : retained original R ⊆ incidences original := filter_subset _ _
  have hAne : (retained original R).Nonempty := hEne.mono hEA
  have hE : E ⊆ incidences original := hEA.trans hA
  have hcost := htransferCut n D eta h hDdt heta original horiginal (retained original R) hA hAne
  refine ⟨E,hEcore,hcost,?_⟩
  have hF : (0:ℝ) < factor d g L := by
    have hbasepos : 0 < d+g+g := by omega
    unfold factor NativeLocalPairUniformCore.retentionCost
    positivity
  have hQrad : (0:ℝ) < coreRadix original R L := by
    have hh := NativeSourceSizeBounds.radix_four_le (retained original R).card L
    exact_mod_cast (show 0 < coreRadix original R L by dsimp [coreRadix]; omega)
  intro j p hp
  let Ep := parentEdges D a (2^(schedule j).val) E p
  let S := source h R Ep a (schedule j).val p
  have hEp : Ep ⊆ incidences original := (filter_subset _ _).trans hE
  have hQ : ∀z∈Ep,z.1 ∈ parentLabels D R a (2^(schedule j).val) p := by
    intro z hz
    obtain ⟨hzE,hzp⟩ := mem_filter.mp hz
    exact mem_filter.mpr ⟨(mem_filter.mp (hEA hzE)).2,hzp⟩
  have hQne : (parentLabels D R a (2^(schedule j).val) p).Nonempty := by
    obtain ⟨z,hz⟩ := hp
    exact ⟨z.1,hQ z hz⟩
  obtain ⟨had,hcw,hden⟩ := hbudget n D eta h hDdb heta
    original horiginal (retained original R) hA hAne (2^(schedule j).val) (by positivity) (hwindow j)
  obtain ⟨hnative,hfixed⟩ := native_input h hzeta.le original horiginal ha R Ep hEp
    level (schedule j).val hdy (Nat.le_of_lt_succ (schedule j).isLt) p hQ hQne
    (fun ell q hq => (H ell q hq).1) (factor d g L) (coreRadix original R L) hF hQrad
    (hEcore.2.2.2.2.2.1 j p hp) had hcw hden
  have htransfer := source_parent_multiplicity_transfer h original horiginal ha R E hE
    (schedule j).val p hF hQrad (hEcore.2.2.2.2.2.2 j) hp hQ
  have hlocalSmall : S.thickness ≤ dm := hwindowCut D.thickness h.1.2.1 hDdw
    (2^(schedule j).val) (by positivity) (hwindow j)
  have hmu := hupper (parentLabels D R a (2^(schedule j).val) p).card S hlocalSmall
    (NativeFiniteKakeyaCounts.input_mono hnative heeu) hfixed
  have heps : 0 < S.thickness := hnative.1.2.1
  have hfinite : (ENNReal.ofReal S.thickness).rpow (-extremalExponent-epsilon) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_ne_zero (ENNReal.ofReal_ne_zero_iff.mpr heps) ENNReal.ofReal_ne_top
  have hmuReal : (NativeFiniteKakeyaCounts.multiplicity S).toReal ≤
      S.thickness^(-extremalExponent-epsilon) := by
    have hh := ENNReal.toReal_mono hfinite hmu
    simpa only [ENNReal.rpow_eq_pow,←ENNReal.toReal_rpow,ENNReal.toReal_ofReal heps.le] using hh
  exact ⟨hnative,hfixed,source_exact_trace h R Ep a (schedule j).val p hQ,hmu,htransfer,
    htransfer.trans (mul_le_mul hcost hmuReal ENNReal.toReal_nonneg (Real.rpow_nonneg h.1.2.1.le _))⟩

end NativeActualLocalPowerUpper
