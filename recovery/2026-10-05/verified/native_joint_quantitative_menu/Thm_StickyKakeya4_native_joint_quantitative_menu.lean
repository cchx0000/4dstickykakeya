import Theorems.Thm_StickyKakeya4_native_joint_uniform_coarse_relations

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

noncomputable section
namespace NativeJointQuantitativeMenu
open Classical Finset MeasureTheory StickyKakeya4 NativeOriginalParentSelection
open NativeCommonCubicalMesh NativeCubicalIncidenceCounts NativeLocalParentSource
open NativeOriginalParentDensityCore NativeUnitParentNormalization NativeActualLocalAdmission
open NativeFixedCompactKakeyaExponent NativeActualLocalExtremal NativeJointLocalCoarseUpper
open NativeJointUniformCoarseRelations SelfUniform
open scoped ENNReal BigOperators

def HasCoarseScale {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (E : Finset (Fin n × Index)) (a : ℝ) (level m : ℕ) (e zeta theta epsilon : ℝ) : Prop :=
  let rep := NativeCoarseDirectionThinning.representative h R a (2^m)
  (∃ (Q : Finset Parent)
    (hsep : ∀p∈Q,∀q∈Q,p≠q → 64/((2^m:ℕ):ℝ) ≤
      dist (direction (D.line (rep p))) (direction (D.line (rep q)))),
    Q⊆R.image (parentLabel D a (2^m)) ∧ Q.Nonempty ∧
    let C := NativeCoarseCellSource.source h a level m Q rep E hsep
    IsWangZakharovNativeFiniteInput C e ∧ (∀i,C.line i∈fixedCompactClass) ∧
    C.thickness=64/((2^m:ℕ):ℝ) ∧
    D.thickness^(5*zeta) ≤ (wzTotalShadingVolume C).toReal ∧
    (ENNReal.ofReal D.thickness).rpow (7*zeta)*
      NativeFiniteKakeyaCounts.multiplicity (NativeFullCoarseShadow.fullSource h R a level m E) ≤
        NativeFiniteKakeyaCounts.multiplicity C ∧
    NativeFiniteKakeyaCounts.multiplicity C ≤
      (ENNReal.ofReal (64/((2^m:ℕ):ℝ))).rpow (-extremalExponent-epsilon)) ∧
  NativeFiniteKakeyaCounts.multiplicity (NativeFullCoarseShadow.fullSource h R a level m E) ≤
    (ENNReal.ofReal D.thickness).rpow (-theta)*
      (ENNReal.ofReal (64/((2^m:ℕ):ℝ))).rpow (-extremalExponent-epsilon)

/-- Quantitative choices and every coarse scale are exposed from the same
one-budget, one-original-core construction. No parameter is inferred from a
separate existential witness. -/
theorem joint_upper_with_parameters
    (epsilon window theta : ℝ) (hepsilon : 0 < epsilon)
    (hw : 0 < window) (htheta : 0 < theta) (d g : ℕ) (hdg : 0 < d+g) :
    ∃ (e zeta : ℝ) (L : ℕ) (eta0 delta0 : ℝ),
      0 < e ∧ zeta=window*e/32 ∧ 0 < zeta ∧ zeta ≤ theta/32 ∧ 0 < L ∧
      16/zeta < (L:ℝ) ∧ 0 < eta0 ∧ eta0 ≤ zeta/16 ∧ 0 < delta0 ∧
      ∀ (n : ℕ) (D : FiniteScaleSource n) (eta : ℝ)
        (h : IsWangZakharovNativeFiniteInput D eta),
        (∀i,D.line i ∈ fixedCompactClass) → D.thickness ≤ delta0 → eta ≤ eta0 →
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
              (∀j,1/((2^(schedule j).val:ℕ):ℝ) ≤ D.thickness^window) →
              (∀j,D.thickness/(1/((2^(schedule j).val:ℕ):ℝ)) ≤ D.thickness^window) →
              ∃ E, IsCore D original R a eta zeta d g L Rel
                (fun j => 2^(schedule j).val) E ∧
                (125*175616*16384:ℝ)*(factor d g L:ℝ)*(coreRadix original R L:ℝ)^2*
                  D.thickness^(-eta) ≤ D.thickness^(-theta) ∧
                (∀m : ℕ,1/((2^m:ℕ):ℝ) ≤ D.thickness^window →
                  D.thickness/(1/((2^m:ℕ):ℝ)) ≤ D.thickness^window →
                  HasCoarseScale h R E a level m e zeta theta epsilon) ∧
                ∀j,HasJointScale h R E a level (schedule j).val e zeta theta epsilon := by
  obtain ⟨eu,heu,dm,hdm,hupper⟩ :=
    NativeFixedCompactMultiplicity.fixed_compact_multiplicity_upper hepsilon
  let e := min eu (theta/window)
  have he : 0 < e := lt_min heu (div_pos htheta hw)
  have heeu : e ≤ eu := min_le_left _ _
  have hbeta : 0 < (window/2)*e := mul_pos (half_pos hw) he
  have hbetatheta : window*e ≤ theta := by
    have hh := (le_div_iff₀ hw).mp (show e ≤ theta/window from min_le_right _ _)
    nlinarith only [hh]
  obtain ⟨zeta,L,eta0,db,hzdef,hzeta,hL,hLlarge,heta0,hetaz,hdb,_hdbsmall,hbudget⟩ :=
    NativeLocalAdmissionBudget.exists_uniform_source_budget e (window/2) he (half_pos hw) d g
  have hzeq : zeta=window*e/32 := by rw [hzdef]; ring
  have hzsmall : zeta ≤ theta/32 := by rw [hzeq]; linarith
  have hLquant : 16/zeta < (L:ℝ) := by
    rw [hzdef,div_div_eq_mul_div]
    norm_num
    exact hLlarge
  have hLp : (0:ℝ) < L := by exact_mod_cast hL
  have hradixexp : 8/(L:ℝ) ≤ (window/2)*e/32 := by
    have hh := (div_lt_iff₀ hbeta).mp hLlarge
    apply (div_le_iff₀ hLp).mpr
    nlinarith only [hh]
  have hgap : eta0+8/(L:ℝ) ≤ theta/2 := by rw [hzdef] at hetaz; linarith
  have hztheta : 7*zeta ≤ theta := by rw [hzeq]; linarith
  have hF : 0 < factor d g L := by
    have hbasepos : 0 < d+g+g := by omega
    unfold factor NativeLocalPairUniformCore.retentionCost
    positivity
  obtain ⟨dt,hdt,_hdt1,htransferCut⟩ :=
    NativeLocalTransferBudget.exists_parent_transfer_cutoff theta htheta d g L hL eta0 hgap
  obtain ⟨dl,hdl,hlocalCut⟩ := exists_relative_window_cutoff (half_pos hw) hdm
  obtain ⟨ds,hds,_hds1,hcoarseCut⟩ := exists_positive_rpow_absorption_threshold hw
    (show 0 ≤ 64/dm by positivity) (by norm_num : (0:ℝ)<1)
  obtain ⟨da,hda,hcoarseAdmit⟩ := NativeSameSourceCoarseAdmission.same_source_coarse_admission
    he hw (factor d g L) hF
  obtain ⟨dc,hdc,hbase⟩ := compact_original_scheduled_parent_density_core
    fixedCompactClass fixedCompactClass_compact hzeta
  let delta0 := min db (min dc (min dt (min dl (min ds da))))
  have hd0 : 0 < delta0 := lt_min hdb (lt_min hdc (lt_min hdt (lt_min hdl (lt_min hds hda))))
  refine ⟨e,zeta,L,eta0,delta0,he,hzeq,hzeta,hzsmall,hL,hLquant,heta0,hetaz,hd0,?_⟩
  intro n D eta h hDK hsmall heta
  have hh : D.thickness≤db ∧ D.thickness≤dc ∧ D.thickness≤dt ∧
      D.thickness≤dl ∧ D.thickness≤ds ∧ D.thickness≤da := by
    simpa only [delta0,le_min_iff] using hsmall
  obtain ⟨hDdb,hDdc,hDdt,hDdl,hDds,hDda⟩ := hh
  have hetac : eta ≤ window*e/512 := by have hh := heta.trans hetaz; rw [hzeq] at hh; linarith
  obtain ⟨a,level,R,original,horiginal,hdy,ha,hR,hhalf,hshade,hdensity,hCW,H,hcore⟩ :=
    hbase n D eta h hDK hDdc (heta.trans hetaz)
  refine ⟨a,level,R,original,horiginal,hdy,ha,hR,hhalf,hshade,hdensity,hCW,H,?_⟩
  intro Rel hrefl hsym schedule hcoarse hfine
  obtain ⟨E,hEcore⟩ := hcore d g L hdg hL Rel hrefl hsym schedule
  have hEA : E ⊆ retained original R := hEcore.1
  have hA : retained original R ⊆ incidences original := filter_subset _ _
  have hAne : (retained original R).Nonempty := hEcore.2.1.mono hEA
  have hE : E ⊆ incidences original := hEA.trans hA
  have hcost := htransferCut n D eta h hDdt heta original horiginal (retained original R) hA hAne
  have hFr : (0:ℝ) < factor d g L := by exact_mod_cast hF
  have hQrad : (0:ℝ) < coreRadix original R L := by
    have hh := NativeSourceSizeBounds.radix_four_le (retained original R).card L
    exact_mod_cast (show 0 < coreRadix original R L by dsimp [coreRadix]; omega)
  have hcoarseAll : ∀m : ℕ,1/((2^m:ℕ):ℝ) ≤ D.thickness^window →
      D.thickness/(1/((2^m:ℕ):ℝ)) ≤ D.thickness^window →
      HasCoarseScale h R E a level m e zeta theta epsilon := by
    intro m hcoarseM hfineM
    let rep := NativeCoarseDirectionThinning.representative h R a (2^m)
    obtain ⟨Q,hsep,hQP,hQne,hC,hCK,hfull,hCshade⟩ :=
      hcoarseAdmit n D eta h hDK hDda hetac original a level R E horiginal hdy ha hR
        hEA hEcore.2.2.1 (by simpa only [hzeq] using H) m hcoarseM hfineM
    let C := NativeCoarseCellSource.source h a level m Q rep E hsep
    have hsmallC : C.thickness ≤ dm := by
      have hh := hcoarseCut D.thickness h.1.2.1 hDds
      have heq : (64/dm)*D.thickness^window=(64*D.thickness^window)/dm := by ring
      rw [heq] at hh
      change 64/((2^m:ℕ):ℝ) ≤ dm
      calc
        _ = 64*(1/((2^m:ℕ):ℝ)) := by ring
        _ ≤ 64*D.thickness^window := mul_le_mul_of_nonneg_left hcoarseM (by norm_num)
        _ ≤ _ := (div_le_one hdm).mp hh
    have hmuC := hupper Q.card C hsmallC (NativeFiniteKakeyaCounts.input_mono hC heeu) hCK
    have hmuC' : NativeFiniteKakeyaCounts.multiplicity C ≤
        (ENNReal.ofReal (64/((2^m:ℕ):ℝ))).rpow (-extremalExponent-epsilon) := hmuC
    have hfull' : (ENNReal.ofReal D.thickness).rpow (7*zeta)*
        NativeFiniteKakeyaCounts.multiplicity (NativeFullCoarseShadow.fullSource h R a level m E) ≤
          NativeFiniteKakeyaCounts.multiplicity C := by simpa only [hzeq] using hfull
    have hfullUpper := remove_small_power h.1.2.1 h.1.2.2.1 hztheta (hfull'.trans hmuC')
    refine ⟨⟨Q,hsep,hQP,hQne,hC,hCK,rfl,?_,hfull',hmuC'⟩,hfullUpper⟩
    simpa only [hzeq] using hCshade
  refine ⟨E,hEcore,hcost,hcoarseAll,?_⟩
  intro j
  let m := (schedule j).val
  have hwindowLocal : ((2^m:ℕ):ℝ)*D.thickness ≤ D.thickness^(window/2) := by
    have hh : ((2^m:ℕ):ℝ)*D.thickness ≤ D.thickness^window := by
      simpa only [div_div_eq_mul_div,div_one,mul_comm] using hfine j
    exact hh.trans (Real.rpow_le_rpow_of_exponent_ge h.1.2.1 h.1.2.2.1 (by linarith))
  have hcoarseNow := hcoarseAll m (hcoarse j) (hfine j)
  refine ⟨hcoarseNow.1,hcoarseNow.2,?_⟩
  intro p hp
  let Ep := parentEdges D a (2^m) E p
  let S := source h R Ep a m p
  have hEp : Ep ⊆ incidences original := (filter_subset _ _).trans hE
  have hQ : ∀z∈Ep,z.1 ∈ parentLabels D R a (2^m) p := by
    intro z hz
    obtain ⟨hzE,hzp⟩ := mem_filter.mp hz
    exact mem_filter.mpr ⟨(mem_filter.mp (hEA hzE)).2,hzp⟩
  have hQne : (parentLabels D R a (2^m) p).Nonempty := by
    obtain ⟨z,hz⟩ := hp
    exact ⟨z.1,hQ z hz⟩
  obtain ⟨had,hcw,hden⟩ := hbudget n D eta h hDdb heta
    original horiginal (retained original R) hA hAne (2^m) (by positivity) hwindowLocal
  obtain ⟨hnative,hfixed⟩ := native_input h hzeta.le original horiginal ha R Ep hEp
    level m hdy (Nat.le_of_lt_succ (schedule j).isLt) p hQ hQne
    (fun ell q hq => (H ell q hq).1) (factor d g L) (coreRadix original R L) hFr hQrad
    (hEcore.2.2.2.2.2.1 j p hp) had hcw hden
  have htransfer := source_parent_multiplicity_transfer h original horiginal ha R E hE
    m p hFr hQrad (hEcore.2.2.2.2.2.2 j) hp hQ
  have hsmallS : S.thickness ≤ dm := hlocalCut D.thickness h.1.2.1 hDdl
    (2^m) (by positivity) hwindowLocal
  have hmu := hupper (parentLabels D R a (2^m) p).card S hsmallS
    (NativeFiniteKakeyaCounts.input_mono hnative heeu) hfixed
  have heps : 0 < S.thickness := hnative.1.2.1
  have hfinite : (ENNReal.ofReal S.thickness).rpow (-extremalExponent-epsilon) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_ne_zero (ENNReal.ofReal_ne_zero_iff.mpr heps) ENNReal.ofReal_ne_top
  have hmuReal : (NativeFiniteKakeyaCounts.multiplicity S).toReal ≤
      S.thickness^(-extremalExponent-epsilon) := by
    have hh := ENNReal.toReal_mono hfinite hmu
    simpa only [ENNReal.rpow_eq_pow,←ENNReal.toReal_rpow,ENNReal.toReal_ofReal heps.le] using hh
  exact ⟨hnative,hfixed,source_exact_trace h R Ep a m p hQ,hmu,
    htransfer.trans (mul_le_mul hcost hmuReal ENNReal.toReal_nonneg (Real.rpow_nonneg h.1.2.1.le _))⟩


/-- The actual three-relation menu is selected once with the same explicit
quantitative parameters. Full physical coarse bounds hold at every scale in
the window; local admission and the physical bridge hold on the finite menu. -/
theorem joint_quantitative_relations
    (epsilon window theta : ℝ) (hepsilon : 0 < epsilon)
    (hw : 0 < window) (htheta : 0 < theta) (d g : ℕ) (hdg : 0 < d+g) :
    ∃ (e zeta : ℝ) (L : ℕ) (eta0 delta0 : ℝ),
      0 < e ∧ zeta=window*e/32 ∧ 0 < zeta ∧ zeta ≤ theta/32 ∧ 0 < L ∧
      16/zeta < (L:ℝ) ∧ 0 < eta0 ∧ eta0 ≤ zeta/16 ∧ 0 < delta0 ∧
      ∀ (n : ℕ) (D : FiniteScaleSource n) (eta : ℝ)
        (h : IsWangZakharovNativeFiniteInput D eta),
        (∀i,D.line i ∈ fixedCompactClass) → D.thickness ≤ delta0 → eta ≤ eta0 →
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
          ∀ schedule : Fin g → Fin (level+1),
            (∀j,1/((2^(schedule j).val:ℕ):ℝ) ≤ D.thickness^window) →
            (∀j,D.thickness/(1/((2^(schedule j).val:ℕ):ℝ)) ≤ D.thickness^window) →
            ∀ (Rel : Fin d → (Fin n × Index) → (Fin n × Index) → Prop),
              (∀j x,Rel j x x) → (∀j x y,Rel j x y → Rel j y x) →
              ∃ E, IsCore D original R a eta zeta (menuSize d g) g L
                (relationMenu h R a schedule Rel) (fun j => 2^(schedule j).val) E ∧
                (125*175616*16384:ℝ)*(factor (menuSize d g) g L:ℝ)*(coreRadix original R L:ℝ)^2*
                  D.thickness^(-eta) ≤ D.thickness^(-theta) ∧
                (∀j x y,x∈E → y∈E → degree (fun _ : Fin n × Index => 1) (Rel j) E x ≤
                  (coreRadix original R L)^2*degree (fun _ : Fin n × Index => 1) (Rel j) E y) ∧
                (∀m : ℕ,1/((2^m:ℕ):ℝ) ≤ D.thickness^window →
                  D.thickness/(1/((2^m:ℕ):ℝ)) ≤ D.thickness^window →
                  HasCoarseScale h R E a level m e zeta theta epsilon) ∧
                ∀j,
                  HasJointScale h R E a level (schedule j).val e zeta theta epsilon ∧
                  HasUniformFibers E (coreRadix original R L) (physicalPair h R a level (schedule j).val) ∧
                  HasUniformFibers E (coreRadix original R L) (physicalPoint h R a level (schedule j).val) ∧
                  HasUniformFibers E (coreRadix original R L) (formalPair D a (schedule j).val) ∧
                  NativeIncidenceMultiplicityTower.multiplicity
                    (NativeIncidenceMultiplicityTower.coarse E (parentLabel D a (2^(schedule j).val))) ≤
                    (125:ℝ)*(coreRadix original R L:ℝ)^4*
                      (NativeFiniteKakeyaCounts.multiplicity
                        (NativeFullCoarseShadow.fullSource h R a level (schedule j).val E)).toReal ∧
                  ∀p,(parentEdges D a (2^(schedule j).val) E p).Nonempty →
                    ∀q,(parentEdges D a (2^(schedule j).val) E q).Nonempty →
                      NativeIncidenceMultiplicityTower.multiplicity (parentEdges D a (2^(schedule j).val) E p) ≤
                        (coreRadix original R L:ℝ)^2*
                          NativeIncidenceMultiplicityTower.multiplicity (parentEdges D a (2^(schedule j).val) E q) := by
  have hmenu : 0 < menuSize d g+g := by unfold menuSize; omega
  obtain ⟨e,zeta,L,eta0,delta0,he,hzeq,hzeta,hzsmall,hL,hLquant,heta0,hetaz,hdelta0,hbase⟩ :=
    joint_upper_with_parameters epsilon window theta hepsilon hw htheta (menuSize d g) g hmenu
  refine ⟨e,zeta,L,eta0,delta0,he,hzeq,hzeta,hzsmall,hL,hLquant,heta0,hetaz,hdelta0,?_⟩
  intro n D eta h hDK hsmall heta
  obtain ⟨a,level,R,original,horiginal,hdy,ha,hR,hhalf,hshade,hdensity,hCW,H,hcore⟩ :=
    hbase n D eta h hDK hsmall heta
  refine ⟨a,level,R,original,horiginal,hdy,ha,hR,hhalf,hshade,hdensity,hCW,H,?_⟩
  intro schedule hcoarse hfine Rel hrefl hsym
  let T := relationMenu h R a schedule Rel
  have hTrefl : ∀j x,T j x x := by
    intro j
    refine Fin.addCases ?_ ?_ j
    · intro k x
      simpa only [T,relationMenu,Fin.addCases_left] using hrefl k x
    · intro k
      refine Fin.addCases ?_ ?_ k
      · intro _j _x
        simp only [T,relationMenu,Fin.addCases_right,Fin.addCases_left]
      · intro k
        refine Fin.addCases ?_ ?_ k <;> intro _j _x <;>
          simp only [T,relationMenu,Fin.addCases_right,Fin.addCases_left]
  have hTsym : ∀j x y,T j x y → T j y x := by
    intro j
    refine Fin.addCases ?_ ?_ j
    · intro k x y hh
      simpa only [T,relationMenu,Fin.addCases_left] using
        hsym k x y (by simpa only [T,relationMenu,Fin.addCases_left] using hh)
    · intro k
      refine Fin.addCases ?_ ?_ k
      · intro _j _x _y hh
        simp only [T,relationMenu,Fin.addCases_right,Fin.addCases_left] at hh ⊢
        exact hh.symm
      · intro k
        refine Fin.addCases ?_ ?_ k <;> intro _j _x _y hh <;>
          simp only [T,relationMenu,Fin.addCases_right,Fin.addCases_left] at hh ⊢ <;> exact hh.symm
  obtain ⟨E,hEcore,hcost,hcoarseAll,hjoint⟩ := hcore T hTrefl hTsym schedule hcoarse hfine
  have hU := hEcore.2.2.2.1
  refine ⟨E,hEcore,hcost,?_,hcoarseAll,?_⟩
  · intro j x y hx hy
    simpa only [T,relationMenu,Fin.addCases_left] using
      hU (Fin.castAdd (g+(g+g)) j) x y hx hy
  intro j
  have hpair : HasUniformFibers E (coreRadix original R L)
      (physicalPair h R a level (schedule j).val) := by
    intro x hx y hy
    simpa only [T,relationMenu,Fin.addCases_right,Fin.addCases_left,unit_degree_eq_fiber] using
      hU (Fin.natAdd d (Fin.castAdd (g+g) j)) x y hx hy
  have hpoint : HasUniformFibers E (coreRadix original R L)
      (physicalPoint h R a level (schedule j).val) := by
    intro x hx y hy
    simpa only [T,relationMenu,Fin.addCases_right,Fin.addCases_left,unit_degree_eq_fiber] using
      hU (Fin.natAdd d (Fin.natAdd g (Fin.castAdd g j))) x y hx hy
  have hformal : HasUniformFibers E (coreRadix original R L)
      (formalPair D a (schedule j).val) := by
    intro x hx y hy
    simpa only [T,relationMenu,Fin.addCases_right,unit_degree_eq_fiber] using
      hU (Fin.natAdd d (Fin.natAdd g (Fin.natAdd g j))) x y hx hy
  refine ⟨hjoint j,hpair,hpoint,hformal,?_,?_⟩
  · have hE : E⊆incidences original := hEcore.1.trans (filter_subset _ _)
    have hER : ∀z∈E,z.1∈R := fun z hz => (mem_filter.mp (hEcore.1 hz)).2
    exact NativeCoarsePointMultiplicity.multiplicity_le_full_source h original horiginal ha
      R E hE hER level (schedule j).val hdy (Nat.le_of_lt_succ (schedule j).isLt)
      (coreRadix original R L) hpair hpoint
  · intro p hp q hq
    exact NativeParentAverageUniformity.parent_multiplicity_le E (parentLabel D a (2^(schedule j).val))
      (coreRadix original R L) hformal p hp q hq


end NativeJointQuantitativeMenu
