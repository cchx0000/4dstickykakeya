import Theorems.Thm_StickyKakeya4_native_common_Y_total_budget
import Theorems.Thm_StickyKakeya4_native_same_Q_fine_graph

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 7000000
noncomputable section
namespace NativeActualYTotalMass
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeCubicalIncidenceCounts NativeReferenceXYGridPoints NativeHorizontalGrainSlice
open NativeLocalParentSource NativeMiddleWindowBalance CanonicalConfiguredE4Bridge
open NativeConfiguredIncidenceFibers NativeActualSparseReferenceAdmission NativeActualBaselineGraphMass
open NativeConfiguredThirdRelation NativeJointUniformCoarseRelations NativeWholeYGraphRetention
open NativeLiteralYHeightAlignment NativeAlignmentTauRange SelfUniform
open NativeActualCommonYGraphMass NativeCommonYTotalBudget NativeSameReferenceChartBounds
open scoped BigOperators

/-- Pre-source source entrance for htotal. The same baseline sparse
admission, actual planar witnesses, actual third slots and raw F3*Q3^4
allowance are consumed internally. It constructs the whole-Y fine graph
and proves its normalized total; no desired total/profile is an input.
The old cost/population trace is retained in the baseline admission fields. -/
theorem exists_actual_total_mass (E zeta53 chi window eB c3 menuTax : ℝ)
    (hE : 0 < E) (_hzeta53 : 0 < zeta53) (hzetaSmall : zeta53 ≤ E/16384)
    (hchi : 0 < chi) (hw : 0 < window) (heB : 0 < eB) (hc3 : 0 ≤ c3)
    (hmenuTax : 0 < menuTax)
    (htax : 5*eB/16+2*c3+menuTax ≤ (window*chi/2)*(E/16384)) (bins : ℕ) :
    ∃ eps0 : ℝ, 0 < eps0 ∧ ∀ (n : ℕ) (D : FiniteScaleSource n) (eta : ℝ)
      (h : IsWangZakharovNativeFiniteInput D eta)
      (original : Fin n → Finset Index) (R : Finset (Fin n)) (level : ℕ)
      (a zeta : ℝ), 0 ≤ zeta → HasOriginalBackbone D original R a level zeta →
      ∀ (Eref H T : Finset (Fin n × Index)) (m : ℕ), 6 ≤ m → D.thickness ≤ (rho m)^2 →
      ∀ (p : Parent) (etaRef : ℝ)
        (href : IsWangZakharovNativeFiniteInput (source h R Eref a m p) etaRef),
      T ⊆ Eref → Eref ⊆ incidences original →
      (∀ z ∈ T, z.1 ∈ parentLabels D R a (2 ^ m) p) →
      (source h R Eref a m p).thickness ≤ eps0 → etaRef ≤ window * eB / 256 →
      (64 : ℝ) ^ 3 * (source h R Eref a m p).thickness ^ (window * eB / 16) ≤ D.thickness ^ zeta →
      ∀ population cost : ℝ, 0 < population → 0 < cost →
        population * (parentLabels D R a (2 ^ m) p).card ≤ D.thickness * H.card →
        (H.card : ℝ) ≤ cost * T.card →
      ∀ u : ℕ, m + (u+12) ≤ level →
        64 / ((2 ^ (u+12) : ℕ) : ℝ) ≤ (source h R Eref a m p).thickness ^ window →
        retentionFactor cost population ≤ (64 / ((2 ^ (u+12) : ℕ) : ℝ)) ^ (-(eB / 32)) →
      ∀ (P : Submodule ℝ E4) (hP : P ≤ heightKernel)
        (hd : Module.finrank ℝ P = 1)
        (F Fcfg : ℤ → Matrix (Fin 2) (Fin 1) ℝ),
      (∀ t u v, |F t u v| ≤ 1 / 4) → (∀ t u v, |Fcfg t u v| ≤ 1 / 4) →
      ∀ (R0 : ℕ), 0 < R0 → rho m ≤ mu m * (R0 : ℝ) →
        mu m * (R0 : ℝ) = 4096 / ((2 ^ (u+12) : ℕ) : ℝ) →
      ∀(d Q F3 : ℕ)
        (extra : Fin d → (Fin n × Index) → (Fin n × Index) → Prop),
      1 ≤ F3 → (F3:ℝ)*(Q:ℝ)^4 ≤ D.thickness^(-c3) →
      (∀j x y,x∈T → y∈T →
        degree (fun _ : Fin n × Index => 1)
          (completeRelations D a m p .oneTwo P hP hd F Fcfg R0 u extra j) T x ≤
        Q^2*degree (fun _ : Fin n × Index => 1)
          (completeRelations D a m p .oneTwo P hP hd F Fcfg R0 u extra j) T y) →
      let key:=fun z : Fin n × Index => coarseYKey D a m p .oneTwo P hP hd F Fcfg R0 z.2
      let cfg:=NativeActualConfiguredPoint.point D a m p .oneTwo P hP hd F Fcfg R0
      let graph:=fun z : Fin n × Index => (cfg z.2,outputTube h R Eref a m (u+12) p href z.1)
      ∀t : ℝ,
      ∀(W : ∀height : {height : ℤ // height∈(T.image key).image Prod.fst},
        HeightAlignment (T.image key) u t zeta53 chi height.val)
        (bin : ℝ → Fin (bins+1)),
      ∃c : NativeYCommonScaleSelection.Menu u bins,∃selected : Finset Key,
        selected⊆T.image key ∧ selected.Nonempty ∧
        let eps:=64/((2^(u+12):ℕ):ℝ)
        let Ycut:=T.filter (fun z => key z∈selected)
        0 < localSigma c ∧
        localSigma c ≤ (source h R Eref a m p).thickness^(window*chi/2) ∧
        (localSigma c)^(E/4096) ≤ eps^4*((Ycut.image graph).card:ℝ) ∧
        (∀b : ℕ,b ≤ u+12 →
          (localSigma c)^(E/4096) ≤ eps^4*
            (∑q∈(univ : Finset (Fin (parentLabels D R a (2^m) p).card)).image
              (parentLabel (source h R Eref a m p) 0 (2^b)),
                NativeSameQFineGraph.weight h R Eref a m (u+12) b p href cfg Ycut q)) ∧
        ∀height∈selected.image Prod.fst,∃hh : height∈(T.image key).image Prod.fst,
          (W ⟨height,hh⟩).chart=c.1 ∧ (W ⟨height,hh⟩).rhoDepth=c.2.1 ∧
          (W ⟨height,hh⟩).tauDepth=c.2.2.1 ∧ bin (W ⟨height,hh⟩).exponent=c.2.2.2 ∧
          heightPoints selected ((2:ℝ)⁻¹^u/512) height=(W ⟨height,hh⟩).selected := by
  obtain ⟨rCut,hrCut,hrCut1,Hcut⟩:=exists_total_cutoff E zeta53 chi window menuTax hE hchi hw hmenuTax bins
  obtain ⟨baseCut,hbaseCut,Hsource⟩:=exists_actual_common_mass eB window heB hw
  refine ⟨min rCut baseCut,lt_min hrCut hbaseCut,?_⟩
  intro n D eta h original R level a zeta hzeta HB Eref H T m hm hscale p etaRef href
    hTE hEorig hparent hsmall heta hprofile population cost hpop hcost hpopulation hretain
    u hmb hwindow hpaid P hP hd F Fcfg hF hCfg R0 hR0 hbase hmatch
    d Q F3 extra hF3 H3 Hrel key cfg graph t W bin
  have hsBase:=(hsmall.trans (min_le_right rCut baseCut))
  obtain ⟨c,selected,hsel,hsn,hMass,hwhole⟩:=
    Hsource n D eta h original R level a zeta hzeta HB Eref H T m hm p etaRef href
      hTE hEorig hparent hsBase heta hprofile population cost hpop hcost hpopulation hretain
      u hmb hwindow hpaid P hP hd F Fcfg hF hCfg R0 hR0 hbase hmatch
      d bins Q extra Hrel t zeta53 chi W bin
  let r:ℝ:=(source h R Eref a m p).thickness
  let eps:ℝ:=64/((2^(u+12):ℕ):ℝ)
  let N:ℝ:=2*((u+10:ℕ):ℝ)^2*((bins+1:ℕ):ℝ)
  let Ycut:=T.filter (fun z => key z∈selected)
  let deltaY:ℝ:=(2:ℝ)⁻¹^u/512
  have hr : 0 < r:=href.1.2.1
  have hrSmall : r ≤ rCut:=hsmall.trans (min_le_left _ _)
  have hr1 : r ≤ 1:=hrSmall.trans hrCut1
  have heps : 0 < eps:=by dsimp [eps]; positivity
  have hFine:=source_scale_guard h R Eref level m (u+12) p HB.2.1 hmb
  have hrEps : r ≤ eps := by
    have hh : r ≤ 1/((2^(u+12):ℕ):ℝ) :=
      (le_div_iff₀ (by positivity)).mpr (by simpa only [mul_comm] using hFine)
    exact hh.trans (div_le_div_of_nonneg_right (by norm_num : (1:ℝ)≤64) (by positivity))
  have hCut:=Hcut r hr hrSmall
  have hMenu : N ≤ r^(-menuTax) := by
    apply hCut.2.2 u
    · simpa only [eps,fine_mesh_eq] using hrEps
    · simpa only [eps,fine_mesh_eq] using hwindow
  have hQ:=radix_cost_from_raw F3 Q hF3 hr hc3
    (source_thickness_sq_le_original h R Eref m p hscale) H3
  obtain ⟨z,hz⟩:=hsn
  obtain ⟨hh,_hchart,hRho,hTau,_hbin,_hPoints⟩:=hwhole z.1 (mem_image_of_mem Prod.fst hz)
  let V:=W ⟨z.1,hh⟩
  have hgap:=V.gap
  change V.rhoDepth=c.2.1 at hRho
  change V.tauDepth=c.2.2.1 at hTau
  change deltaY^(-chi) ≤ scale deltaY V.tauDepth.val/scale deltaY V.rhoDepth.val at hgap
  rw [hRho,hTau] at hgap
  have hdelta : deltaY=eps/8:=input_mesh_eq u
  have hSigma : localSigma c ≤ r^(window*chi/2) := by
    have hg:=local_sigma_from_gap hr heps
      (by dsimp [scale,deltaY]; positivity : 0 < scale deltaY c.2.1.val)
      (by dsimp [scale,deltaY]; positivity : 0 < scale deltaY c.2.2.1.val)
      hchi (by rwa [←hdelta]) hwindow hCut.1
    have heq : localSigma c=32768*scale deltaY c.2.1.val/scale deltaY c.2.2.1.val := by
      unfold localSigma
      rw [show 32768*scale deltaY c.2.1.val/scale deltaY c.2.2.1.val=
        32768*(scale deltaY c.2.1.val/scale deltaY c.2.2.1.val) by ring,
        scale_ratio (by dsimp [deltaY]; positivity)]
    rwa [←heq] at hg
  have hsigma:=localSigma_pos c
  have hTotal:=pay_actual_graph_mass Q hr hr1 hrEps hsigma hE hzetaSmall heB.le
    (by positivity : 0 < window*chi/2) htax hMenu hQ hSigma hCut.2.1
    (Nat.cast_nonneg ((Ycut.image graph).card)) hMass
  refine ⟨c,selected,hsel,hsn,hsigma,hSigma,hTotal,?_,hwhole⟩
  intro b hb
  have hYP : ∀z∈Ycut,z.1∈parentLabels D R a (2^m) p :=
    fun z hz => hparent z (mem_filter.mp hz).1
  rw [NativeSameQFineGraph.total_weight_eq_graph h R Eref Ycut a m (u+12) b hb p href cfg hYP]
  exact hTotal

end NativeActualYTotalMass
