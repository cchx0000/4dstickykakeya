import Theorems.Thm_StickyKakeya4_native_htotal_implementation
import Theorems.Thm_StickyKakeya4_native_actual_raw_weight_source
import Theorems.Thm_StickyKakeya4_native_actual_final_third_total_mass
/- Combined original-incidence total after the actual Y selection. Consult receipts for verification. -/

/- Frozen origin: Thm_StickyKakeya4_native_raw_whole_Y_retention.lean; SHA256 060f0d402d1c1f9e640ef984956638a4ae2a265ec0189dda6b9a40aca260c09c. -/

/- Original-incidence retention through the literal planar Y selection.
Originally drafted without verification; consult current receipts. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 3500000
noncomputable section
namespace NativeRawWholeYRetention
open Classical Finset NativeJointUniformCoarseRelations NativeConfiguredYWeightedRetention
open NativeLiteralYHeightAlignment NativeWholeYGraphRetention NativeYTotalEpsilonBudget
open scoped BigOperators

/-- The common class is selected using the actual planar witnesses and
original Y cardinalities. Only the installed Y-key radix is charged. -/
theorem select_actual_common_edges {A P : Type*} [DecidableEq A] [DecidableEq P]
    (T : Finset A) (hT : T.Nonempty) (point : A → P) (key : P → Key) (Q : ℕ)
    (HY : HasUniformFibers T Q (fun z => key (point z)))
    (u bins : ℕ) (t zeta chi : ℝ)
    (W : ∀h : {h : ℤ // h∈(T.image (fun z => key (point z))).image Prod.fst},
      HeightAlignment (T.image (fun z => key (point z))) u t zeta chi h.val)
    (bin : ℝ → Fin (bins+1)) :
    ∃c : NativeYCommonScaleSelection.Menu u bins,∃selected : Finset Key,
      selected⊆T.image (fun z => key (point z)) ∧ selected.Nonempty ∧
      let U := T.filter (fun z => key (point z)∈selected)
      menuFraction zeta c/(2*((u+10:ℕ):ℝ)^2*((bins+1:ℕ):ℝ))*(T.card:ℝ) ≤
        (Q:ℝ)^2*(U.card:ℝ) ∧
      U⊆T ∧ U.Nonempty ∧
      (∀p∈U.image point,U.filter (fun z => point z=p)=T.filter (fun z => point z=p)) ∧
      ∀h∈selected.image Prod.fst,∃hh : h∈(T.image (fun z => key (point z))).image Prod.fst,
        (W ⟨h,hh⟩).chart=c.1 ∧ (W ⟨h,hh⟩).rhoDepth=c.2.1 ∧
        (W ⟨h,hh⟩).tauDepth=c.2.2.1 ∧ bin (W ⟨h,hh⟩).exponent=c.2.2.2 ∧
        heightPoints selected ((2:ℝ)⁻¹^u/512) h=(W ⟨h,hh⟩).selected := by
  let f := fun z => key (point z)
  obtain ⟨c,selected,hsel,hsn,hret,hwhole⟩ :=
    select_aligned_common (T.image f) (hT.image f) u bins t zeta chi W bin
  let N : ℝ := 2*((u+10:ℕ):ℝ)^2*((bins+1:ℕ):ℝ)
  have hN : 0 < N := by dsimp [N]; positivity
  have hf : 0 < menuFraction zeta c := by unfold menuFraction; positivity
  have hret' : menuFraction zeta c*((T.image f).card:ℝ) ≤ N*(selected.card:ℝ) := by
    convert hret using 1
  have hfrac : menuFraction zeta c/N*((T.image f).card:ℝ) ≤ (selected.card:ℝ) := by
    have hh := (div_le_iff₀ hN).mpr (by simpa only [mul_comm] using hret')
    convert hh using 1
    ring
  have hm := uniform_subset_retention T f Q HY selected hsel
    (menuFraction zeta c/N) (div_nonneg hf.le hN.le) hfrac
  let U := T.filter (fun z => f z∈selected)
  have hUn : U.Nonempty := by
    obtain ⟨y,hy⟩ := hsn
    obtain ⟨z,hz,hzy⟩ := mem_image.mp (hsel hy)
    exact ⟨z,mem_filter.mpr ⟨hz,by rw [hzy]; exact hy⟩⟩
  refine ⟨c,selected,hsel,hsn,hm,filter_subset _ _,hUn,?_,hwhole⟩
  intro p hp
  obtain ⟨z,hz,hzp⟩ := mem_image.mp hp
  have hzsel := (mem_filter.mp hz).2
  ext w
  simp only [U,mem_filter]
  constructor
  · exact fun hw => ⟨hw.1.1,hw.2⟩
  · rintro ⟨hw,hwp⟩
    refine ⟨⟨hw,?_⟩,hwp⟩
    simpa only [f,hwp,hzp] using hzsel

/-- Normalize the actual original-edge retention; using Q^4 here is an
explicit conservative weakening of the sharper Q^2 supplied above. -/
theorem normalized_mass_transfer {nu eps sigma zeta eB N : ℝ}
    (Q : ℕ) (hQ : 1 ≤ Q) (T U : ℕ)
    (hnu : 0 ≤ nu) (hsigma : 0 < sigma) (hN : 0 < N)
    (Hbase : (16/(5:ℝ)^4)*eps^(5*eB/16) ≤ nu*T)
    (Hret : (sigma/32768)^zeta/N*(T:ℝ) ≤ (Q:ℝ)^2*(U:ℝ)) :
    (16/(5:ℝ)^4)*(sigma/32768)^zeta*eps^(5*eB/16) ≤ N*(Q:ℝ)^4*(nu*U) := by
  have hfrac : 0 ≤ (sigma/32768)^zeta := by positivity
  have hQr : (1:ℝ) ≤ Q := by exact_mod_cast hQ
  have hPow : (Q:ℝ)^2 ≤ (Q:ℝ)^4 := pow_le_pow_right₀ hQr (by decide)
  have hmass := mul_le_mul_of_nonneg_left Hret (mul_nonneg hnu hN.le)
  have hmass' : (sigma/32768)^zeta*(nu*T) ≤ N*(Q:ℝ)^2*(nu*U) := by
    convert hmass using 1 <;> field_simp [hN.ne'] <;> ring
  calc
    _ = (sigma/32768)^zeta*((16/(5:ℝ)^4)*eps^(5*eB/16)) := by ring
    _ ≤ (sigma/32768)^zeta*(nu*T) := mul_le_mul_of_nonneg_left Hbase hfrac
    _ ≤ N*(Q:ℝ)^2*(nu*U) := hmass'
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hPow hN.le)
      (mul_nonneg hnu (Nat.cast_nonneg U))

/-- The existing epsilon budget pays the normalized raw total itself.
The temporary division by eps^4 is purely scalar and cancels exactly. -/
theorem pay_raw_mass_at_epsilon {eps sigma E zeta53 eB c3 window menuTax N mass : ℝ}
    (Q : ℕ) (heps : 0 < eps) (heps1 : eps ≤ 1)
    (hs : 0 < sigma) (hE : 0 < E) (hzeta : zeta53 ≤ E/16384)
    (heB : 0 ≤ eB) (chi : ℝ) (hchi : 0 < chi)
    (htax : 5*eB/16+2*c3/window+menuTax ≤ (chi/2)*(E/16384))
    (hMenu : N ≤ eps^(-menuTax)) (hQ : (Q:ℝ)^4 ≤ eps^(-(2*c3/window)))
    (hSigma : sigma ≤ eps^(chi/2))
    (hfixed : ((5:ℝ)^4*(32768:ℝ)^zeta53/16)*eps^((chi/2)*(E/8192)) ≤ 1)
    (hmass : 0 ≤ mass)
    (Hsource : (16/(5:ℝ)^4)*(sigma/32768)^zeta53*eps^(5*eB/16) ≤ N*(Q:ℝ)^4*mass) :
    sigma^(E/4096) ≤ mass := by
  have hCancel : eps^4*(mass/eps^4)=mass := by field_simp [heps.ne']
  have Hsource' : (16/(5:ℝ)^4)*(sigma/32768)^zeta53*eps^(5*eB/16) ≤
      N*(Q:ℝ)^4*eps^4*(mass/eps^4) := by
    calc
      _ ≤ N*(Q:ℝ)^4*mass := Hsource
      _ = _ := by rw [mul_assoc (N*(Q:ℝ)^4),hCancel]
  have hh := pay_actual_graph_mass_at_epsilon Q heps heps1 hs hE hzeta heB chi hchi
    htax hMenu hQ hSigma hfixed (div_nonneg hmass (pow_nonneg heps.le 4)) Hsource'
  simpa only [hCancel] using hh

end NativeRawWholeYRetention
end -- original anonymous section NativeRawWholeYRetention

/- Frozen origin: Thm_StickyKakeya4_native_actual_raw_Y_total_mass.lean; SHA256 e6a3656a9c53278c9448b417e67fcf8f23303a42790fed8bb74c5b6835b02eab. -/

/- Actual raw-incidence total after the literal common planar selection.
Originally drafted without verification; consult current receipts. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 6000000
noncomputable section
namespace NativeActualRawYTotalMass
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeLocalParentSource NativeReferenceXYGridPoints NativeHorizontalGrainSlice
open NativeConfiguredThirdRelation NativeJointUniformCoarseRelations NativeFiniteSliceHomogeneity
open NativeRawWholeYRetention NativeWholeYGraphRetention NativeLiteralYHeightAlignment
open NativeCommonYTotalBudget NativeYTotalEpsilonBudget NativeActualSparseReferenceAdmission
open NativeActualRawWeightSource NativeOriginalIncidenceMassLower SelfUniform
open scoped BigOperators Matrix.Norms.Elementwise

/-- The admitted SAME reference and actual Hp-to-T0 retention supply the raw
baseline internally. The returned Ycut keeps whole old-point fibers and pays
only the already installed coarse-Y radix; no total-mass premise is supplied. -/
theorem exists_actual_raw_total (E zeta53 chi window eB c3 menuTax : ℝ)
    (hE : 0 < E) (hzetaSmall : zeta53 ≤ E/16384)
    (hchi : 0 < chi) (hw : 0 < window) (heB : 0 < eB) (hc3 : 0 ≤ c3)
    (hmenuTax : 0 < menuTax)
    (htax : 5*eB/16+2*c3/window+menuTax ≤ (chi/2)*(E/16384)) (bins : ℕ) :
    ∃rCut : ℝ,0 < rCut ∧ ∀(n : ℕ) (D : FiniteScaleSource n) (eta a : ℝ)
      (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
      (Eref Hp T : Finset (Fin n × Index)) (m : ℕ) (p : Parent) (etaRef : ℝ)
      (href : IsWangZakharovNativeFiniteInput (source h R Eref a m p) etaRef),
      D.thickness ≤ (rho m)^2 → (source h R Eref a m p).thickness ≤ rCut →
      etaRef ≤ window*eB/256 →
      ∀population cost : ℝ,0 < population → 0 < cost →
      population*(parentLabels D R a (2^m) p).card ≤ D.thickness*Hp.card →
      (Hp.card:ℝ) ≤ cost*T.card →
      ∀u : ℕ,64/((2^(u+12):ℕ):ℝ) ≤ (source h R Eref a m p).thickness^window →
      retentionFactor cost population ≤ (64/((2^(u+12):ℕ):ℝ))^(-(eB/32)) →
      ∀(P : Submodule ℝ E4) (hP : P≤heightKernel) (hd : Module.finrank ℝ P=1)
        (F Fcfg : ℤ → Matrix (Fin 2) (Fin 1) ℝ) (R0 d Q F3 : ℕ)
        (extra : Fin d → (Fin n × Index) → (Fin n × Index) → Prop),
      1 ≤ F3 → 1 ≤ Q → (F3:ℝ)*(Q:ℝ)^4 ≤ D.thickness^(-c3) →
      (∀j x y,x∈T → y∈T →
        degree (fun _ : Fin n × Index => 1)
          (completeRelations D a m p .oneTwo P hP hd F Fcfg R0 u extra j) T x ≤
        Q^2*degree (fun _ : Fin n × Index => 1)
          (completeRelations D a m p .oneTwo P hP hd F Fcfg R0 u extra j) T y) →
      let key := fun z : Fin n × Index => coarseYKey D a m p .oneTwo P hP hd F Fcfg R0 z.2
      ∀t : ℝ,∀(W : ∀height : {height : ℤ // height∈(T.image key).image Prod.fst},
        HeightAlignment (T.image key) u t zeta53 chi height.val)
        (bin : ℝ → Fin (bins+1)),
      ∃c : NativeYCommonScaleSelection.Menu u bins,∃selected : Finset Key,
        selected⊆T.image key ∧ selected.Nonempty ∧
        let Ycut := T.filter (fun z => key z∈selected)
        0 < localSigma c ∧
        localSigma c ≤ (source h R Eref a m p).thickness^(window*chi/2) ∧
        4096*(64/((2^(u+12):ℕ):ℝ)) ≤ localSigma c ∧
        (localSigma c)^(E/4096) ≤ normalization D m*(Ycut.card:ℝ) ∧
        Ycut⊆T ∧ Ycut.Nonempty ∧
        (∀k∈Ycut.image Prod.snd,Ycut.filter (fun z => z.2=k)=T.filter (fun z => z.2=k)) ∧
        ∀height∈selected.image Prod.fst,∃hh : height∈(T.image key).image Prod.fst,
          (W ⟨height,hh⟩).chart=c.1 ∧ (W ⟨height,hh⟩).rhoDepth=c.2.1 ∧
          (W ⟨height,hh⟩).tauDepth=c.2.2.1 ∧ bin (W ⟨height,hh⟩).exponent=c.2.2.2 ∧
          heightPoints selected ((2:ℝ)⁻¹^u/512) height=(W ⟨height,hh⟩).selected := by
  obtain ⟨epsCut,hepsCut,hepsCut1,Hcut⟩ := exists_epsilon_cutoff E zeta53 chi menuTax hE hchi hmenuTax bins
  obtain ⟨rCut,hrCut,_hrCut1,Hpull⟩ := NativeQuarterScaleParameters.exists_small_power_cutoff hw hepsCut
  refine ⟨rCut,hrCut,?_⟩
  intro n D eta a h R Eref Hp T m p etaRef href hscale hsmall heta population cost
    hpop hcost hpopulation hretain u hwindow hpaid P hP hd F Fcfg R0 d Q F3 extra
    hF3 hQone H3 Hrel key t W bin
  let r : ℝ := (source h R Eref a m p).thickness
  let eps : ℝ := 64/((2^(u+12):ℕ):ℝ)
  let N : ℝ := 2*((u+10:ℕ):ℝ)^2*((bins+1:ℕ):ℝ)
  let deltaY : ℝ := (2:ℝ)⁻¹^u/512
  let nu : ℝ := normalization D m
  have hr : 0 < r := href.1.2.1
  have heps : 0 < eps := by dsimp [eps]; positivity
  have hepsSmall : eps ≤ epsCut := hwindow.trans (Hpull r hr hsmall)
  have heps1 : eps ≤ 1 := hepsSmall.trans hepsCut1
  have hNu : nu=D.thickness*r^3 := by dsimp only [nu,normalization,r]; rw [source_thickness]
  have hNu0 : 0 < nu := by rw [hNu]; exact mul_pos h.1.2.1 (pow_pos hr 3)
  have hRaw := paid_raw_cardinality_lower h R Eref Hp T m p href population cost
    hpop hcost hpopulation hretain eps eB window heps heB hw heta hwindow hpaid
  have hConstant : (16/(5:ℝ)^4) ≤ retentionConstant := by
    unfold retentionConstant NativeOriginalPrunedMass.volumeConstant
    have hh := Real.pi_gt_three
    nlinarith only [hh,sq_nonneg (Real.pi-3)]
  have hConstantPos : 0 < retentionConstant := lt_of_lt_of_le (by norm_num) hConstant
  have hWeak : (16/(5:ℝ)^4)*eps^(5*eB/16) ≤ nu*(T.card:ℝ) := by
    have hp := Real.rpow_le_rpow_of_exponent_ge heps heps1
      (show 9*eB/256 ≤ 5*eB/16 by linarith only [heB])
    have hc := mul_le_mul hConstant hp (Real.rpow_nonneg heps.le _) hConstantPos.le
    exact hc.trans (by simpa only [hNu] using hRaw)
  have hT : T.Nonempty := by
    by_contra hn
    have hz := not_nonempty_iff_eq_empty.mp hn
    rw [hz,card_empty,Nat.cast_zero,mul_zero] at hWeak
    have hp : 0 < (16/(5:ℝ)^4)*eps^(5*eB/16) := by positivity
    exact (not_le_of_gt hp) hWeak
  have HY : HasUniformFibers T Q key := by
    intro x hx y hy
    have hh := Hrel 0 x y hx hy
    change degree (fun _ : Fin n × Index => 1) (fun x y => key x=key y) T x ≤
      Q^2*degree (fun _ : Fin n × Index => 1) (fun x y => key x=key y) T y at hh
    simpa only [unit_degree_eq_fiber] using hh
  obtain ⟨c,selected,hsel,hsn,hMass,hYT,hYn,hFibers,hwhole⟩ :=
    select_actual_common_edges T hT Prod.snd (coarseYKey D a m p .oneTwo P hP hd F Fcfg R0)
      Q HY u bins t zeta53 chi W bin
  let Ycut := T.filter (fun z => key z∈selected)
  have hCut := Hcut eps heps hepsSmall
  have hMenu : N ≤ eps^(-menuTax) := hCut.2.2 u (fine_mesh_eq u)
  have hQr := radix_cost_from_raw F3 Q hF3 hr hc3
    (source_thickness_sq_le_original (a:=a) h R Eref m p hscale) H3
  have hQ := radix_cost_at_epsilon Q hr heps hw hc3 hwindow hQr
  have hsnSaved := hsn
  obtain ⟨z,hz⟩:=hsn
  obtain ⟨hh,_hchart,hRho,hTau,_hbin,_hPoints⟩:=hwhole z.1 (mem_image_of_mem Prod.fst hz)
  let V:=W ⟨z.1,hh⟩
  have hgap:=V.gap
  change V.rhoDepth=c.2.1 at hRho
  change V.tauDepth=c.2.2.1 at hTau
  change deltaY^(-chi) ≤ scale deltaY V.tauDepth.val/scale deltaY V.rhoDepth.val at hgap
  rw [hRho,hTau] at hgap
  have hdelta : deltaY=eps/8:=input_mesh_eq u
  have hSigmaEps : localSigma c ≤ eps^(chi/2) := by
    have hg:=local_sigma_from_gap (r:=eps) (window:=1) heps heps
      (by dsimp [scale,deltaY]; positivity : 0 < scale deltaY c.2.1.val)
      (by dsimp [scale,deltaY]; positivity : 0 < scale deltaY c.2.2.1.val)
      hchi (by rwa [←hdelta]) (by rw [Real.rpow_one])
      (by simpa only [one_mul] using hCut.1)
    have heq : localSigma c=32768*scale deltaY c.2.1.val/scale deltaY c.2.2.1.val := by
      unfold localSigma
      rw [show 32768*scale deltaY c.2.1.val/scale deltaY c.2.2.1.val=
        32768*(scale deltaY c.2.1.val/scale deltaY c.2.2.1.val) by ring,
        NativeLiteralYHeightAlignment.scale_ratio (by dsimp [deltaY]; positivity) c.2.1.val c.2.2.1.val]
    simpa only [←heq,one_mul] using hg
  have hSigma : localSigma c ≤ r^(window*chi/2) := by
    have hh:=Real.rpow_le_rpow heps.le hwindow (show 0 ≤ chi/2 by positivity)
    rw [←Real.rpow_mul hr.le] at hh
    have he : window*(chi/2)=window*chi/2 := by ring
    simpa only [he] using hSigmaEps.trans hh
  have hsigma:=localSigma_pos c
  have hSigmaLower : 4096*eps ≤ localSigma c := by
    have hLow := V.scale_lower
    have hHigh := V.scale_upper
    change deltaY ≤ scale deltaY V.rhoDepth.val at hLow
    change scale deltaY V.tauDepth.val ≤ 1 at hHigh
    rw [hRho] at hLow
    rw [hTau] at hHigh
    have hDen : 0 < scale deltaY c.2.2.1.val := by dsimp [scale,deltaY]; positivity
    have hRatio : deltaY ≤ scale deltaY c.2.1.val/scale deltaY c.2.2.1.val := by
      apply (le_div_iff₀ hDen).mpr
      exact (mul_le_of_le_one_right (by dsimp [deltaY]; positivity) hHigh).trans hLow
    have hh := mul_le_mul_of_nonneg_left hRatio (by norm_num : (0:ℝ)≤32768)
    rw [NativeLiteralYHeightAlignment.scale_ratio (by dsimp [deltaY]; positivity)] at hh
    change 32768*deltaY ≤ localSigma c at hh
    rw [hdelta] at hh
    linarith only [hh]
  have hMass' : (16/(5:ℝ)^4)*(localSigma c/32768)^zeta53*eps^(5*eB/16) ≤
      N*(Q:ℝ)^4*(nu*Ycut.card) := by
    apply normalized_mass_transfer Q hQone T.card Ycut.card hNu0.le hsigma (by dsimp [N]; positivity) hWeak
    simpa only [fraction_eq_localSigma] using hMass
  have hTotal := pay_raw_mass_at_epsilon Q heps heps1 hsigma hE hzetaSmall heB.le chi hchi
    htax hMenu hQ hSigmaEps hCut.2.1 (mul_nonneg hNu0.le (Nat.cast_nonneg _)) hMass'
  exact ⟨c,selected,hsel,hsnSaved,hsigma,hSigma,hSigmaLower,hTotal,hYT,hYn,hFibers,hwhole⟩

end NativeActualRawYTotalMass
end -- original anonymous section NativeActualRawYTotalMass

/- Frozen origin: Thm_StickyKakeya4_native_actual_raw_third_total_mass.lean; SHA256 5efc5b63cef79b57e64d2658c345da489589ac9337d9aa8c34b9629ee78413f5. -/

/- The raw total paid from the actual final third-core source record.
Originally drafted without verification; consult current receipts. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 12000000
noncomputable section
namespace NativeActualRawThirdTotalMass
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeActualPaidPlanarAlignment NativeActualYEpsilonTotalMass NativeActualBaselineRetentionPayment
open NativePaidThirdRecordReadback NativePaidThirdRecord NativePaidThirdBudget NativeThirdXYSourceData
open NativeRetainedSliceCore NativeRetainedSliceBudgetAlgebra NativeReferenceSliceBudgetAlgebra
open NativeActualNewCutBudget NativeNewCutOutputBudget NativeFinestYOutputBudget
open NativeReferenceXYGridPoints NativeReferenceXYGridField NativeReferenceXYGridMaps
open NativeHorizontalGrainSlice NativeGrainQuotientFibers NativeTranslatedGrainHeightOverlap
open NativeEncodedQuotientAD NativeFixedCompactKakeyaExponent NativeRankExponentHierarchy
open NativeParentHeightGraphCore NativeActivePhasePopulation NativeAllTwoScaleConfiguration
open NativeSingleHeightCoarseYAD NativeLiteralYHeightAlignment NativeConfiguredThirdRelation
open NativeActualSparseReferenceAdmission NativeLocalParentSource NativeOriginalParentDensityCore
open NativeMiddleWindowBalance NativeCubicalIncidenceCounts
open NativeWholeYGraphRetention NativeConfiguredIncidenceFibers NativeCommonYTotalBudget SelfUniform
open NativeSharpXPowerAlgebra NativeSquaredGrainQueries NativeThirdXYData
open scoped BigOperators Matrix.Norms.Elementwise

open NativeActualRawYTotalMass

/-- The old-edge baseline payment is computed from the SAME H1/H2/H3,
Hp and final U/T record. The actual planar family is preserved verbatim. -/
theorem exists_raw_total_supplier (totalLoss zeta53 chi window eB menuTax eta0 c epsilonQ : ℝ)
    (hLossTotal : 0 < totalLoss) (hzetaSmall : zeta53 ≤ totalLoss/16384)
    (hchi : 0 < chi) (hw : 0 < window) (heB : 0 < eB) (hMenuTax : 0 < menuTax)
    (he0 : 0 < eta0) (he01 : eta0 ≤ 1) (hc : 0 < c) (hc1 : c ≤ 1)
    (heQ : 0 < epsilonQ) (heQ1 : epsilonQ ≤ 1) (heQSmall : eta0 ≤ epsilonQ) (hcQ : c ≤ epsilonQ/24)
    (hTax : 5*eB/16+2*(commonBudget eta0 c/4)/window+menuTax ≤ (chi/2)*(totalLoss/16384))
    (Kcoh Ksupport g K bins : ℕ) (meshConstant row : ℝ) (hC : 0 ≤ meshConstant) (hrow : 0 ≤ row) :
    ∃epsCut rCut : ℝ,0 < epsCut ∧ epsCut ≤ 1 ∧ 0 < rCut ∧
    ∀ {epsilon delta0 : ℝ} {dExtra J L3 n : ℕ}
    {D : FiniteScaleSource n} {eta : ℝ}
    (Hbudget : HasBudget epsilon eta0 c g K (dExtra+3) J L3 delta0)
    (h : IsWangZakharovNativeFiniteInput D eta) (hsmall : D.thickness ≤ delta0) (heta : 0 ≤ eta)
    (original : Fin n → Finset Index) (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (S : Finset (Fin n × Index)) (hS : S⊆incidences original) (hSn : S.Nonempty)
    (F1 F2 G Q1 Q2 m : ℕ) (hF1 : 0 < F1) (hG : 0 < G) (hQ1 : 1 ≤ Q1) (hQ2 : 0 < Q2)
    (hGF : G ≤ F2) (hm12 : 12 ≤ m) 
    (zeta lambda b tau seed c2 r q : ℝ)
    (hetaSeed : eta ≤ seed/8) (htau0 : 0 ≤ tau) (htau : tau ≤ commonBudget eta0 c/1024)
    (hseed : seed ≤ tau/16384) (hc2 : c2=commonBudget eta0 c/4)
    (H1 : (125*175616*16384:ℝ)*(F1:ℝ)*(Q1:ℝ)^2*D.thickness^(-eta) ≤ D.thickness^(-(seed/8)))
    (H2 : (125*175616*16384:ℝ)*(F2:ℝ)*(Q2:ℝ)^2*D.thickness^(-eta) ≤ D.thickness^(-c2))
    (hr : 0 < r) (hr1 : r ≤ 1) (hrdelta : r ≤ D.thickness^(cutoff c (1:Fin 4)))
    (hlambda : lambda=r^(rankLoss eta0 c (1:Fin 4))/(4*((g:ℝ)+1)))
    (hb : r^((2*((2:ℕ):ℝ)+1)*rankLoss eta0 c (1:Fin 4)) ≤ b)
    (hq : 0 < q) (hq1 : q ≤ 1)
    (hgrid : 1/(g:ℝ) < NativeActualMesoscopicRankConfiguration.rankWindow tau/4)
    (hqraw : r^(2*c)/(2*D.thickness^(-(1/(g:ℝ)))) ≤ q)
    (hscale : ((64:ℝ)/((2^m:ℕ):ℝ))^2 ≤ 6144*r)
    (Cpre : ℝ) (hCpre : 0 < Cpre)
    (a : ℝ) (plane : Index → Submodule ℝ E4) (E Hgraph T : Finset (Fin n × Index))
    (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (hdim : Module.finrank ℝ P=2-1)
    (Fraw : ℤ → Matrix (Fin 2) (Fin 1) ℝ)
    (p : Parent) (t : ℝ) (Rel3 : Fin (dExtra+3) → (Fin n × Index) → (Fin n × Index) → Prop)
    (Hdata :
      let F3 := refinementCost ((dExtra+3)+2) (J+1) L3
      let Q3 := NativeSourceSizeBounds.radix S.card L3
      let w := min (boundaryWindow tau) ((tau/16)/1000)
      let pop := population D.thickness eta lambda b F1 G
      let eps := columnEpsilon D.thickness lambda (seed/8) c2
      let CX := (Cpre/quotientCost q)*fiberCoefficient D.thickness eta zeta tau (seed/8) c2 lambda b
        F1 G Q2 F3 Q3 q (2)
      HasThirdXYSourceData (J:=J) D zeta a m plane E Hgraph S T P hP (by omega) (by omega) hdim Fraw p
        pop (profileLower D.thickness pop eps tau (seed/8) w) (profileUpper D.thickness eps tau)
        Q2 (pop/rowConstant) (selectionCost K) Cpre t L3 Rel3 CX)

    (R : Finset (Fin n))
    (Eref Hp : Finset (Fin n × Index)) (etaRef : ℝ)
    (href : IsWangZakharovNativeFiniteInput (source h R Eref a m p) etaRef)
    (hScale : D.thickness ≤ (rho m)^2)
    (hRefSmall : (source h R Eref a m p).thickness ≤ rCut)
    (hEtaRef : etaRef ≤ window*eB/256)
    (hPopulation : population D.thickness eta lambda b F1 G*
      (parentLabels D R a (2^m) p).card ≤ D.thickness*Hp.card)
    (hGraphRet : Hp.card ≤ selectionCost K*Hgraph.card)
    (u R0 : ℕ)
    (hWindow : 64/((2^(u+12):ℕ):ℝ) ≤ (source h R Eref a m p).thickness^window)
    (loss metric epsilonGeom : ℝ) (depths : Fin Kcoh → ℕ)
    (hLoss : 0 ≤ loss) (hmetric : 0 ≤ metric)
    (heGeom : 0 ≤ epsilonGeom) (heGeom4 : epsilonGeom ≤ 1/4)
    (hLip : metric ≤ r^(-2*epsilonGeom))
    (hstopLo : 3072*r ≤ (rho m)^2)
    (hHeight : ((8*R0:ℕ):ℝ) ≤ 1280*((rho m)/64)^(-2*epsilonGeom))
    (hCost : Cpre=quotientCost q*(newCutCharge Kcoh Ksupport 2 g R0 meshConstant row
      r loss (rankLoss eta0 c (1:Fin 4)) metric extremalExponent
      (fun j => 64/((2^(depths j):ℕ):ℝ)):ℝ))
    (hSmall : (64:ℝ)/((2^(u+12):ℕ):ℝ) ≤ epsCut)
    (hShape : 64*((64:ℝ)/((2^(u+12):ℕ):ℝ)) ≤
      2*max ((5/4:ℝ)*(rho m)^(1-2*epsilonGeom)) (rho m))
    (hNu : newExponent Kcoh epsilonGeom loss (rankLoss eta0 c (1:Fin 4)) ≤ 1/2)
    (hBaseMargin : 4*newExponent Kcoh epsilonGeom loss (rankLoss eta0 c (1:Fin 4))+
      2*(18*rankLoss eta0 c (1:Fin 4)+4*epsilonQ/3) ≤ eB/64)
    (Fcfg : ℤ → Matrix (Fin 2) (Fin 1) ℝ)
    (extra : Fin dExtra → (Fin n × Index) → (Fin n × Index) → Prop),
    let Sq := NativeWeightedGrainQuotientGeometry.retained D a m 2 plane Hgraph P hP
      (by norm_num) (by norm_num) hdim (physicalMesh m (phaseDepth m)/8)
    let field := fixedField D a m 2 plane Sq Fraw
    let key := fun z : Fin n × Index => coarseYKey D a m p .oneTwo P hP hdim field Fcfg R0 z.2
    Rel3=completeRelations D a m p .oneTwo P hP hdim field Fcfg R0 u extra →
    ∀W : ∀height : {height : ℤ // height∈(T.image key).image Prod.fst},
      HeightAlignment (T.image key) u (2-extremalExponent) zeta53 chi height.val,
    ∀bin : ℝ → Fin (bins+1),
    ∃menu : NativeYCommonScaleSelection.Menu u bins,∃selected : Finset Key,
      selected⊆T.image key ∧ selected.Nonempty ∧
      let Ycut := T.filter (fun z => key z∈selected)
      0 < localSigma menu ∧
      localSigma menu ≤ (source h R Eref a m p).thickness^(window*chi/2) ∧
      4096*(64/((2^(u+12):ℕ):ℝ)) ≤ localSigma menu ∧
      (localSigma menu)^(totalLoss/4096) ≤ NativeActualRawWeightSource.normalization D m*(Ycut.card:ℝ) ∧
      Ycut⊆T ∧ Ycut.Nonempty ∧
      (∀k∈Ycut.image Prod.snd,Ycut.filter (fun z => z.2=k)=T.filter (fun z => z.2=k)) ∧
      ∀height∈selected.image Prod.fst,∃hh : height∈(T.image key).image Prod.fst,
        (W ⟨height,hh⟩).chart=menu.1 ∧ (W ⟨height,hh⟩).rhoDepth=menu.2.1 ∧
        (W ⟨height,hh⟩).tauDepth=menu.2.2.1 ∧ bin (W ⟨height,hh⟩).exponent=menu.2.2.2 ∧
        heightPoints selected ((2:ℝ)⁻¹^u/512) height=(W ⟨height,hh⟩).selected := by
  obtain ⟨epsBase,hEB,hEB1,Hbase⟩ :=
    exists_actual_retention_cutoff eB heB Kcoh Ksupport g K meshConstant row hC hrow
  obtain ⟨rCut,hRC,Hmass⟩ := NativeActualRawYTotalMass.exists_actual_raw_total
    totalLoss zeta53 chi window eB (commonBudget eta0 c/4) menuTax hLossTotal hzetaSmall
    hchi hw heB (div_nonneg (commonBudget_pos he0 hc).le (by norm_num)) hMenuTax hTax bins
  refine ⟨epsBase,rCut,hEB,hEB1,hRC,?_⟩
  intro epsilon delta0 dExtra J L3 n D eta Hbudget h hsmall heta original horiginal
    S hS hSn F1 F2 G Q1 Q2 m hF1 hG hQ1 hQ2 hGF hm12
    zeta lambda b tau seed c2 r q hetaSeed htau0 htau hseed hc2 H1 H2
    hr hr1 hrdelta hlambda hb hq hq1 hgrid hqraw hscale Cpre hCpre a plane E Hgraph T
    P hP hdim Fraw p t Rel3 Hdata R Eref Hp etaRef href
    hScale hRefSmall hEtaRef hPopulation hGraphRet u R0 hWindow loss metric epsilonGeom depths hLoss hmetric heGeom heGeom4 hLip
    hstopLo hHeight hCost hSmall hShape hNu hBaseMargin Fcfg extra Sq field key hRel W bin
  let F3 := refinementCost ((dExtra+3)+2) (J+1) L3
  let Q3 := NativeSourceSizeBounds.radix S.card L3
  let pop := population D.thickness eta lambda b F1 G
  let eps : ℝ := 64/((2^(u+12):ℕ):ℝ)
  have hRank : 0 < rankLoss eta0 c (1:Fin 4) := rankLoss_pos he0 hc _
  have hRank1 : rankLoss eta0 c (1:Fin 4) ≤ 1 :=
    (rankLoss_le_initial he0.le hc.le hc1 _).trans he01
  have hm6 : 6 ≤ m := by omega
  have Hrel := Hdata.1.2.2.2.2.2.1
  have ht := commonBudget_pos he0 hc
  have hetaRaw : eta ≤ commonBudget eta0 c/32 := by linarith only [hetaSeed,hseed,htau,ht]
  have H3 := Hbudget.1 n D eta h hsmall heta hetaRaw original horiginal S hS hSn
  have hF3 : 1 ≤ F3 := by have hh := refinementCost_pos ((dExtra+3)+2) (J+1) L3; omega
  have hQ3 : 1 ≤ Q3 := (by norm_num : 1 ≤ (4:ℕ)).trans
    (NativeSourceSizeBounds.radix_four_le _ _)
  have hQ2one : 1 ≤ Q2 := by omega
  have hRho1 : rho m ≤ 1 := by
    have hpow : (64:ℝ) ≤ ((2^m:ℕ):ℝ) := by
      exact_mod_cast (Nat.pow_le_pow_right (by norm_num : 1≤(2:ℕ)) hm6)
    exact (div_le_one (by positivity)).mpr hpow
  have hTauQ : tau ≤ commonBudget eta0 c/(1000*((0:ℕ)+1:ℝ)) := by
    norm_num
    linarith only [htau,ht]
  have hqLower := NativeSmallLossParentBudget.actual_test_radius_small_loss h.1.2.1 hr hr1
    heQ he0.le heQSmall hc hc1 hcQ (1:Fin 4) hrdelta htau0 g 0 hTauQ hgrid hqraw
  have hB7 : r^(7*rankLoss eta0 c (1:Fin 4)) ≤ b := by
    have hh' := Real.rpow_le_rpow_of_exponent_ge hr hr1
      (show (2*((2:ℕ):ℝ)+1)*rankLoss eta0 c (1:Fin 4) ≤
        7*rankLoss eta0 c (1:Fin 4) by norm_num; linarith only [hRank])
    exact hh'.trans hb
  have hRetention := Hbase D.thickness eta lambda b tau seed (commonBudget eta0 c) c2 r
    (cutoff c (1:Fin 4)) (rankLoss eta0 c (1:Fin 4)) q epsilonQ loss metric epsilonGeom
    extremalExponent eps F1 F2 G Q1 Q2 F3 Q3 m R0 2 depths h.1.2.1 h.1.2.2.1 heta
    hF1 hG hQ1 hQ2one hQ3 hGF H1 H2 H3 ht.le htau hseed hc2 hr hr1 hRank.le hRank1
    hrdelta (cutoff_mul_rankLoss eta0 c _).symm hlambda hB7 hq hq1 heQ.le heQ1 hqLower
    (by norm_num) hLoss hmetric heGeom heGeom4 hLip hRho1 hstopLo hscale hHeight
    (by dsimp [eps]; positivity) hSmall hShape
    (by linarith only [hNu]) hBaseMargin
  have hRetain := (NativeBaselineThirdRetentionTrace.from_third_source D zeta a m plane E Hp Hgraph
    S T P hP (by norm_num) (by norm_num) hdim Fraw p pop _ _ Q2 _ _ Cpre t L3 Rel3 _ Hdata K hGraphRet).2
  have hPop : 0 < pop := by
    have hd := h.1.2.1
    have hlambdaPos : 0 < lambda := by rw [hlambda]; positivity
    have hbPos := (Real.rpow_pos_of_pos hr _).trans_le hb
    dsimp [pop,population]
    positivity
  have hCostPos : 0 < (selectionCost K:ℝ)*Cpre*(F3:ℝ) := by
    have hF3p : (0:ℝ) < F3 := by exact_mod_cast (show 0<F3 by omega)
    have hGraph : 0 < selectionCost K := by
      unfold selectionCost NativeProjectorCellChart.chartCount
      positivity
    positivity
  have hPaid : retentionFactor ((selectionCost K:ℝ)*Cpre*(F3:ℝ)) pop ≤ eps^(-(eB/32)) := by
    rw [hCost]
    simpa only [mul_assoc] using hRetention
  have Hrel' : ∀j x y,x∈T → y∈T → degree (fun _ : Fin n × Index => 1)
      (completeRelations D a m p .oneTwo P hP hdim field Fcfg R0 u extra j) T x ≤
      Q3^2*degree (fun _ : Fin n × Index => 1)
        (completeRelations D a m p .oneTwo P hP hdim field Fcfg R0 u extra j) T y := by
    simpa only [hRel] using Hrel
  exact Hmass n D eta a h R Eref Hp T m p etaRef href hScale hRefSmall hEtaRef
    pop ((selectionCost K:ℝ)*Cpre*(F3:ℝ)) hPop hCostPos hPopulation hRetain
    u hWindow hPaid P hP hdim field Fcfg R0 dExtra Q3 F3 extra hF3 hQ3 H3 Hrel'
    (2-extremalExponent) W bin

end NativeActualRawThirdTotalMass
end -- original anonymous section NativeActualRawThirdTotalMass
