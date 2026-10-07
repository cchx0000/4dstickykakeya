import Theorems.Thm_StickyKakeya4_native_raw_whole_Y_retention
import Theorems.Thm_StickyKakeya4_native_actual_raw_weight_source

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
