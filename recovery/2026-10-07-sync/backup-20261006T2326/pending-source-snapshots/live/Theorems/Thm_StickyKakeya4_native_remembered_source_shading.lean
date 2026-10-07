import Theorems.Thm_StickyKakeya4_native_remembered_source_construction

/- UNVERIFIED actual remembered-source shading construction. The sparse
set T supplies the literal same-Q rows; it need not have native admission.
The output source is the exact one to which rank_two_union applies. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 6000000

noncomputable section
namespace NativeRememberedSourceShading
open Classical Finset MeasureTheory StickyKakeya4 NativeCommonCubicalMesh
open NativeOriginalParentSelection NativeOriginalCellChartGeometry NativeCubicalIncidenceCounts
open NativeLocalParentSource NativeRelativeParentLabels NativeRelativeCoarseReadback
open NativeConfiguredIncidenceFibers NativeReferenceXYGridPoints NativeHorizontalGrainSlice
open CanonicalConfiguredE4Bridge NativeRememberedSourceMaps NativeRememberedHeightSelection
open NativeRememberedOccurrenceReadback NativeRememberedFineCount NativeFineWeightedCoarseCore
open NativeCoarseCellSource NativeCoarseDirectionThinning NativeCoarseSourceParentReadback
open NativeTranslatedGrainHeightOverlap NativeLocalCellCoherence
open scoped BigOperators ENNReal

/-- The actual fine-pair and remembered-height counts pay exactly the
final local cell volume. There is no separate old-height retention charge. -/
lemma count_to_mass {r eps d w sigma p G H M : ℝ}
    (hr : 0 < r) (heps : 0 < eps) (hd : 0 < d) (hw : 0 < w)
    (hscale : sigma=d/w)
    (hG : G ≤ fineCapacity*r^(-p)*(d/eps)^3*H)
    (hH : H ≤ 4096*(sigma/eps)*M) :
    r^p*eps^4*G/(65536*fineCapacity*w^3) ≤ M*(sigma/2)^4 := by
  have hCf := fineCapacity_pos
  calc
    _ = (r^p*eps^4/(65536*fineCapacity*w^3))*G := by ring
    _ ≤ (r^p*eps^4/(65536*fineCapacity*w^3))*
        (fineCapacity*r^(-p)*(d/eps)^3*H) :=
      mul_le_mul_of_nonneg_left hG (by positivity)
    _ ≤ (r^p*eps^4/(65536*fineCapacity*w^3))*
        (fineCapacity*r^(-p)*(d/eps)^3*(4096*(sigma/eps)*M)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hH (by positivity)) (by positivity)
    _ = _ := by
      rw [hscale,Real.rpow_neg hr.le]
      field_simp [heps.ne',hw.ne',hCf.ne',(Real.rpow_pos_of_pos hr p).ne']
      ring

/-- Select a genuine old height per final bin, on the actual same-Q
intermediate source, and derive the total shading lower on its literal
local source. All phase, row, capacity and parent readbacks are performed
here. The retained fine graph keeps its baseline b0 tube indices. -/
theorem select_height_and_shading {n : ℕ} {D : FiniteScaleSource n}
    {eta etaS etaC a zeta pExp : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (R : Finset (Fin n)) (Eref T : Finset (Fin n × Index))
    (level m b0 b c : ℕ) (hm : 6 ≤ m) (hb0 : 8 ≤ b0) (hb : b ≤ b0)
    (hc : c ≤ b) (hc6 : 6 ≤ c)
    (HB : NativeMiddleWindowBalance.HasOriginalBackbone D original R a level zeta)
    (hmb0 : m+b0 ≤ level) (hscale : D.thickness ≤ (rho m)^2) (p : Parent)
    (hp : (parentLabels D R a (2^m) p).Nonempty)
    (hS : IsWangZakharovNativeFiniteInput (source h R Eref a m p) etaS)
    (hbudget : (64:ℝ)^3*(source h R Eref a m p).thickness^pExp ≤ D.thickness^zeta)
    (hT : T ⊆ incidences original)
    (hparent : ∀z∈T,z.1∈parentLabels D R a (2^m) p)
    (s : Split) (P : Submodule ℝ E4) (hP : P ≤ heightKernel)
    (hdim : Module.finrank ℝ P=tangentDim s)
    (F Fcfg : ℤ → Matrix (Fin (normalDim s)) (Fin (tangentDim s)) ℝ)
    (hF : ∀t i j,|F t i j| ≤ 1/4) (hCfg : ∀t i j,|Fcfg t i j| ≤ 1/4)
    (R0 : ℕ) (hR0 : 0 < R0) (hbase : rho m ≤ mu m*(R0:ℝ))
    (hmatch : mu m*(R0:ℝ)=4096/((2^b0:ℕ):ℝ))
    (Hsingle : ∀x∈T,∀y∈T,translatedHeight D a m x.2/((8*R0:ℕ):ℤ)=
      translatedHeight D a m y.2/((8*R0:ℕ):ℤ) → translatedHeight D a m x.2=translatedHeight D a m y.2)
    (Q : Finset Parent)
    (hQ : Q ⊆ (univ : Finset (Fin (parentLabels D R a (2^m) p).card)).image
      (parentLabel (source h R Eref a m p) 0 (2^b)))
    (hsep : ∀q∈Q,∀q'∈Q,q≠q' → 64/((2^b:ℕ):ℝ) ≤
      dist (direction ((source h R Eref a m p).line (representative hS univ 0 (2^b) q)))
        (direction ((source h R Eref a m p).line (representative hS univ 0 (2^b) q')))) :
    let C := NativeCoarseCellSource.source hS 0 (level-m+6) b Q
      (representative hS univ 0 (2^b)) (incidences (sourceCells D R T a (2^m) p)) hsep
    ∀hC : IsWangZakharovNativeFiniteInput C etaC,
    let cfg := NativeActualConfiguredPoint.point D a m p s P hP hdim F Fcfg R0
    (∀x∈T.image (fun z => cfg z.2),∀y∈T.image (fun z => cfg z.2),x≠y →
      64/((2^b0:ℕ):ℝ) ≤ dist x y) →
    ∀(A : Finset (Fin n × Index)),A ⊆ T → A.Nonempty →
      (∀z∈A,relativeLabel D a (2^m) p (2^b) z.1∈Q) →
    ∀qOld : Parent,(∀z∈A,relativeLabel D a (2^m) p (2^c) z.1=qOld) →
    let pA := zeroProjection qOld
    let cells := actualRows h R Eref T level m b p hS Q
    let Occ := occurrences h R a m b p hp Q cells A
    ∃B ⊆ Occ.image (taggedKey D a m C c pA),
      (∀v∈B,∀w∈B,finalTime v=finalTime w → v.1=w.1) ∧
      let Efinal := selectedPairs D a m C c pA Occ B
      Efinal.Nonempty ∧ Efinal ⊆ incidences cells ∧
      (∀z∈Efinal,z.1∈parentLabels C univ 0 (2^c) pA) ∧
      Efinal.image (localPair C 0 (2^c) pA)=B.image Prod.snd ∧
      ENNReal.ofReal ((source h R Eref a m p).thickness^pExp*(64/((2^b0:ℕ):ℝ))^4*
        ((NativeSameQFineGraph.graph h R Eref a m b0 p hS cfg A).card:ℝ)/
        (65536*fineCapacity*(64/((2^c:ℕ):ℝ))^3)) ≤
        wzTotalShadingVolume (source hC univ Efinal 0 c pA) := by
  intro C hC cfg hpointSep A hAT hAne hAQ qOld hPhase pA cells Occ
  let eps : ℝ := 64/((2^b0:ℕ):ℝ)
  let d : ℝ := 64/((2^b:ℕ):ℝ)
  let w : ℝ := 64/((2^c:ℕ):ℝ)
  let sigma : ℝ := ((2^c:ℕ):ℝ)*C.thickness/64
  have heps : 0 < eps := by dsimp only [eps]; positivity
  have hd : 0 < d := by dsimp only [d]; positivity
  have hw : 0 < w := by dsimp only [w]; positivity
  have hthickness : C.thickness=d := rfl
  have hNscale : ((2^m:ℕ):ℝ)*D.thickness ≤ 1 :=
    NativeCompactAncestorRegularity.dyadic_parent_scale HB.2.1 ⟨m,by omega⟩
  have hRelScale : ((2^m:ℕ):ℝ)*D.thickness*((2^b:ℕ):ℝ) ≤ 64 := by
    calc
      _ = ((2^(m+b):ℕ):ℝ)*D.thickness := by push_cast; rw [pow_add]; ring
      _ ≤ 1 := NativeCompactAncestorRegularity.dyadic_parent_scale HB.2.1 ⟨m+b,by omega⟩
      _ ≤ 64 := by norm_num
  have hepsd : eps ≤ d := by
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    exact_mod_cast Nat.pow_le_pow_right (by norm_num : 0 < (2:ℕ)) hb
  have hnc : (64:ℝ) ≤ ((2^c:ℕ):ℝ) := by
    exact_mod_cast Nat.pow_le_pow_right (by norm_num : 0 < (2:ℕ)) hc6
  have hdsigma : C.thickness ≤ sigma := by
    dsimp only [sigma]
    nlinarith only [hnc,hC.1.2.1]
  have hepssigma : eps ≤ sigma := hepsd.trans (by simpa only [hthickness] using hdsigma)
  have hmatchb : mu m*(R0:ℝ) ≤ 4096/((2^b:ℕ):ℝ) := by
    rw [hmatch]
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    exact_mod_cast Nat.pow_le_pow_right (by norm_num : 0 < (2:ℕ)) hb
  have hmesh : mu m*(R0:ℝ)=64*eps := by rw [hmatch]; dsimp only [eps]; ring
  have hsigmaread : sigma=d/w := by
    dsimp only [sigma,w]
    rw [hthickness]
    field_simp
  obtain ⟨B,hBO,hret,hCoherent,hImage⟩ := select_actual_old_height h original horiginal ha R m b hm p hp
    hNscale hRelScale Q C hthickness cells A (hAT.trans hT) (fun z hz => hparent z (hAT hz))
    s P hP hdim F Fcfg hF hCfg R0 hR0 hbase hmatchb eps heps hmesh c pA hdsigma hepssigma
    T hAT Hsingle
  let Efinal := selectedPairs D a m C c pA Occ B
  change ((Occ.image (taggedKey D a m C c pA)).card:ℝ) ≤
    (4096*(sigma/eps))*((Efinal.image (localPair C 0 (2^c) pA)).card:ℝ) at hret
  have hsigma : 0 < sigma := by rw [hsigmaread]; positivity
  have hFine := fine_graph_le_tagged h original horiginal ha R Eref T level m b0 b hm hb0 hb
    HB hmb0 hscale p hp hS hbudget hT hparent s P hP hdim F Fcfg hF hCfg R0 hR0 hbase hmatch
    Q C c pA A hAT hAQ hpointSep
  change ((NativeSameQFineGraph.graph h R Eref a m b0 p hS cfg A).card:ℝ) ≤
    fineCapacity*(source h R Eref a m p).thickness^(-pExp)*(d/eps)^3*
      ((Occ.image (taggedKey D a m C c pA)).card:ℝ) at hFine
  have hCard := count_to_mass hS.1.2.1 heps hd hw hsigmaread hFine hret
  have hEinc : Efinal ⊆ incidences cells := by
    intro v hv
    obtain ⟨z,hz,rfl⟩ := mem_image.mp hv
    exact ((mem_occurrences h R a m b p hp Q cells A z).mp (mem_filter.mp hz).1).1
  have hCurrent := occurrence_current_parent h R Eref T level m b p hp hS Q hQ hsep A c hc qOld hPhase
  have hParentFinal : ∀v∈Efinal,v.1∈parentLabels C univ 0 (2^c) pA := by
    intro v hv
    obtain ⟨z,hz,rfl⟩ := mem_image.mp hv
    exact (mem_parentLabels C univ 0 (2^c) pA _).mpr
      ⟨mem_univ _,hCurrent z (mem_filter.mp hz).1⟩
  have hEne : Efinal.Nonempty := by
    by_contra hEmpty
    have hEmpty' : Efinal=∅ := not_nonempty_iff_eq_empty.mp hEmpty
    have hretZero : ((Occ.image (taggedKey D a m C c pA)).card:ℝ) ≤ 0 := by
      simpa only [hEmpty',image_empty,card_empty,Nat.cast_zero,mul_zero] using hret
    have htags : ((Occ.image (taggedKey D a m C c pA)).card:ℝ)=0 :=
      le_antisymm hretZero (Nat.cast_nonneg _)
    rw [htags,mul_zero] at hFine
    have hgpos : (0:ℝ) < (NativeSameQFineGraph.graph h R Eref a m b0 p hS cfg A).card := by
      exact_mod_cast card_pos.mpr (hAne.image _)
    linarith only [hFine,hgpos]
  refine ⟨B,hBO,hCoherent,hEne,hEinc,hParentFinal,hImage,?_⟩
  rw [source_total_shading hC univ Efinal 0 c pA hParentFinal]
  have hlocalMesh : ((2^c:ℕ):ℝ)*C.thickness/128=sigma/2 := by dsimp only [sigma]; ring
  rw [hlocalMesh]
  simpa only [ENNReal.ofReal_mul (Nat.cast_nonneg _),ENNReal.ofReal_pow (half_pos hsigma).le,
    ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal hCard

end NativeRememberedSourceShading
