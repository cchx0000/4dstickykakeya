/- UNVERIFIED actual first-alignment patch attachment. No compiler run.
The source remains in its original native cubical coordinates.
normalChart is composed only with the packed frame evaluated by key maps.
The actual same-old-phase reader gives74w in E4, hence185w in the planar
Euclidean metric used by localBall;185w<tau when tau=4096w.
Selected-key membership is the literal mother Ycut membership. It is not
an assumed higher-plane support or lower-population condition.
-/
import Theorems.Thm_StickyKakeya4_native_configured_lower_quotient_readback
import Theorems.Thm_StickyKakeya4_native_remembered_source_construction
import Theorems.Thm_StickyKakeya4_native_literal_Y_height_alignment
import Theorems.Thm_StickyKakeya4_native_actual_higher_transfer_construction_draft_2020

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000
noncomputable section
namespace NativeRememberedAlignmentPatchDraft2036
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeHorizontalGrainSlice NativeReferenceXYGridPoints NativeTranslatedGrainHeightOverlap
open NativeConfiguredThirdRelation NativeActualConfiguredPoint NativeLocalParentSource
open NativeConfiguredLowerQuotientReadback NativeRememberedPhaseFootprint
open NativeRelativeParentLabels NativeFixedCompactKakeyaExponent
open CanonicalConfiguredE4Bridge NativeLiteralYHeightAlignment NativePaperAlignmentScales
open NativeAngularChartSelection NativePackedHigherCapacityDraft2006
open scoped BigOperators

/-- The common planar coordinate permutation is applied to the packed
key frame, not to native lines or native cubical cells. -/
def normalChart (j : Fin 2) : E4 ≃ₗᵢ[ℝ] E4 :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap (1:Fin 4) j.castSucc.succ)

lemma normalChart_height (j : Fin 2) (x : E4) : normalChart j x 3=x 3 := by
  fin_cases j <;> simp [normalChart,LinearIsometryEquiv.piLpCongrLeft_apply,Equiv.piCongrLeft']

lemma normalChart_tangent (j : Fin 2) (x : E4) : normalChart j x 0=x 0 := by
  fin_cases j <;> simp [normalChart,LinearIsometryEquiv.piLpCongrLeft_apply,Equiv.piCongrLeft']

def chartRows (j : Fin 2) (F : Matrix (Fin 2) (Fin 1) ℝ) : Matrix (Fin 2) (Fin 1) ℝ :=
  fun i a => F (chartPerm j i) a

theorem normalChart_quotient (j : Fin 2) (F : Matrix (Fin 2) (Fin 1) ℝ) (x : E4) :
    lowerQuotient (chartRows j F) (normalChart j x)=chartPoint j (lowerQuotient F x) := by
  funext i
  fin_cases j <;> fin_cases i <;>
    simp [normalChart,LinearIsometryEquiv.piLpCongrLeft_apply,Equiv.piCongrLeft',
      lowerQuotient,chartRows,chartPoint,chartPerm]

theorem normalized_chart_quotient (j : Fin 2) (F : Matrix (Fin 2) (Fin 1) ℝ)
    (x : E4) (anchor : Fin 2 → ℝ) (tau : ℝ) :
    normalizedLowerQuotient (normalChart j x) (chartRows j F 0 0) (chartRows j F 1 0)
      (chartPoint j anchor) tau = normalization j anchor tau (lowerQuotient F x) := by
  rw [normalization_apply]
  funext i
  fin_cases j <;> fin_cases i <;>
    simp [normalizedLowerQuotient,normalChart,LinearIsometryEquiv.piLpCongrLeft_apply,
      Equiv.piCongrLeft',chartRows,chartPoint,chartPerm,lowerQuotient,
      NormalizedQuantizedPatches.affine]

theorem permuted_witness_pullback (O : E4 ≃ₗᵢ[ℝ] E4) (j : Fin 2) (x : E4) :
    (O.trans (normalChart j)).symm (normalChart j x)=O.symm x := by simp

/-- At one genuine old height, the literal first planar Y points inherit
their Euclidean distance bound from the ACTUAL original phase, not from a
substitute enlarged patch or a higher-field Lipschitz assertion. -/
theorem actual_phase_Y_distance {n : ℕ} {D : FiniteScaleSource n} {eta etaS a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (backbone : Finset (Fin n)) (Eref T : Finset (Fin n × Index)) (m : ℕ) (hm : 6≤m)
    (hscale : D.thickness≤(rho m)^2) (p : Parent)
    (hS : IsWangZakharovNativeFiniteInput (NativeLocalParentSource.source h backbone Eref a m p) etaS)
    (hSK : ∀i,(NativeLocalParentSource.source h backbone Eref a m p).line i∈NativeUnitParentNormalization.fixedCompactClass)
    (levelS b0 c : ℕ) (hb0 : 8≤b0) (hc : c≤b0)
    (P : Submodule ℝ E4) (hP : P≤heightKernel) (hd : Module.finrank ℝ P=1)
    (F Fcfg : ℤ → Matrix (Fin 2) (Fin 1) ℝ)
    (hF : ∀t i j,|F t i j|≤1/4) (hCfg : ∀t i j,|Fcfg t i j|≤1/4)
    (R0 : ℕ) (hR0 : 0<R0) (hbase : rho m≤mu m*(R0:ℝ))
    (hmatch : mu m*(R0:ℝ)≤4096/((2^b0:ℕ):ℝ))
    (z z' : Fin n × Index)
    (hz : z∈NativeCubicalIncidenceCounts.incidences original)
    (hz' : z'∈NativeCubicalIncidenceCounts.incidences original)
    (hzP : z.1∈parentLabels D backbone a (2^m) p)
    (hzP' : z'.1∈parentLabels D backbone a (2^m) p)
    (ht : translatedHeight D a m z.2=translatedHeight D a m z'.2)
    (hphase : relativeLabel D a (2^m) p (2^c) z.1=relativeLabel D a (2^m) p (2^c) z'.1) :
    dist (EuclideanAlignmentPatches.euclidean
      (NativeQuotientGridCenters.center (mu m*(R0:ℝ)/512)
        (coarseYKey D a m p .oneTwo P hP hd F Fcfg R0 z.2).2))
      (EuclideanAlignmentPatches.euclidean
      (NativeQuotientGridCenters.center (mu m*(R0:ℝ)/512)
        (coarseYKey D a m p .oneTwo P hP hd F Fcfg R0 z'.2).2))≤
      185*(64/((2^c:ℕ):ℝ)) := by
  have hE4 := actual_configured_diameter h original horiginal ha backbone Eref T m hm hscale p hS hSK
    levelS b0 c hb0 hc .oneTwo P hP hd F Fcfg hF hCfg R0 hR0 hbase hmatch z z' hz hz' hzP hzP' ht hphase
  have hSup := key_center_dist_of_same_old_height D a m p P hP hd F Fcfg
    (fun t i => hCfg t i 0) R0 z.2 z'.2 ht
  let x := NativeQuotientGridCenters.center (mu m*(R0:ℝ)/512)
    (coarseYKey D a m p .oneTwo P hP hd F Fcfg R0 z.2).2
  let y := NativeQuotientGridCenters.center (mu m*(R0:ℝ)/512)
    (coarseYKey D a m p .oneTwo P hP hd F Fcfg R0 z'.2).2
  have hc0 : 0≤(5/4:ℝ)*dist (point D a m p .oneTwo P hP hd F Fcfg R0 z.2)
      (point D a m p .oneTwo P hP hd F Fcfg R0 z'.2) := by positivity
  have hEuclid := EuclideanAlignmentPatches.euclidean_dist_le_card_mul x y _ hc0 (fun j => by
    exact (show |x j-y j|≤dist x y by simpa only [Real.dist_eq] using dist_le_pi_dist x y j).trans hSup)
  change dist (EuclideanAlignmentPatches.euclidean x) (EuclideanAlignmentPatches.euclidean y)≤_
  norm_num only [Nat.cast_ofNat] at hEuclid
  nlinarith only [hEuclid,hE4]

lemma selected_key_center_mem (kept : Finset Key) (delta : ℝ) (q : Key) (hq : q∈kept) :
    NativeQuotientGridCenters.center delta q.2∈heightPoints kept delta q.1 := by
  exact mem_image_of_mem _ (mem_filter.mpr ⟨hq,rfl⟩)

/-- Consume the actual first common-menu selected slice, including its
original selected point set. The caller obtains hNear from the preceding
actual-phase reader with185w<tau, so hPatch is an output here. -/
theorem selected_height_patch {X : Type*} (A : Finset X) (key : X → Key)
    (kept Y : Finset Key) (u : ℕ) (t zeta chi : ℝ) (height : ℤ)
    (W : HeightAlignment Y u t zeta chi height)
    (hSelected : heightPoints kept ((2:ℝ)⁻¹^u/512) height=W.selected)
    (hKey : ∀z∈A,key z∈kept) (hHeight : ∀z∈A,(key z).1=height)
    (z0 : X) (hz0 : z0∈A)
    (hNear : ∀z∈A,
      dist (EuclideanAlignmentPatches.euclidean (NativeQuotientGridCenters.center ((2:ℝ)⁻¹^u/512) (key z).2))
        (EuclideanAlignmentPatches.euclidean (NativeQuotientGridCenters.center ((2:ℝ)⁻¹^u/512) (key z0).2))<
        NativeDyadicTubeStopping.scale ((2:ℝ)⁻¹^u/512) W.tauDepth.val) :
    let anchor := NativeQuotientGridCenters.center ((2:ℝ)⁻¹^u/512) (key z0).2
    let tau := NativeDyadicTubeStopping.scale ((2:ℝ)⁻¹^u/512) W.tauDepth.val
    let rho := NativeDyadicTubeStopping.scale ((2:ℝ)⁻¹^u/512) W.rhoDepth.val
    let Patch := (localBall W.selected anchor tau).image (normalization W.chart anchor tau)
    NativeLiteralAlignedSet.NearlyLiteralAligned Patch (rho/tau) t W.exponent ((rho/tau)^(-zeta)) ∧
      ∀z∈A,normalization W.chart anchor tau
        (NativeQuotientGridCenters.center ((2:ℝ)⁻¹^u/512) (key z).2)∈Patch := by
  intro anchor tau rho Patch
  have hMem : ∀z∈A,NativeQuotientGridCenters.center ((2:ℝ)⁻¹^u/512) (key z).2∈W.selected := by
    intro z hz
    rw [←hSelected]
    have hh := selected_key_center_mem kept ((2:ℝ)⁻¹^u/512) (key z) (hKey z hz)
    simpa only [hHeight z hz] using hh
  refine ⟨W.aligned anchor (hMem z0 hz0),?_⟩
  intro z hz
  exact mem_image_of_mem _ (mem_filter.mpr ⟨hMem z hz,hNear z hz⟩)

/-- One ORIGINAL occupied-height/old-phase slice supplies its genuine
common higher field and FULL scalar Y. The patch membership and its radius
are derived internally from actual original incidences, the literal Ycut,
and the original HeightAlignment selected slice. -/
theorem actual_old_height_scalar_family {n : ℕ} {D : FiniteScaleSource n} {eta etaS a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (backbone : Finset (Fin n)) (Eref T A : Finset (Fin n × Index)) (hAn : A.Nonempty)
    (m : ℕ) (hm : 6≤m) (hscale : D.thickness≤(rho m)^2) (p : Parent)
    (hS : IsWangZakharovNativeFiniteInput (NativeLocalParentSource.source h backbone Eref a m p) etaS)
    (hSK : ∀i,(NativeLocalParentSource.source h backbone Eref a m p).line i∈NativeUnitParentNormalization.fixedCompactClass)
    (levelS b0 c : ℕ) (hb0 : 8≤b0) (hc : c≤b0)
    (P : Submodule ℝ E4) (hP : P≤heightKernel) (hd : Module.finrank ℝ P=1)
    (F Fcfg : ℤ → Matrix (Fin 2) (Fin 1) ℝ)
    (hF : ∀t i j,|F t i j|≤1/4) (hCfg : ∀t i j,|Fcfg t i j|≤1/4)
    (R0 : ℕ) (hR0 : 0<R0) (hbase : rho m≤mu m*(R0:ℝ))
    (hmatch : mu m*(R0:ℝ)≤4096/((2^b0:ℕ):ℝ))
    (hA : A⊆NativeCubicalIncidenceCounts.incidences original)
    (hParent : ∀z∈A,z.1∈parentLabels D backbone a (2^m) p)
    (oldH : ℤ) (hHeight : ∀z∈A,translatedHeight D a m z.2=oldH)
    (q : Parent) (hPhase : ∀z∈A,relativeLabel D a (2^m) p (2^c) z.1=q)
    (kept Ybase : Finset Key) (u : ℕ) (t zeta chi : ℝ)
    (hBaseEq : mu m*(R0:ℝ)=(2:ℝ)⁻¹^u)
    (W : HeightAlignment Ybase u t zeta chi (oldH/((8*R0:ℕ):ℤ)))
    (hSelected : heightPoints kept ((2:ℝ)⁻¹^u/512) (oldH/((8*R0:ℕ):ℤ))=W.selected)
    (hKey : ∀z∈A,coarseYKey D a m p .oneTwo P hP hd F Fcfg R0 z.2∈kept)
    (hTau : NativeDyadicTubeStopping.scale ((2:ℝ)⁻¹^u/512) W.tauDepth.val=
      4096*(64/((2^c:ℕ):ℝ))) :
    let tau := NativeDyadicTubeStopping.scale ((2:ℝ)⁻¹^u/512) W.tauDepth.val
    let rhoA := NativeDyadicTubeStopping.scale ((2:ℝ)⁻¹^u/512) W.rhoDepth.val
    let M := chartRows W.chart (Fcfg (oldH/((8*R0:ℕ):ℤ)))
    ∃(anchor : Fin 2 → ℝ) (theta : ℝ) (Y : Finset ℝ),
      anchor∈W.selected ∧ |theta|≤1 ∧ |M 1 0-theta*M 0 0|≤1/2 ∧ Y.Nonempty ∧
      (∀y∈Y,|y|≤1) ∧
      FiniteVoronoiRealADCoarsening.ADBounds Y (rhoA/tau) ((rhoA/tau)^(-zeta)) (t-W.exponent) ∧
      ∀z∈A,∃y∈Y,
        |NativeHigherQuotientParentTransport.higherY (M 1 0-theta*M 0 0) theta
          (normalChart W.chart (point D a m p .oneTwo P hP hd F Fcfg R0 z.2))-
          (tau*y+(chartPoint W.chart anchor 1-theta*chartPoint W.chart anchor 0))|≤2*rhoA := by
  intro tau rhoA M
  let key := fun z : Fin n × Index => coarseYKey D a m p .oneTwo P hP hd F Fcfg R0 z.2
  let ypoint := fun z : Fin n × Index => NativeQuotientGridCenters.center ((2:ℝ)⁻¹^u/512) (key z).2
  obtain ⟨z0,hz0⟩ := hAn
  let anchor := ypoint z0
  have hKeyHeight : ∀z∈A,(key z).1=oldH/((8*R0:ℕ):ℤ) := by
    intro z hz
    rw [coarse_height_readback,hHeight z hz]
  have hAnchor : anchor∈W.selected := by
    rw [←hSelected]
    have hh := selected_key_center_mem kept ((2:ℝ)⁻¹^u/512) (key z0) (hKey z0 hz0)
    simpa only [hKeyHeight z0 hz0] using hh
  have hNear : ∀z∈A,dist (EuclideanAlignmentPatches.euclidean (ypoint z))
      (EuclideanAlignmentPatches.euclidean anchor)<tau := by
    intro z hz
    have hh := actual_phase_Y_distance h original horiginal ha backbone Eref T m hm hscale p hS hSK
      levelS b0 c hb0 hc P hP hd F Fcfg hF hCfg R0 hR0 hbase hmatch z z0
      (hA hz) (hA hz0) (hParent z hz) (hParent z0 hz0)
      ((hHeight z hz).trans (hHeight z0 hz0).symm) ((hPhase z hz).trans (hPhase z0 hz0).symm)
    rw [hBaseEq] at hh
    have hw : (0:ℝ)<64/((2^c:ℕ):ℝ) := by positivity
    change dist (EuclideanAlignmentPatches.euclidean (ypoint z))
      (EuclideanAlignmentPatches.euclidean (ypoint z0))≤_ at hh
    change dist (EuclideanAlignmentPatches.euclidean (ypoint z))
      (EuclideanAlignmentPatches.euclidean (ypoint z0))<_
    change tau=4096*(64/((2^c:ℕ):ℝ)) at hTau
    linarith only [hh,hTau,hw]
  obtain ⟨hPatch,hMem⟩ := selected_height_patch A key kept Ybase u t zeta chi
    (oldH/((8*R0:ℕ):ℤ)) W hSelected hKey hKeyHeight z0 hz0 hNear
  let Patch := (localBall W.selected anchor tau).image (normalization W.chart anchor tau)
  obtain ⟨theta,Y,hTheta,hYn,hYbox,hYAD,hWitness⟩ :=
    nearly_aligned_scalar_witnesses Patch (rhoA/tau) t W.exponent ((rhoA/tau)^(-zeta)) hPatch
  have hM0 : |M 0 0|≤1/4 := hCfg _ _ _
  have hM1 : |M 1 0|≤1/4 := hCfg _ _ _
  have hC : |M 1 0-theta*M 0 0|≤1/2 := by
    have hh := abs_sub (M 1 0) (theta*M 0 0)
    rw [abs_mul] at hh
    have hm' := mul_le_mul hTheta hM0 (abs_nonneg _) zero_le_one
    linarith only [hh,hm',hM1]
  refine ⟨anchor,theta,Y,hAnchor,hTheta,hC,hYn,hYbox,hYAD,?_⟩
  intro z hz
  let cfg := point D a m p .oneTwo P hP hd F Fcfg R0 z.2
  have hRead : lowerQuotient (Fcfg (oldH/((8*R0:ℕ):ℤ))) cfg=ypoint z := by
    have hh := point_quotient_readback D a m p P hP hd F Fcfg R0 z.2
    rw [hBaseEq] at hh
    simpa only [hKeyHeight z hz] using hh
  have hNorm : normalizedLowerQuotient (normalChart W.chart cfg) (M 0 0) (M 1 0)
      (chartPoint W.chart anchor) tau = normalization W.chart anchor tau (ypoint z) := by
    rw [normalized_chart_quotient,hRead]
  have hIn : normalizedLowerQuotient (normalChart W.chart cfg) (M 0 0) (M 1 0)
      (chartPoint W.chart anchor) tau∈Patch := by
    rw [hNorm]
    exact hMem z hz
  obtain ⟨y,hy,he⟩ := hWitness _ hIn
  have htau0 : 0<tau := NativeDyadicTubeStopping.scale_pos (by positivity) _
  refine ⟨y,hy,?_⟩
  rw [normalized_lower_identity (normalChart W.chart cfg) (M 0 0) (M 1 0)
    theta (chartPoint W.chart anchor) tau htau0.ne']
  have hid : tau*(normalizedLowerQuotient (normalChart W.chart cfg) (M 0 0) (M 1 0)
      (chartPoint W.chart anchor) tau 1-
      theta*normalizedLowerQuotient (normalChart W.chart cfg) (M 0 0) (M 1 0)
        (chartPoint W.chart anchor) tau 0)+
      (chartPoint W.chart anchor 1-theta*chartPoint W.chart anchor 0)-
      (tau*y+(chartPoint W.chart anchor 1-theta*chartPoint W.chart anchor 0))=
    tau*(normalizedLowerQuotient (normalChart W.chart cfg) (M 0 0) (M 1 0)
      (chartPoint W.chart anchor) tau 1-
      theta*normalizedLowerQuotient (normalChart W.chart cfg) (M 0 0) (M 1 0)
        (chartPoint W.chart anchor) tau 0-y) := by ring
  rw [hid,abs_mul,abs_of_pos htau0]
  have hh := mul_le_mul_of_nonneg_left he htau0.le
  have hcancel : tau*(2*(rhoA/tau))=2*rhoA := by field_simp [htau0.ne'] <;> ring
  exact hh.trans_eq hcancel

end NativeRememberedAlignmentPatchDraft2036
