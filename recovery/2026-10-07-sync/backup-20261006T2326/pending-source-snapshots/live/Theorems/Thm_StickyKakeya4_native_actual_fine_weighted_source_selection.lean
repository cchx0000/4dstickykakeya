import Theorems.Thm_StickyKakeya4_native_actual_fine_weight_shading_bridge
import Theorems.Thm_StickyKakeya4_native_same_reference_chart_bounds
import Theorems.Thm_StickyKakeya4_native_current_reference_incidence_subset

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 6000000

noncomputable section
namespace NativeActualFineWeightedSourceSelection
open Classical Finset MeasureTheory StickyKakeya4 NativeCommonCubicalMesh
open NativeOriginalParentSelection NativeCubicalIncidenceCounts NativeLocalParentSource
open NativeMiddleWindowBalance NativeRelativeCoarseReadback NativeReferenceXYGridPoints
open NativeHorizontalGrainSlice CanonicalConfiguredE4Bridge NativeUnitParentNormalization
open NativeFineWeightedCoarseCore NativeActualFineWeightShadingBridge
open NativeCoarsePowerWindow NativeCoarseRelativeCW NativeDyadicParentCells
open scoped BigOperators ENNReal

/-- Source-facing construction on the unchanged original T and admitted
initial reference. Original HB supplies every reference population used by
coloring, pruning and the fixed-height capacity. Actual fine-pair counts
supply both the per-parent U and the original-E shading bridge.

Exactly one Q is selected. Its terminal ancestor certificate, native source,
and retained BASELINE fine graph are all returned together. The original
fine-graph normalization and scalar payments remain explicit for the caller's
pre-source parameter factory. The squared-scale guard is only for the INITIAL
reference construction; it is not imposed on a second local parent. -/
theorem exists_same_Q_source {n : ℕ} {D : FiniteScaleSource n}
    {eta etaS a zeta pExp z e : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta)
    (original : Fin n → Finset Index) (R : Finset (Fin n)) (level : ℕ)
    (HB : HasOriginalBackbone D original R a level zeta)
    (Eref T : Finset (Fin n × Index)) (hEref : Eref⊆incidences original) (hTE : T⊆Eref)
    (m b0 b : ℕ) (hm : 6 ≤ m) (hb0 : 8 ≤ b0) (hb : b ≤ b0) (h6 : 6 ≤ b)
    (hmb0 : m+b0 ≤ level) (hInitialScale : D.thickness ≤ (rho m)^2) (p : Parent)
    (hS : IsWangZakharovNativeFiniteInput (source h R Eref a m p) etaS)
    (hparent : ∀v∈T,v.1∈parentLabels D R a (2^m) p)
    (hpExp : 0 ≤ pExp) (hpz : pExp ≤ z)
    (s : Split) (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (hdim : Module.finrank ℝ P=tangentDim s)
    (F Fcfg : ℤ → Matrix (Fin (normalDim s)) (Fin (tangentDim s)) ℝ)
    (hF : ∀t u v,|F t u v| ≤ 1/4) (hCfg : ∀t u v,|Fcfg t u v| ≤ 1/4)
    (R0 : ℕ) (hR0 : 0 < R0) (hbase : rho m ≤ mu m*(R0:ℝ))
    (hmatch : mu m*(R0:ℝ)=4096/((2^b0:ℕ):ℝ)) :
    let Sref := source h R Eref a m p
    let cfg := NativeActualConfiguredPoint.point D a m p s P hP hdim F Fcfg R0
    let r := Sref.thickness
    let eps : ℝ := 64/((2^b0:ℕ):ℝ)
    let d : ℝ := 64/((2^b:ℕ):ℝ)
    let G := fun A : Finset (Fin n × Index) => NativeSameQFineGraph.graph h R Eref a m b0 p hS cfg A
    let rep := NativeCoarseDirectionThinning.representative hS univ 0 (2^b)
    (∀x∈T.image (fun v => cfg v.2),∀y∈T.image (fun v => cfg v.2),x≠y → eps ≤ dist x y) →
    r^z ≤ eps^4*((G T).card:ℝ) →
    (64:ℝ)^3*r^pExp ≤ D.thickness^zeta →
    colorCost*r^z ≤ 1 → 2*pruneCost*((b:ℝ)+1)*r^(3*z) ≤ 1 →
    1088*fineCapacity*r^z ≤ 1 → d^e ≤ r^(8*z) →
    10077696*r^(8*z) ≤ 1 → densityCost*r^z ≤ 1 → cwCost*r^(2*z-etaS) ≤ 1 →
    ∃ (Q : Finset Parent)
      (hsep : ∀q∈Q,∀q'∈Q,q≠q' → d ≤
        dist (direction (Sref.line (rep q))) (direction (Sref.line (rep q')))),
      Q⊆(univ : Finset (Fin (parentLabels D R a (2^m) p).card)).image (parentLabel Sref 0 (2^b)) ∧
      Q.Nonempty ∧
      (∀q∈Q,parentLabel Sref 0 (2^b) (rep q)=q) ∧
      (∀ell : Fin (b+1),∀q : Parent,
        (Q.filter (fun q' => ancestor b ell.val q'=q)).Nonempty →
          r^(8*z)*(((2^b:ℕ):ℝ)/((2^ell.val:ℕ):ℝ))^3 ≤
            ((Q.filter (fun q' => ancestor b ell.val q'=q)).card:ℝ)) ∧
      let TQ := NativeSameQSourceRestriction.restrict D a m b p Q T
      let C := NativeCoarseCellSource.source hS 0 (level-m+6) b Q rep
        (incidences (sourceCells D R T a (2^m) p)) hsep
      IsWangZakharovNativeFiniteInput C e ∧ C.thickness=d ∧
      (∀i,C.line i∈fixedCompactClass) ∧
      r^(5*z) ≤ (wzTotalShadingVolume C).toReal ∧
      r^pExp/(2*colorCost)*((G T).card:ℝ) ≤ ((G TQ).card:ℝ) ∧
      r^(3*z)/2 ≤ eps^4*((G TQ).card:ℝ) ∧
      r^(3*z)/(2*eps^4) ≤ ((G TQ).card:ℝ) := by
  intro Sref cfg r eps d G rep hpointSep htotal hprofile hcolor hprune hshadeCost hpower hupper hdensity hcw
  have hT : T⊆incidences original := hTE.trans hEref
  have hQoriginal : (parentLabels D R a (2^m) p).Nonempty := card_pos.mp hS.1.1
  have hr : 0 < r := hS.1.2.1
  have heps : 0 < eps := by dsimp [eps]; positivity
  have hmlevel : m ≤ level := by omega
  have hblevel : b ≤ level-m+6 := by omega
  have H := NativeSameReferenceChartBounds.population_through h original R level HB Eref m b0 hmb0 p hprofile
  have Hfine : ∀q : Parent,
      ((univ : Finset (Fin (parentLabels D R a (2^m) p).card)).filter
        (fun i => parentLabel Sref 0 (2^b0) i=q)).Nonempty →
      r^pExp*((1/((2^b0:ℕ):ℝ))/r)^3 ≤
        (((univ : Finset (Fin (parentLabels D R a (2^m) p).card)).filter
          (fun i => parentLabel Sref 0 (2^b0) i=q)).card:ℝ) :=
    fun q hq => (H ⟨b0,by omega⟩ q hq).1
  have hscale : ((2^b:ℕ):ℝ)*Sref.thickness ≤ 1 :=
    NativeSameReferenceChartBounds.source_scale_guard (a:=a) h R Eref level m b p HB.2.1 (by omega)
  let W := NativeSameQFineGraph.weight h R Eref a m b0 b p hS cfg T
  have hW : ∀q∈(univ : Finset (Fin (parentLabels D R a (2^m) p).card)).image
      (parentLabel Sref 0 (2^b)),0 ≤ W q := by
    intro q _hq
    exact Nat.cast_nonneg _
  have hU := NativeActualFineWeightShadingBridge.actual_weight_upper h original HB.1 HB.2.2.1
    R Eref T level m b0 b hm hb0 hb HB.2.1 hmb0 hInitialScale p hS hT hparent Hfine
    s P hP hdim F Fcfg hF hCfg R0 hR0 hbase hmatch hpointSep
  have hbridge := NativeActualFineWeightShadingBridge.same_Q_weight_shading h original HB.1 HB.2.2.1
    R Eref T level m b0 b hm hb0 hb HB.2.1 hmb0 hInitialScale p hQoriginal hS hT hparent Hfine
    s P hP hdim F Fcfg hF hCfg R0 hR0 hbase hmatch hpointSep
  have hWtotal : (∑q∈(univ : Finset (Fin (parentLabels D R a (2^m) p).card)).image
      (parentLabel Sref 0 (2^b)),W q)=((G T).card:ℝ) :=
    NativeSameQFineGraph.total_weight_eq_graph h R Eref T a m b0 b hb p hS cfg hparent
  have htotalW : r^z ≤ eps^4*(∑q∈(univ : Finset (Fin (parentLabels D R a (2^m) p).card)).image
      (parentLabel Sref 0 (2^b)),W q) := by
    rw [hWtotal]
    exact htotal
  obtain ⟨Q,hQP,hQne,hrep,hsep,hret,hfineMass,hbareMass,hterminal⟩ :=
    NativeFineWeightedCoarseCore.same_Q_selection hS hpExp hpz heps univ b hscale
      (fun ell q hq => (H ⟨ell.val,by omega⟩ q hq).1) W hW
      (fun q _hq => hU q) htotalW hcolor hprune
  have hshade : r^(5*z) ≤ ∑q∈Q,NativeCoarseShadingPruning.weight Sref 0 (level-m+6) b rep
      (incidences (sourceCells D R T a (2^m) p)) q :=
    NativeFineWeightedCoarseCore.actual_shading_from_fine_weights hr hS.1.2.2.1 hpz hfineMass
      (hbridge Q) hshadeCost
  let originalRef := sourceCells D R Eref a (2^m) p
  let E := incidences (sourceCells D R T a (2^m) p)
  have hE : ∀v∈E,v.2∈originalRef v.1 := by
    intro v hv
    exact (mem_incidences originalRef v.1 v.2).mp
      (NativeCurrentReferenceIncidenceSubset.source_incidences_mono D R T Eref hTE a (2^m) p hv)
  have hRefDyadic : Sref.thickness=(2:ℝ)⁻¹^(level-m+6) :=
    NativeRelativeCoarseReadback.local_source_dyadic h R Eref a level m p HB.2.1 hmlevel
  have hRefCube : ∀i,Sref.shading i=wzCellShading (mesh Sref) originalRef i :=
    NativeActualRelativeCoarseAdmission.source_common_mesh h R Eref a m p
  have hRefCommon : ∀i,wzGraphTime (Sref.line i) 0-mark (Sref.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ) :=
    NativeActualRelativeCoarseAdmission.source_common_height_zero h R Eref a m p hS
  have hRefCompact : ∀i,Sref.line i∈fixedCompactClass := by
    intro i
    have hi := (mem_parentLabels D R a (2^m) p _).mp
      (NativePaddedCellSource.originalLabel_mem (parentLabels D R a (2^m) p) i)
    exact NativeLocalParentGeometry.mem_fixedCompactClass D a (2^m) p _ hi.2
  have Hcoarse : ∀q : Parent,
      ((univ : Finset (Fin (parentLabels D R a (2^m) p).card)).filter
        (fun i => parentLabel Sref 0 (2^b) i=q)).Nonempty →
      r^z*((1/((2^b:ℕ):ℝ))/r)^3 ≤
        (((univ : Finset (Fin (parentLabels D R a (2^m) p).card)).filter
          (fun i => parentLabel Sref 0 (2^b) i=q)).card:ℝ) := by
    intro q hq
    have hratio : 0 ≤ ((1/((2^b:ℕ):ℝ))/r)^3 := by positivity
    exact (mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_ge hr hS.1.2.2.1 hpz) hratio).trans
      (H ⟨b,by omega⟩ q hq).1
  have hnative := NativeCoarseNativeAdmissibility.native_input hS hRefCompact (hpExp.trans hpz)
    originalRef hRefCube hRefCommon univ (level-m+6) b hRefDyadic hblevel h6 hscale
    Q hQP hQne rep (fun q hq => (hrep q hq).2) E hE hsep Hcoarse hterminal hshade
    hpower hupper hdensity (by simpa only [show 8*z-(etaS+6*z)=2*z-etaS by ring] using hcw)
  have hWQ : (∑q∈Q,W q)=((G (NativeSameQSourceRestriction.restrict D a m b p Q T)).card:ℝ) :=
    NativeSameQFineGraph.sum_weight_eq_graph h R Eref T a m b0 b hb p hS cfg Q hparent
  rw [hWtotal,hWQ] at hret
  rw [hWQ] at hfineMass hbareMass
  refine ⟨Q,hsep,hQP,hQne,fun q hq => (hrep q hq).2,hterminal,hnative,rfl,?_,?_,hret,hfineMass,hbareMass⟩
  · intro i
    exact NativeCoarseRepresentativeGeometry.zero_parent_mem_fixedCompactClass hS hRefCompact hRefCommon
      (rep (NativeCoarseCellSource.parentIndex Q i))
  · rw [NativeCoarseSourceMass.source_total_shading_real]
    exact hshade

end NativeActualFineWeightedSourceSelection
