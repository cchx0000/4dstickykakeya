/- UNVERIFIED same-baseline fine graph to remembered tagged-image bound.
The final local pair keeps its literal intermediate tube index. A tagged
fiber therefore lies in one true old height and one old b-parent, and the
actual fixed-height tube/point bound supplies its capacity. -/
import Theorems.Thm_StickyKakeya4_native_remembered_occurrence_readback
import Theorems.Thm_StickyKakeya4_native_actual_fine_weight_shading_bridge

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 5000000
noncomputable section
namespace NativeRememberedFineCount
open Classical Finset StickyKakeya4 NativeOriginalParentSelection NativeCommonCubicalMesh
open NativeCubicalIncidenceCounts NativeLocalParentSource NativeRelativeCoarseReadback
open NativeRelativeParentLabels NativeRememberedSourceMaps NativeRememberedOccurrenceReadback
open NativeReferenceXYGridPoints NativeHorizontalGrainSlice CanonicalConfiguredE4Bridge
open NativeConfiguredIncidenceFibers NativeCappedOldAncestors NativeActualFineWeightShadingBridge
open NativeTranslatedGrainHeightOverlap

/-- The full reference population is derived from the original backbone.
The original graph stays at b0 even when the intermediate source is at b.
No output count, height-richness, or native input for sparse A is assumed. -/
theorem fine_graph_le_tagged {n : ℕ} {D : FiniteScaleSource n} {eta etaS a zeta pExp : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (R : Finset (Fin n)) (Eref T : Finset (Fin n × Index))
    (level m b0 b : ℕ) (hm : 6 ≤ m) (hb0 : 8 ≤ b0) (hb : b≤b0)
    (HB : NativeMiddleWindowBalance.HasOriginalBackbone D original R a level zeta)
    (hmb0 : m+b0≤level) (hscale : D.thickness≤(rho m)^2) (p : Parent)
    (hp : (parentLabels D R a (2^m) p).Nonempty)
    (hS : IsWangZakharovNativeFiniteInput (source h R Eref a m p) etaS)
    (hbudget : (64:ℝ)^3*(source h R Eref a m p).thickness^pExp≤D.thickness^zeta)
    (hT : T⊆incidences original)
    (hparent : ∀z∈T,z.1∈parentLabels D R a (2^m) p)
    (s : Split) (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (hdim : Module.finrank ℝ P=tangentDim s)
    (F Fcfg : ℤ → Matrix (Fin (normalDim s)) (Fin (tangentDim s)) ℝ)
    (hF : ∀t i j,|F t i j|≤1/4) (hCfg : ∀t i j,|Fcfg t i j|≤1/4)
    (R0 : ℕ) (hR0 : 0<R0) (hbase : rho m≤mu m*(R0:ℝ))
    (hmatch : mu m*(R0:ℝ)=4096/((2^b0:ℕ):ℝ))
    (Q : Finset Parent) (C : FiniteScaleSource Q.card) (c : ℕ) (pA : Parent)
    (A : Finset (Fin n × Index)) (hAT : A⊆T)
    (hAQ : ∀z∈A,relativeLabel D a (2^m) p (2^b) z.1∈Q) :
    let cfg := NativeActualConfiguredPoint.point D a m p s P hP hdim F Fcfg R0
    (∀x∈T.image (fun z => cfg z.2),∀y∈T.image (fun z => cfg z.2),x≠y →
      64/((2^b0:ℕ):ℝ)≤dist x y) →
    let cells := actualRows h R Eref T level m b p hS Q
    let Occ := occurrences h R a m b p hp Q cells A
    ((NativeSameQFineGraph.graph h R Eref a m b0 p hS cfg A).card:ℝ) ≤
      fineCapacity*(source h R Eref a m p).thickness^(-pExp)*
        ((64/((2^b:ℕ):ℝ))/(64/((2^b0:ℕ):ℝ)))^3*
          ((Occ.image (taggedKey D a m C c pA)).card:ℝ) := by
  intro cfg hpointSep cells Occ
  let Sref := source h R Eref a m p
  let eps : ℝ := 64/((2^b0:ℕ):ℝ)
  let d : ℝ := 64/((2^b:ℕ):ℝ)
  let O := NativePackedFrameIsometry.frame s P hP hdim
  let pair := fun z : Fin n × Index => (cfg z.2,outputTube h R Eref a m b0 p hS z.1)
  let G := T.image pair
  let selected := incidences (sourceCells D R T a (2^m) p)
  have hNle : ((2^b:ℕ):ℝ)≤((2^b0:ℕ):ℝ) := by
    simp only [Nat.cast_pow,Nat.cast_ofNat]
    exact pow_le_pow_right₀ (by norm_num) hb
  have hepsd : eps≤d := div_le_div_of_nonneg_left (by norm_num) (by positivity) hNle
  have hstep : 1/((2^b:ℕ):ℝ)≤d :=
    div_le_div_of_nonneg_right (by norm_num) (by positivity)
  have hRefScale : ((2^b0:ℕ):ℝ)*Sref.thickness≤1 :=
    NativeSameReferenceChartBounds.source_scale_guard (a:=a) h R Eref level m b0 p HB.2.1 hmb0
  have Hprofile := NativeSameReferenceChartBounds.population_through h original R level HB Eref m b0 hmb0 p hbudget
  have Hfine : ∀q : Parent,
      ((univ : Finset (Fin (parentLabels D R a (2^m) p).card)).filter
        (fun i => parentLabel Sref 0 (2^b0) i=q)).Nonempty →
      Sref.thickness^pExp*((1/((2^b0:ℕ):ℝ))/Sref.thickness)^3≤
        (((univ : Finset (Fin (parentLabels D R a (2^m) p).card)).filter
          (fun i => parentLabel Sref 0 (2^b0) i=q)).card:ℝ) :=
    fun q hq => (Hprofile ⟨b0,by omega⟩ q hq).1
  have hGgeom : ∀x i,(x,i)∈G → x∈markedUnitTube
      (MarkedIsometricChart.line O 0
        ((NativeFullCoarseShadow.fullSource hS univ 0 (level-m+6) b0 selected).line i)) eps := by
    intro x i hxi
    obtain ⟨z,hz,hzi⟩ := mem_image.mp hxi
    have hk : (NativePaddedCellSource.originalLabel (parentLabels D R a (2^m) p)
        (localIndex h R Eref a m p hS z.1),z.2)∈incidences original := by
      rw [localIndex_readback h R Eref a m p hS z.1 (hparent z hz)]
      exact hT hz
    have hh := NativeActualConfiguredTube.point_mem_full_tube h original horiginal ha R Eref m hm
      hscale p hS (level-m+6) b0 selected (localIndex h R Eref a m p hS z.1) z.2 hk
      s P hP hdim F Fcfg hF hCfg R0 hR0 hbase hmatch.le
    have hx : cfg z.2=x := congrArg Prod.fst hzi
    have hi : outputTube h R Eref a m b0 p hS z.1=i := congrArg Prod.snd hzi
    rw [←hx,←hi]
    exact hh
  have hGpoints : G.image Prod.fst=T.image (fun z => cfg z.2) := by
    dsimp only [G]
    rw [image_image]
    rfl
  have hGsep : ∀x∈G.image Prod.fst,∀y∈G.image Prod.fst,x≠y → eps≤dist x y := by
    rw [hGpoints]
    exact hpointSep
  have hOrig : Occ.image Prod.snd=A := by
    rw [original_image h R Eref T level m b p hp hS hparent HB.2.1
      (by omega) (by omega) Q A hAT]
    exact filter_eq_self.mpr hAQ
  have hImage : Occ.image (fun z => pair z.2)=A.image pair := by
    rw [←hOrig,image_image]
  change ((A.image pair).card:ℝ)≤_
  rw [←hImage]
  apply NativeTangentGridCoarsening.image_card_le_real_mul_of_fiber_images Occ
    (fun z => pair z.2) (taggedKey D a m C c pA)
  intro v _hv
  let V := Occ.filter (fun z => taggedKey D a m C c pA z=v)
  let time := NativeConfiguredTimeCoarsening.finalTime (mu m*(R0:ℝ)) (v.1/((8*R0:ℕ):ℤ))
  have hsub : V.image (fun z => pair z.2)⊆G.filter
      (fun z => z.1 (3:Fin 4)=time ∧ oldAncestor Sref univ 0 b0 b z.2=NativeCoarseCellSource.parentIndex Q v.2.1) := by
    intro u hu
    obtain ⟨z,hz,rfl⟩ := mem_image.mp hu
    obtain ⟨hzO,hzKey⟩ := mem_filter.mp hz
    obtain ⟨_hzCell,hzA,hzPhase,_hshadow⟩ := (mem_occurrences h R a m b p hp Q cells A z).mp hzO
    have hheight : translatedHeight D a m z.2.2=v.1 := congrArg Prod.fst hzKey
    have htube : z.1.1=v.2.1 := congrArg (fun w : ℤ × (Fin Q.card × Index) => w.2.1) hzKey
    refine mem_filter.mpr ⟨mem_image_of_mem _ (hAT hzA),?_,?_⟩
    · change cfg z.2.2 (3:Fin 4)=time
      rw [NativeActualConfiguredPoint.point,NativeActualConfiguredPoint.graphGrid_height,
        NativeActualConfiguredPoint.sourceLabel_height,hheight]
    · change oldAncestor Sref univ 0 b0 b (outputTube h R Eref a m b0 p hS z.2.1)=_
      rw [outputTube_ancestor_readback h R Eref a m b0 b hb p hS z.2.1 (hparent z.2 (hAT hzA)),←hzPhase,htube]
  have hcap := NativeFixedHeightPairCap.full_source_old_parent_height_fiber (a:=0) (e:=pExp)
    hS univ (level-m+6) b0 hb0 selected hRefScale Hfine O
    (NativePackedFrameIsometry.frame_height s P hP hdim) G hGgeom hGsep b hb hepsd hstep
    time (NativeCoarseCellSource.parentIndex Q v.2.1)
  exact (show ((V.image (fun z => pair z.2)).card:ℝ)≤
    ((G.filter (fun z => z.1 (3:Fin 4)=time ∧
      oldAncestor Sref univ 0 b0 b z.2=NativeCoarseCellSource.parentIndex Q v.2.1)).card:ℝ) by
      exact_mod_cast card_le_card hsub).trans hcap

end NativeRememberedFineCount
