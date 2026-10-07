/- UNVERIFIED fixed-height footprint of an actual old full-phase parent. -/
import Theorems.Thm_StickyKakeya4_native_original_phase_chart_gaps
import Theorems.Thm_StickyKakeya4_native_full_chart_tube_graph
import Theorems.Thm_StickyKakeya4_native_matched_shadow_configured_geometry
import Theorems.Thm_StickyKakeya4_native_joint_local_xy_geometry
import Theorems.Thm_StickyKakeya4_native_configured_output_pairs

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
noncomputable section
namespace NativeRememberedPhaseFootprint
open Classical Finset StickyKakeya4 NativeOriginalParentSelection NativeCommonCubicalMesh
open NativeOriginalCellChartGeometry NativeCoarseCellSource NativeCoarseDirectionThinning
open NativeFullCoarseShadow NativeDyadicParentCells NativeFullChartTubeGraph
open NativeMatchedShadowConfiguredGeometry

/-- Two actual fine full-source tube incidences in one old phase parent
and one physical height lie within74w. The phase includes intercepts. -/
theorem full_old_phase_diameter {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (hK : ∀i,D.line i∈fixedCompactClass)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (R : Finset (Fin n)) (level b0 c : ℕ) (hb0 : 8 ≤ b0) (hc : c ≤ b0)
    (E : Finset (Fin n × Index))
    (O : E4 ≃ₗᵢ[ℝ] E4) (hO : ∀x : E4,O x (3:Fin 4)=x (3:Fin 4))
    (i j : Fin (R.image (parentLabel D a (2^b0))).card)
    (hphase : ancestor b0 c (parentIndex (R.image (parentLabel D a (2^b0))) i)=
      ancestor b0 c (parentIndex (R.image (parentLabel D a (2^b0))) j))
    (x y : E4) (ht : x (3:Fin 4)=y (3:Fin 4))
    (hx : x∈markedUnitTube (MarkedIsometricChart.line O 0 ((fullSource h R a level b0 E).line i))
      (64/((2^b0:ℕ):ℝ)))
    (hy : y∈markedUnitTube (MarkedIsometricChart.line O 0 ((fullSource h R a level b0 E).line j))
      (64/((2^b0:ℕ):ℝ))) :
    dist x y ≤ 74*(64/((2^c:ℕ):ℝ)) := by
  let li := MarkedIsometricChart.line O 0 ((fullSource h R a level b0 E).line i)
  let lj := MarkedIsometricChart.line O 0 ((fullSource h R a level b0 E).line j)
  let ri := representative h R a (2^b0) (parentIndex (R.image (parentLabel D a (2^b0))) i)
  let rj := representative h R a (2^b0) (parentIndex (R.image (parentLabel D a (2^b0))) j)
  have hi := (representative_spec h R a (2^b0) (parentIndex_mem _ i)).2
  have hj := (representative_spec h R a (2^b0) (parentIndex_mem _ j)).2
  have hp : parentLabel D a (2^c) ri=parentLabel D a (2^c) rj := by
    rw [←parent_ancestor_eq D a hc ri,←parent_ancestor_eq D a hc rj,hi,hj]
    exact hphase
  have hg := NativeOriginalPhaseChartGaps.original_phase_chart_gaps h hK ha O hO 0
    (by norm_num) (2^c) (by positivity) ri rj hp
  change (∀v : Fin 3,|slope li v-slope lj v| ≤ 672/((2^c:ℕ):ℝ)) ∧
    ∀v : Fin 3,|intercept li v-intercept lj v| ≤ 672/((2^c:ℕ):ℝ) at hg
  have hxb := full_source_graph_bounds h R a level b0 hb0 E O hO i x hx
  have hyb := full_source_graph_bounds h R a level b0 hb0 E O hO j y hy
  have hscale : 64/((2^b0:ℕ):ℝ) ≤ 64/((2^c:ℕ):ℝ) := by
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    exact_mod_cast Nat.pow_le_pow_right (by norm_num : 0<(2:ℕ)) hc
  have hsp (v : Fin 3) : |x v.castSucc-y v.castSucc| ≤ 37*(64/((2^c:ℕ):ℝ)) := by
    have he : x v.castSucc-y v.castSucc=
        (x v.castSucc-intercept li v-slope li v*x (3:Fin 4))-
        (y v.castSucc-intercept lj v-slope lj v*y (3:Fin 4))+
        (intercept li v-intercept lj v)+x (3:Fin 4)*(slope li v-slope lj v) := by rw [ht]; ring
    have htprod : |x (3:Fin 4)*(slope li v-slope lj v)| ≤ 672/((2^c:ℕ):ℝ) := by
      rw [abs_mul]
      exact (mul_le_mul hxb.1 (hg.1 v) (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)
    rw [he]
    have hh := abs_add_le
      ((x v.castSucc-intercept li v-slope li v*x (3:Fin 4))-
        (y v.castSucc-intercept lj v-slope lj v*y (3:Fin 4))+
        (intercept li v-intercept lj v)) (x (3:Fin 4)*(slope li v-slope lj v))
    have hh2 := abs_add_le
      ((x v.castSucc-intercept li v-slope li v*x (3:Fin 4))-
        (y v.castSucc-intercept lj v-slope lj v*y (3:Fin 4))) (intercept li v-intercept lj v)
    have hh3 := abs_sub
      (x v.castSucc-intercept li v-slope li v*x (3:Fin 4))
      (y v.castSucc-intercept lj v-slope lj v*y (3:Fin 4))
    linarith only [hh,hh2,hh3,hxb.2 v,hyb.2 v,hg.2 v,htprod,hscale]
  apply (distance_of_coordinates x y (37*(64/((2^c:ℕ):ℝ))) (by positivity) ?_).trans_eq (by ring)
  intro v
  refine Fin.lastCases ?_ (fun v => hsp v) v
  rw [show (Fin.last 3:Fin 4)=3 by rfl,ht,sub_self,abs_zero]
  positivity

open NativeReferenceXYGridPoints NativeHorizontalGrainSlice CanonicalConfiguredE4Bridge
open NativeLocalParentSource NativeConfiguredIncidenceFibers NativeRelativeParentLabels
open NativeTranslatedGrainHeightOverlap NativeNormalizedCellRelativeMenu
open scoped Matrix.Norms.Elementwise

/-- Same-source version: both points are the original configured map, both
fine tubes are its unchanged full-source representatives, and the old phase
is read through the actual outputTube ancestor identity. -/
theorem actual_configured_diameter {n : ℕ} {D : FiniteScaleSource n} {eta etaS a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (backbone : Finset (Fin n)) (Eref T : Finset (Fin n × Index)) (m : ℕ) (hm : 6 ≤ m)
    (hscale : D.thickness ≤ (rho m)^2) (p : Parent)
    (hS : IsWangZakharovNativeFiniteInput (NativeLocalParentSource.source h backbone Eref a m p) etaS)
    (hSK : ∀i,(NativeLocalParentSource.source h backbone Eref a m p).line i∈fixedCompactClass)
    (levelS b0 c : ℕ) (hb0 : 8 ≤ b0) (hc : c ≤ b0)
    (s : Split) (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (hd : Module.finrank ℝ P=tangentDim s)
    (F Fcfg : ℤ → Matrix (Fin (normalDim s)) (Fin (tangentDim s)) ℝ)
    (hF : ∀t i j,|F t i j| ≤ 1/4) (hCfg : ∀t i j,|Fcfg t i j| ≤ 1/4)
    (R0 : ℕ) (hR0 : 0 < R0) (hbase : rho m ≤ mu m*(R0:ℝ))
    (hmatch : mu m*(R0:ℝ) ≤ 4096/((2^b0:ℕ):ℝ))
    (z z' : Fin n × Index)
    (hz : z∈NativeCubicalIncidenceCounts.incidences original)
    (hz' : z'∈NativeCubicalIncidenceCounts.incidences original)
    (hzP : z.1∈parentLabels D backbone a (2^m) p)
    (hzP' : z'.1∈parentLabels D backbone a (2^m) p)
    (ht : translatedHeight D a m z.2=translatedHeight D a m z'.2)
    (hphase : relativeLabel D a (2^m) p (2^c) z.1=relativeLabel D a (2^m) p (2^c) z'.1) :
    dist (NativeActualConfiguredPoint.point D a m p s P hP hd F Fcfg R0 z.2)
      (NativeActualConfiguredPoint.point D a m p s P hP hd F Fcfg R0 z'.2) ≤
        74*(64/((2^c:ℕ):ℝ)) := by
  let S := NativeLocalParentSource.source h backbone Eref a m p
  let O := NativePackedFrameIsometry.frame s P hP hd
  let selected := NativeCubicalIncidenceCounts.incidences
    (NativeLocalParentSource.sourceCells D backbone T a (2^m) p)
  let cfg := NativeActualConfiguredPoint.point D a m p s P hP hd F Fcfg R0
  have hTube (v : Fin n × Index) (hv : v∈NativeCubicalIncidenceCounts.incidences original)
      (hvP : v.1∈parentLabels D backbone a (2^m) p) :
      cfg v.2∈markedUnitTube
        (MarkedIsometricChart.line O 0 ((fullSource hS univ 0 levelS b0 selected).line
          (outputTube h backbone Eref a m b0 p hS v.1))) (64/((2^b0:ℕ):ℝ)) := by
    let i := localIndex h backbone Eref a m p hS v.1
    have hr := localIndex_readback h backbone Eref a m p hS v.1 hvP
    have hv' : (NativePaddedCellSource.originalLabel (parentLabels D backbone a (2^m) p) i,v.2)∈
        NativeCubicalIncidenceCounts.incidences original := by rw [hr]; exact hv
    exact NativeActualConfiguredTube.point_mem_full_tube h original horiginal ha backbone Eref m hm
      hscale p hS levelS b0 selected i v.2 hv' s P hP hd F Fcfg hF hCfg R0 hR0 hbase hmatch
  have hAnc : ancestor b0 c (parentIndex (univ.image (parentLabel S 0 (2^b0)))
      (outputTube h backbone Eref a m b0 p hS z.1))=
      ancestor b0 c (parentIndex (univ.image (parentLabel S 0 (2^b0)))
      (outputTube h backbone Eref a m b0 p hS z'.1)) := by
    rw [outputTube_ancestor_readback h backbone Eref a m b0 c hc p hS z.1 hzP,
      outputTube_ancestor_readback h backbone Eref a m b0 c hc p hS z'.1 hzP']
    exact hphase
  have hTime : cfg z.2 (3:Fin 4)=cfg z'.2 (3:Fin 4) := by
    simp only [cfg,NativeActualConfiguredPoint.point,NativeActualConfiguredPoint.graphGrid_height,
      NativeActualConfiguredPoint.sourceLabel_height,ht]
  exact full_old_phase_diameter hS hSK
    (NativeActualRelativeCoarseAdmission.source_common_height_zero h backbone Eref a m p hS)
    univ levelS b0 c hb0 hc selected O (NativePackedFrameIsometry.frame_height s P hP hd)
    _ _ hAnc _ _ hTime (hTube z hz hzP) (hTube z' hz' hzP')

/-- Convert the configured-point diameter back to literal old physical
cells. This uses the same raw point and the actual first-parent rounding. -/
theorem oldPoint_dist_of_configured {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (m : ℕ) (hm : 6 ≤ m) (p : Parent)
    (i : Fin n) (hi : parentLabel D a (2^m) i=p)
    (s : Split) (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (hd : Module.finrank ℝ P=tangentDim s)
    (F Fcfg : ℤ → Matrix (Fin (normalDim s)) (Fin (tangentDim s)) ℝ)
    (hF : ∀t i j,|F t i j| ≤ 1/4) (hCfg : ∀t i j,|Fcfg t i j| ≤ 1/4)
    (R0 : ℕ) (hR0 : 0 < R0) (hbase : rho m ≤ mu m*(R0:ℝ))
    {w : ℝ} (hw : 0 < w) (hmu : mu m ≤ w) (hwidth : mu m*(R0:ℝ) ≤ 64*w)
    (k l : Index)
    (hclose : dist (NativeActualConfiguredPoint.point D a m p s P hP hd F Fcfg R0 k)
      (NativeActualConfiguredPoint.point D a m p s P hP hd F Fcfg R0 l) ≤ 74*w) :
    dist (oldPoint D a m p k) (oldPoint D a m p l) ≤ 128*(512*w) := by
  let O := NativePackedFrameIsometry.frame s P hP hd
  let cfg := NativeActualConfiguredPoint.point D a m p s P hP hd F Fcfg R0
  let x := O ((1/512:ℝ) • rawPoint D a m p k)
  let y := O ((1/512:ℝ) • rawPoint D a m p l)
  have hk := NativeActualConfiguredPoint.point_distance D a m hm p s P hP hd F Fcfg hF hCfg R0 hR0 k hbase
  have hl := NativeActualConfiguredPoint.point_distance D a m hm p s P hP hd F Fcfg hF hCfg R0 hR0 l hbase
  have htri := dist_triangle x (cfg k) y
  have htri2 := dist_triangle (cfg k) (cfg l) y
  have hs : dist x y=(1/512:ℝ)*dist (rawPoint D a m p k) (rawPoint D a m p l) := by
    simp only [x,y,O.dist_map,dist_eq_norm,←smul_sub,norm_smul,Real.norm_eq_abs]
    norm_num
  have hraw : dist (rawPoint D a m p k) (rawPoint D a m p l) ≤
      6*(mu m*(R0:ℝ))+512*(74*w) := by
    change dist (cfg k) x ≤ _ at hk
    change dist (cfg l) y ≤ _ at hl
    rw [dist_comm x (cfg k),hs] at htri
    nlinarith only [hk,hl,htri,htri2,hclose]
  have hOldK := physical_rounding h m hm p i hi k
  have hOldL := physical_rounding h m hm p i hi l
  have hOldTri := dist_triangle (oldPoint D a m p k) (rawPoint D a m p k) (oldPoint D a m p l)
  have hOldTri2 := dist_triangle (rawPoint D a m p k) (rawPoint D a m p l) (oldPoint D a m p l)
  rw [dist_comm (oldPoint D a m p k) (rawPoint D a m p k)] at hOldTri
  nlinarith only [hraw,hOldK,hOldL,hOldTri,hOldTri2,hmu,hwidth,hw]


end NativeRememberedPhaseFootprint
