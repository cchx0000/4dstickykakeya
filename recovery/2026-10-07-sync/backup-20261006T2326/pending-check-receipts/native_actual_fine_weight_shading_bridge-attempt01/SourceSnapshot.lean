import Theorems.Thm_StickyKakeya4_native_same_Q_fine_graph
import Theorems.Thm_StickyKakeya4_native_same_Q_shadow_mass
import Theorems.Thm_StickyKakeya4_native_fixed_height_pair_cap
import Theorems.Thm_StickyKakeya4_native_matched_shadow_configured_geometry
import Theorems.Thm_StickyKakeya4_native_actual_configured_height_caps
import Theorems.Thm_StickyKakeya4_native_matched_height_bound
import Theorems.Thm_StickyKakeya4_native_tangent_grid_coarsening
import Theorems.Thm_StickyKakeya4_native_fine_weighted_coarse_core

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 6000000

noncomputable section
namespace NativeActualFineWeightShadingBridge
open Classical Finset MeasureTheory StickyKakeya4 NativeCommonCubicalMesh
open NativeOriginalParentSelection NativeOriginalCellChartGeometry NativeCubicalIncidenceCounts
open NativeLocalParentSource NativeRelativeParentLabels NativeRelativeCoarseReadback
open NativeRelativeCoarsePointMenu NativeConfiguredIncidenceFibers NativeReferenceXYGridPoints
open NativeHorizontalGrainSlice CanonicalConfiguredE4Bridge NativeSameQSourceRestriction
open NativeFineWeightedCoarseCore NativeCappedOldAncestors
open scoped BigOperators ENNReal

/-- The actual half-thickness cell volume cancels the four fine-to-coarse
powers. The input counts fine pairs above their witnessed shadow cells. -/
lemma pair_capacity_to_shading {r eps d p G S : ℝ}
    (hr : 0 < r) (heps : 0 < eps)
    (hcount : G ≤ 34*fineCapacity*r^(-p)*(d/eps)^4*S) :
    r^p*eps^4*G/(544*fineCapacity) ≤ S*(d/2)^4 := by
  have hCf := fineCapacity_pos
  calc
    _ = (r^p*eps^4/(544*fineCapacity))*G := by ring
    _ ≤ (r^p*eps^4/(544*fineCapacity))*(34*fineCapacity*r^(-p)*(d/eps)^4*S) :=
      mul_le_mul_of_nonneg_left hcount (by positivity)
    _ = _ := by
      rw [Real.rpow_neg hr.le]
      field_simp [heps.ne',hCf.ne',(Real.rpow_pos_of_pos hr p).ne']

/-- Literal configured fine pairs are grouped by the coarse shadow of each
original occurrence. The image-fiber lemma retains all such witnesses and
requires no well-defined shadow map on deduplicated fine pairs. Each shadow
fiber has at most 34d/eps original configured heights; each one-height fiber
is bounded by the actual same-reference angular/point capacity. The displayed
D.thickness ≤ (rho m)^2 guard belongs only to construction of this INITIAL
reference. It is not a guard on the selected coarse source or a later parent. -/
theorem fine_graph_le_shadow {n : ℕ} {D : FiniteScaleSource n} {eta etaS a pExp : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (R : Finset (Fin n)) (Eref T : Finset (Fin n × Index))
    (level m b0 b : ℕ) (hm : 6 ≤ m) (hb0 : 8 ≤ b0) (hb : b ≤ b0)
    (hdy : D.thickness=(2:ℝ)⁻¹^level) (hmb0 : m+b0 ≤ level)
    (hscale : D.thickness ≤ (rho m)^2) (p : Parent)
    (hQ : (parentLabels D R a (2^m) p).Nonempty)
    (hS : IsWangZakharovNativeFiniteInput (source h R Eref a m p) etaS)
    (hT : T⊆incidences original)
    (hparent : ∀z∈T,z.1∈parentLabels D R a (2^m) p)
    (Hfine : ∀q : Parent,
      ((univ : Finset (Fin (parentLabels D R a (2^m) p).card)).filter
        (fun i => parentLabel (source h R Eref a m p) 0 (2^b0) i=q)).Nonempty →
      (source h R Eref a m p).thickness^pExp*
        ((1/((2^b0:ℕ):ℝ))/(source h R Eref a m p).thickness)^3 ≤
      (((univ : Finset (Fin (parentLabels D R a (2^m) p).card)).filter
        (fun i => parentLabel (source h R Eref a m p) 0 (2^b0) i=q)).card:ℝ))
    (s : Split) (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (hdim : Module.finrank ℝ P=tangentDim s)
    (F Fcfg : ℤ → Matrix (Fin (normalDim s)) (Fin (tangentDim s)) ℝ)
    (hF : ∀t u v,|F t u v| ≤ 1/4) (hCfg : ∀t u v,|Fcfg t u v| ≤ 1/4)
    (R0 : ℕ) (hR0 : 0 < R0) (hbase : rho m ≤ mu m*(R0:ℝ))
    (hmatch : mu m*(R0:ℝ)=4096/((2^b0:ℕ):ℝ)) :
    let cfg := NativeActualConfiguredPoint.point D a m p s P hP hdim F Fcfg R0
    (∀x∈T.image (fun z => cfg z.2),∀y∈T.image (fun z => cfg z.2),x≠y →
      64/((2^b0:ℕ):ℝ) ≤ dist x y) →
    ((NativeSameQFineGraph.graph h R Eref a m b0 p hS cfg T).card:ℝ) ≤
      34*fineCapacity*(source h R Eref a m p).thickness^(-pExp)*
        ((64/((2^b:ℕ):ℝ))/(64/((2^b0:ℕ):ℝ)))^4*
        ((T.image (doublePair h R a m p hQ (2^b))).card:ℝ) := by
  intro cfg hpointSep
  let Sref := source h R Eref a m p
  let eps : ℝ := 64/((2^b0:ℕ):ℝ)
  let d : ℝ := 64/((2^b:ℕ):ℝ)
  let O := NativePackedFrameIsometry.frame s P hP hdim
  let pair := fun z : Fin n × Index => (cfg z.2,outputTube h R Eref a m b0 p hS z.1)
  let shadow := doublePair h R a m p hQ (2^b)
  let G := T.image pair
  let selected := incidences (sourceCells D R T a (2^m) p)
  have hr : 0 < Sref.thickness := hS.1.2.1
  have heps : 0 < eps := by dsimp [eps]; positivity
  have hd : 0 < d := by dsimp [d]; positivity
  have hNb : (0:ℝ) < ((2^b:ℕ):ℝ) := by positivity
  have hNle : ((2^b:ℕ):ℝ) ≤ ((2^b0:ℕ):ℝ) := by
    simp only [Nat.cast_pow,Nat.cast_ofNat]
    exact pow_le_pow_right₀ (by norm_num) hb
  have hepsd : eps ≤ d := div_le_div_of_nonneg_left (by norm_num) hNb hNle
  have hstep : 1/((2^b:ℕ):ℝ) ≤ d :=
    div_le_div_of_nonneg_right (by norm_num) hNb.le
  have hmatchCoarse : mu m*(R0:ℝ) ≤ 4096/((2^b:ℕ):ℝ) := by
    rw [hmatch]
    exact div_le_div_of_nonneg_left (by norm_num) hNb hNle
  have hRefScale : ((2^b0:ℕ):ℝ)*Sref.thickness ≤ 1 :=
    NativeSameReferenceChartBounds.source_scale_guard (a:=a) h R Eref level m b0 p hdy hmb0
  have hNscale : ((2^m:ℕ):ℝ)*D.thickness ≤ 1 :=
    NativeCompactAncestorRegularity.dyadic_parent_scale hdy ⟨m,by omega⟩
  have hRelScale : ((2^m:ℕ):ℝ)*D.thickness*((2^b:ℕ):ℝ) ≤ 64 := by
    calc
      _ = ((2^(m+b):ℕ):ℝ)*D.thickness := by push_cast; rw [pow_add]; ring
      _ ≤ 1 := NativeCompactAncestorRegularity.dyadic_parent_scale hdy ⟨m+b,by omega⟩
      _ ≤ 64 := by norm_num
  have hGgeom : ∀x i,(x,i)∈G → x∈markedUnitTube
      (MarkedIsometricChart.line O 0
        ((NativeFullCoarseShadow.fullSource hS univ 0 (level-m+6) b0 selected).line i)) eps := by
    have hh := configured_incidence_geometry h original horiginal ha R Eref m hm hscale b0
      (level-m+6) p hS selected s P hP hdim F Fcfg hF hCfg R0 hR0 hbase hmatch.le T hparent hT
    intro x i hxi
    exact hh (x,i) hxi
  have hGpoints : G.image Prod.fst=T.image (fun z => cfg z.2) := by
    dsimp only [G]
    rw [image_image]
    rfl
  have hGsep : ∀x∈G.image Prod.fst,∀y∈G.image Prod.fst,x≠y → eps ≤ dist x y := by
    rw [hGpoints]
    exact hpointSep
  change (G.card:ℝ) ≤ 34*fineCapacity*Sref.thickness^(-pExp)*(d/eps)^4*(T.image shadow).card
  apply NativeTangentGridCoarsening.image_card_le_real_mul_of_fiber_images T pair shadow
  intro v _hv
  let A := T.filter (fun z => shadow z=v)
  let I := A.image pair
  let Z := I.image (fun z => z.1 (3:Fin 4))
  let center := (cellCenter (32/((2^b:ℕ):ℝ)) v.2) (3:Fin 4)
  have hAT : A⊆T := filter_subset _ _
  have hIG : I⊆G := image_subset_image hAT
  have hZread : Z=(A.image Prod.snd).image (fun k => cfg k (3:Fin 4)) := by
    dsimp only [Z,I]
    rw [image_image,image_image]
    rfl
  have htime : ∀z∈Z,center-2*d ≤ z ∧ z ≤ (center-2*d)+4*d := by
    intro z hz
    obtain ⟨u,hu,rfl⟩ := mem_image.mp hz
    obtain ⟨w,hw,rfl⟩ := mem_image.mp hu
    have hwT := hAT hw
    have hcell : NativeRelativeCoarsePointMenu.doubleLabel D a (2^m) (2^b) p
        (originalRepresentative h R a m p hQ (2^b)
          (relativeLabel D a (2^m) p (2^b) w.1)) w.1 w.2=v.2 :=
      congrArg Prod.snd (mem_filter.mp hw).2
    have hh := NativeMatchedShadowConfiguredGeometry.point_shadow_center_distance
      h original horiginal ha m (2^b) hm (by positivity) hNscale hRelScale p w.1
      (originalRepresentative h R a m p hQ (2^b)
        (relativeLabel D a (2^m) p (2^b) w.1)) w.2
      ((mem_incidences original w.1 w.2).mp (hT hwT))
      ((mem_parentLabels D R a (2^m) p w.1).mp (hparent w hwT)).2
      (originalRepresentative_label h R a m p hQ (2^b) w.1 (hparent w hwT))
      s P hP hdim F Fcfg hF hCfg R0 hR0 hbase hmatchCoarse
    rw [hcell] at hh
    have hc : |cfg w.2 (3:Fin 4)-center| ≤ 2*d := by
      have hx : |cfg w.2 (3:Fin 4)-(O (cellCenter (32/((2^b:ℕ):ℝ)) v.2)) (3:Fin 4)| ≤
          dist (cfg w.2) (O (cellCenter (32/((2^b:ℕ):ℝ)) v.2)) := by
        simpa only [Real.dist_eq] using PiLp.dist_apply_le
          (cfg w.2) (O (cellCenter (32/((2^b:ℕ):ℝ)) v.2)) (3:Fin 4)
      rw [show (O (cellCenter (32/((2^b:ℕ):ℝ)) v.2)) (3:Fin 4)=center from
        NativePackedFrameIsometry.frame_height s P hP hdim _] at hx
      exact hx.trans hh
    have hlo := (abs_le.mp hc).1
    have hhi := (abs_le.mp hc).2
    change center-2*d ≤ cfg w.2 (3:Fin 4) ∧ cfg w.2 (3:Fin 4) ≤ (center-2*d)+4*d
    constructor <;> linarith only [hlo,hhi]
  have hZfilter : Z.filter (fun z => center-2*d ≤ z ∧ z ≤ (center-2*d)+4*d)=Z :=
    filter_eq_self.mpr htime
  have hmesh : (mu m*(R0:ℝ))/512=eps/8 := by rw [hmatch]; dsimp [eps]; ring
  have hZcap : (Z.card:ℝ) ≤ 34*d/eps := by
    have hh := NativeActualConfiguredHeightCaps.actual_height_interval_cap D a m p s P hP hdim
      F Fcfg R0 hR0 (A.image Prod.snd) (center-2*d) (4*d) (by positivity)
    rw [←hZread,hZfilter,hmesh] at hh
    have hratio : 1 ≤ d/eps := (le_div_iff₀ heps).mpr (by simpa only [one_mul] using hepsd)
    calc
      _ ≤ 4*d/(eps/8)+2 := hh
      _ = 32*(d/eps)+2 := by ring
      _ ≤ 34*(d/eps) := by linarith only [hratio]
      _ = _ := by ring
  have hcap (z : ℝ) : ((I.filter (fun u => u.1 (3:Fin 4)=z)).card:ℝ) ≤
      fineCapacity*Sref.thickness^(-pExp)*(d/eps)^3 := by
    have hsub : I.filter (fun u => u.1 (3:Fin 4)=z) ⊆ G.filter
        (fun u => u.1 (3:Fin 4)=z ∧ oldAncestor Sref univ 0 b0 b u.2=v.1) := by
      intro u hu
      have huI := (mem_filter.mp hu).1
      obtain ⟨w,hw,hwu⟩ := mem_image.mp huI
      have hpw : relativeLabel D a (2^m) p (2^b) w.1=v.1 :=
        congrArg Prod.fst (mem_filter.mp hw).2
      refine mem_filter.mpr ⟨hIG huI,(mem_filter.mp hu).2,?_⟩
      rw [←hwu]
      exact (outputTube_ancestor_readback h R Eref a m b0 b hb p hS w.1 (hparent w (hAT hw))).trans hpw
    have hh := NativeFixedHeightPairCap.full_source_old_parent_height_fiber (a:=0) (e:=pExp)
      hS univ (level-m+6) b0 hb0 selected hRefScale Hfine O
      (NativePackedFrameIsometry.frame_height s P hP hdim) G hGgeom hGsep b hb hepsd hstep z v.1
    exact (show ((I.filter (fun u => u.1 (3:Fin 4)=z)).card:ℝ) ≤
      ((G.filter (fun u => u.1 (3:Fin 4)=z ∧ oldAncestor Sref univ 0 b0 b u.2=v.1)).card:ℝ) by
        exact_mod_cast card_le_card hsub).trans hh
  have hCf := fineCapacity_pos
  change (I.card:ℝ) ≤ _
  calc
    _ = ∑z∈Z,((I.filter (fun u => u.1 (3:Fin 4)=z)).card:ℝ) := by
      exact_mod_cast card_eq_sum_card_image (fun u => u.1 (3:Fin 4)) I
    _ ≤ ∑_z∈Z,fineCapacity*Sref.thickness^(-pExp)*(d/eps)^3 :=
      sum_le_sum (fun z _hz => hcap z)
    _ = (fineCapacity*Sref.thickness^(-pExp)*(d/eps)^3)*(Z.card:ℝ) := by simp [mul_comm]
    _ ≤ (fineCapacity*Sref.thickness^(-pExp)*(d/eps)^3)*(34*d/eps) :=
      mul_le_mul_of_nonneg_left hZcap (by positivity)
    _ = _ := by ring

/-- The actual fine-pair/shading bridge on every specified Q. Its left side
uses the unchanged baseline fine tube indices; its right side is the actual
original-T coarse shading on that very Q. No lower coarse graph count or
native assumption on the selected coarse source occurs among the premises. -/
theorem same_Q_weight_shading {n : ℕ} {D : FiniteScaleSource n} {eta etaS a pExp : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (R : Finset (Fin n)) (Eref T : Finset (Fin n × Index))
    (level m b0 b : ℕ) (hm : 6 ≤ m) (hb0 : 8 ≤ b0) (hb : b ≤ b0)
    (hdy : D.thickness=(2:ℝ)⁻¹^level) (hmb0 : m+b0 ≤ level)
    (hscale : D.thickness ≤ (rho m)^2) (p : Parent)
    (hQ : (parentLabels D R a (2^m) p).Nonempty)
    (hS : IsWangZakharovNativeFiniteInput (source h R Eref a m p) etaS)
    (hT : T⊆incidences original)
    (hparent : ∀z∈T,z.1∈parentLabels D R a (2^m) p)
    (Hfine : ∀q : Parent,
      ((univ : Finset (Fin (parentLabels D R a (2^m) p).card)).filter
        (fun i => parentLabel (source h R Eref a m p) 0 (2^b0) i=q)).Nonempty →
      (source h R Eref a m p).thickness^pExp*
        ((1/((2^b0:ℕ):ℝ))/(source h R Eref a m p).thickness)^3 ≤
      (((univ : Finset (Fin (parentLabels D R a (2^m) p).card)).filter
        (fun i => parentLabel (source h R Eref a m p) 0 (2^b0) i=q)).card:ℝ))
    (s : Split) (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (hdim : Module.finrank ℝ P=tangentDim s)
    (F Fcfg : ℤ → Matrix (Fin (normalDim s)) (Fin (tangentDim s)) ℝ)
    (hF : ∀t u v,|F t u v| ≤ 1/4) (hCfg : ∀t u v,|Fcfg t u v| ≤ 1/4)
    (R0 : ℕ) (hR0 : 0 < R0) (hbase : rho m ≤ mu m*(R0:ℝ))
    (hmatch : mu m*(R0:ℝ)=4096/((2^b0:ℕ):ℝ)) :
    let cfg := NativeActualConfiguredPoint.point D a m p s P hP hdim F Fcfg R0
    (∀x∈T.image (fun z => cfg z.2),∀y∈T.image (fun z => cfg z.2),x≠y →
      64/((2^b0:ℕ):ℝ) ≤ dist x y) →
    ∀Q : Finset Parent,
      (source h R Eref a m p).thickness^pExp*(64/((2^b0:ℕ):ℝ))^4*
        (∑q∈Q,NativeSameQFineGraph.weight h R Eref a m b0 b p hS cfg T q)/(544*fineCapacity) ≤
      ∑q∈Q,NativeCoarseShadingPruning.weight (source h R Eref a m p) 0 (level-m+6) b
        (NativeCoarseDirectionThinning.representative hS univ 0 (2^b))
        (incidences (sourceCells D R T a (2^m) p)) q := by
  intro cfg hpointSep Q
  let TQ := restrict D a m b p Q T
  have hTQT : TQ⊆T := filter_subset _ _
  have hcount := fine_graph_le_shadow h original horiginal ha R Eref TQ level m b0 b hm hb0 hb
    hdy hmb0 hscale p hQ hS (hTQT.trans hT) (fun z hz => hparent z (hTQT hz)) Hfine
    s P hP hdim F Fcfg hF hCfg R0 hR0 hbase hmatch
    (fun x hx y hy hxy => hpointSep x (image_subset_image hTQT hx) y (image_subset_image hTQT hy) hxy)
  rw [NativeSameQFineGraph.sum_weight_eq_graph h R Eref T a m b0 b hb p hS cfg Q hparent,
    NativeSameQShadowMass.sum_shadow_weight_eq_pairs h R Eref T a level m b p hS hparent hQ hdy
      (by omega) (by omega) Q]
  have hh := pair_capacity_to_shading hS.1.2.1 (by positivity : 0 < 64/((2^b0:ℕ):ℝ)) hcount
  simpa only [show (64/((2^b:ℕ):ℝ))/2=32/((2^b:ℕ):ℝ) by ring] using hh

/-- The selector's per-parent U is also an actual fine-pair count. The
same fixed-height capacity is summed over the unchanged baseline's at most
18/eps actual configured heights. No new selection or coarse shading lower
bound is used, and hscale is again only the INITIAL-reference guard. -/
theorem actual_weight_upper {n : ℕ} {D : FiniteScaleSource n} {eta etaS a pExp : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (R : Finset (Fin n)) (Eref T : Finset (Fin n × Index))
    (level m b0 b : ℕ) (hm : 6 ≤ m) (hb0 : 8 ≤ b0) (hb : b ≤ b0)
    (hdy : D.thickness=(2:ℝ)⁻¹^level) (hmb0 : m+b0 ≤ level)
    (hscale : D.thickness ≤ (rho m)^2) (p : Parent)
    (hS : IsWangZakharovNativeFiniteInput (source h R Eref a m p) etaS)
    (hT : T⊆incidences original)
    (hparent : ∀z∈T,z.1∈parentLabels D R a (2^m) p)
    (Hfine : ∀q : Parent,
      ((univ : Finset (Fin (parentLabels D R a (2^m) p).card)).filter
        (fun i => parentLabel (source h R Eref a m p) 0 (2^b0) i=q)).Nonempty →
      (source h R Eref a m p).thickness^pExp*
        ((1/((2^b0:ℕ):ℝ))/(source h R Eref a m p).thickness)^3 ≤
      (((univ : Finset (Fin (parentLabels D R a (2^m) p).card)).filter
        (fun i => parentLabel (source h R Eref a m p) 0 (2^b0) i=q)).card:ℝ))
    (s : Split) (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (hdim : Module.finrank ℝ P=tangentDim s)
    (F Fcfg : ℤ → Matrix (Fin (normalDim s)) (Fin (tangentDim s)) ℝ)
    (hF : ∀t u v,|F t u v| ≤ 1/4) (hCfg : ∀t u v,|Fcfg t u v| ≤ 1/4)
    (R0 : ℕ) (hR0 : 0 < R0) (hbase : rho m ≤ mu m*(R0:ℝ))
    (hmatch : mu m*(R0:ℝ)=4096/((2^b0:ℕ):ℝ)) :
    let cfg := NativeActualConfiguredPoint.point D a m p s P hP hdim F Fcfg R0
    (∀x∈T.image (fun z => cfg z.2),∀y∈T.image (fun z => cfg z.2),x≠y →
      64/((2^b0:ℕ):ℝ) ≤ dist x y) →
    ∀q : Parent,NativeSameQFineGraph.weight h R Eref a m b0 b p hS cfg T q ≤
      18*fineCapacity*(source h R Eref a m p).thickness^(-pExp)*
        (64/((2^b:ℕ):ℝ))^3/(64/((2^b0:ℕ):ℝ))^4 := by
  intro cfg hpointSep q
  let Sref := source h R Eref a m p
  let eps : ℝ := 64/((2^b0:ℕ):ℝ)
  let d : ℝ := 64/((2^b:ℕ):ℝ)
  let O := NativePackedFrameIsometry.frame s P hP hdim
  let pair := fun z : Fin n × Index => (cfg z.2,outputTube h R Eref a m b0 p hS z.1)
  let G := T.image pair
  let selected := incidences (sourceCells D R T a (2^m) p)
  let J := G.filter (fun u => NativeSameQFineGraph.phase h R Eref a m b0 b p u.2=q)
  let Z := G.image (fun u => u.1 (3:Fin 4))
  have hr : 0 < Sref.thickness := hS.1.2.1
  have heps : 0 < eps := by dsimp [eps]; positivity
  have hd : 0 < d := by dsimp [d]; positivity
  have hNb : (0:ℝ) < ((2^b:ℕ):ℝ) := by positivity
  have hNle : ((2^b:ℕ):ℝ) ≤ ((2^b0:ℕ):ℝ) := by
    simp only [Nat.cast_pow,Nat.cast_ofNat]
    exact pow_le_pow_right₀ (by norm_num) hb
  have hepsd : eps ≤ d := div_le_div_of_nonneg_left (by norm_num) hNb hNle
  have hstep : 1/((2^b:ℕ):ℝ) ≤ d :=
    div_le_div_of_nonneg_right (by norm_num) hNb.le
  have hRefScale : ((2^b0:ℕ):ℝ)*Sref.thickness ≤ 1 :=
    NativeSameReferenceChartBounds.source_scale_guard (a:=a) h R Eref level m b0 p hdy hmb0
  have hGgeom : ∀x i,(x,i)∈G → x∈markedUnitTube
      (MarkedIsometricChart.line O 0
        ((NativeFullCoarseShadow.fullSource hS univ 0 (level-m+6) b0 selected).line i)) eps := by
    have hh := configured_incidence_geometry h original horiginal ha R Eref m hm hscale b0
      (level-m+6) p hS selected s P hP hdim F Fcfg hF hCfg R0 hR0 hbase hmatch.le T hparent hT
    intro x i hxi
    exact hh (x,i) hxi
  have hGpoints : G.image Prod.fst=T.image (fun z => cfg z.2) := by
    dsimp only [G]
    rw [image_image]
    rfl
  have hGsep : ∀x∈G.image Prod.fst,∀y∈G.image Prod.fst,x≠y → eps ≤ dist x y := by
    rw [hGpoints]
    exact hpointSep
  have hZread : Z=T.image (fun z => cfg z.2 (3:Fin 4)) := by
    dsimp only [Z,G]
    rw [image_image]
    rfl
  have hZcap : (Z.card:ℝ) ≤ 18/eps := by
    rw [hZread]
    exact NativeMatchedHeightBound.baseline_height_bound h original horiginal ha T hT m b0
      (by omega) p s P hP hdim F Fcfg R0 hR0 hmatch
  have hcap (z : ℝ) : ((J.filter (fun u => u.1 (3:Fin 4)=z)).card:ℝ) ≤
      fineCapacity*Sref.thickness^(-pExp)*(d/eps)^3 := by
    have hsub : J.filter (fun u => u.1 (3:Fin 4)=z) ⊆ G.filter
        (fun u => u.1 (3:Fin 4)=z ∧ oldAncestor Sref univ 0 b0 b u.2=q) := by
      intro u hu
      obtain ⟨huJ,hz⟩ := mem_filter.mp hu
      obtain ⟨huG,hphase⟩ := mem_filter.mp huJ
      exact mem_filter.mpr ⟨huG,hz,hphase⟩
    have hh := NativeFixedHeightPairCap.full_source_old_parent_height_fiber (a:=0) (e:=pExp)
      hS univ (level-m+6) b0 hb0 selected hRefScale Hfine O
      (NativePackedFrameIsometry.frame_height s P hP hdim) G hGgeom hGsep b hb hepsd hstep z q
    exact (show ((J.filter (fun u => u.1 (3:Fin 4)=z)).card:ℝ) ≤
      ((G.filter (fun u => u.1 (3:Fin 4)=z ∧ oldAncestor Sref univ 0 b0 b u.2=q)).card:ℝ) by
        exact_mod_cast card_le_card hsub).trans hh
  have hCf := fineCapacity_pos
  have hsumNat : J.card=∑z∈Z,(J.filter (fun u => u.1 (3:Fin 4)=z)).card :=
    card_eq_sum_card_fiberwise (f := fun u => u.1 (3:Fin 4)) (t := Z)
      (fun u hu => mem_image_of_mem _ (mem_filter.mp hu).1)
  change (J.card:ℝ) ≤ 18*fineCapacity*Sref.thickness^(-pExp)*d^3/eps^4
  calc
    _ = ∑z∈Z,((J.filter (fun u => u.1 (3:Fin 4)=z)).card:ℝ) := by
      exact_mod_cast hsumNat
    _ ≤ ∑_z∈Z,fineCapacity*Sref.thickness^(-pExp)*(d/eps)^3 :=
      sum_le_sum (fun z _hz => hcap z)
    _ = (fineCapacity*Sref.thickness^(-pExp)*(d/eps)^3)*(Z.card:ℝ) := by simp [mul_comm]
    _ ≤ (fineCapacity*Sref.thickness^(-pExp)*(d/eps)^3)*(18/eps) :=
      mul_le_mul_of_nonneg_left hZcap (by positivity)
    _ = _ := by field_simp [heps.ne']

end NativeActualFineWeightShadingBridge
