import Theorems.Thm_StickyKakeya4_native_joint_xy_support_count
import Theorems.Thm_StickyKakeya4_native_grid_support_local
import Theorems.Thm_StickyKakeya4_native_rotated_cell_selection

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 6000000
noncomputable section
namespace NativeJointLocalXYGeometry
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeReferenceXYGridLinear NativeReferenceXYGridPoints NativeReferenceXYGridMaps NativeReferenceXYGridMetric
open NativeTwoMapRetainedSliceLabels NativeTwoMapRetainedSliceActualCaps NativeSliceClassBalls
open NativeNormalizedCellRelativeMenu NativeTranslatedGrainHeightOverlap NativeGrainQuotientInjection
open NativeJointXYSupportCount NativeLiteralGridCoverAD
open NativeCubicalIncidenceCounts NativeHorizontalGrainSlice
open scoped Matrix.Norms.Elementwise

lemma scalar_center_gap {base x y : ℝ} (hbase : 0 < base) :
    |base*((⌊x/base⌋:ℝ)+1/2)-base*((⌊y/base⌋:ℝ)+1/2)|  ≤  |x-y|+base := by
  have hx0 := center_label_close hbase (fun _ : Fin 1 => x)
  have hy0 := center_label_close hbase (fun _ : Fin 1 => y)
  have hx : |base*((⌊x/base⌋:ℝ)+1/2)-x| ≤ base/2 := by
    have hh := (dist_le_pi_dist _ _ (0:Fin 1)).trans hx0
    simpa only [NativeLiteralGridOverlap.center,label,Real.dist_eq] using hh
  have hy : |y-base*((⌊y/base⌋:ℝ)+1/2)| ≤ base/2 := by
    have hh := (dist_le_pi_dist _ _ (0:Fin 1)).trans hy0
    simpa only [NativeLiteralGridOverlap.center,label,Real.dist_eq,abs_sub_comm] using hh
  have h1 := abs_sub_le (base*((⌊x/base⌋:ℝ)+1/2)) x (base*((⌊y/base⌋:ℝ)+1/2))
  have h2 := abs_sub_le x y (base*((⌊y/base⌋:ℝ)+1/2))
  linarith only [hx,hy,h1,h2]

/-- On one actual old-height slice, a literal original physical cell has
a bounded footprint in the frozen base XY grid. The old/raw discrepancy
and both coordinate operator norms are derived from the original source. -/
theorem base_XY_footprint {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (m ell : ℕ) (hm : 6 ≤ m) (p : Parent)
    (i : Fin n) (hi : parentLabel D a (2^m) i=p)
    (P : Submodule ℝ E4) (hP : P ≤ heightKernel) (hell : 1 ≤ ell) (hell4 : ell ≤ 4)
    (hd : Module.finrank ℝ P=ell-1)
    (F : ℤ → Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ) (hF : ∀t,‖F t‖ ≤ (1/4:ℝ))
    (R0 depth : ℕ) (hR0 : 0 < R0)
    (hsmall : 512*mu m ≤ 64/((2^depth:ℕ):ℝ))
    (hbase : (R0:ℝ)*mu m ≤ 64/((2^depth:ℕ):ℝ))
    (k l : Index) (ht : translatedHeight D a m k=translatedHeight D a m l)
    (hcell : physicalCell D a (2^m) (2^depth) p k=physicalCell D a (2^m) (2^depth) p l) :
    dist (realized ((R0:ℝ)*mu m) (encode (dimension_sum ell hell hell4)
        (coarseXY ell R0 (pxy D a m ell p P hP hell hell4 hd F k))))
      (realized ((R0:ℝ)*mu m) (encode (dimension_sum ell hell hell4)
        (coarseXY ell R0 (pxy D a m ell p P hP hell hell4 hd F l))))  ≤ 
      6*(64/((2^depth:ℕ):ℝ)) := by
  let Delta : ℝ := 64/((2^depth:ℕ):ℝ)
  let base : ℝ := (R0:ℝ)*mu m
  have hDelta : 0 < Delta := by dsimp [Delta]; positivity
  have hbasep : 0 < base := mul_pos (by exact_mod_cast hR0) (mu_pos m)
  have hmu := mu_pos m
  have hold : dist (oldPoint D a m p k) (oldPoint D a m p l) ≤ 2*Delta := by
    apply NativeRotatedCellSelection.same_grid_dist_le hDelta
    exact hcell
  have hraw0 := raw_dist_le_old h m hm p i hi k l
  have hraw : dist (rawPoint D a m p k) (rawPoint D a m p l) ≤ 2*Delta+256*mu m := by
    linarith only [hraw0,hold]
  rw [dist_eq_norm] at hraw
  have hX (j : Fin (ell-1)) :
      |tangentCoordinates P ell hd (rawPoint D a m p k) j-
        tangentCoordinates P ell hd (rawPoint D a m p l) j| ≤ 4*Delta+512*mu m := by
    have hc := PiLp.norm_apply_le (tangentCoordinates P ell hd (rawPoint D a m p k-rawPoint D a m p l)) j
    have hn := tangent_norm_le P ell hd (rawPoint D a m p k-rawPoint D a m p l)
    simp only [map_sub,PiLp.sub_apply,Real.norm_eq_abs] at hc hn
    nlinarith only [hc,hn,hraw,hDelta,hmu]
  have hY (j : Fin (4-ell)) :
      |quotientMap P hP ell hell hell4 hd (F (translatedHeight D a m k)) (rawPoint D a m p k) j-
        quotientMap P hP ell hell hell4 hd (F (translatedHeight D a m l)) (rawPoint D a m p l) j| ≤ 
      4*Delta+512*mu m := by
    have hc := PiLp.norm_apply_le (quotientMap P hP ell hell hell4 hd (F (translatedHeight D a m k))
      (rawPoint D a m p k-rawPoint D a m p l)) j
    have hn := quotient_norm_le P hP ell hell hell4 hd (F (translatedHeight D a m k)) (hF _)
      (rawPoint D a m p k-rawPoint D a m p l)
    simp only [map_sub,PiLp.sub_apply,Real.norm_eq_abs] at hc hn
    rw [←ht]
    nlinarith only [hc,hn,hraw]
  let x := coarseXY ell R0 (pxy D a m ell p P hP hell hell4 hd F k)
  let y := coarseXY ell R0 (pxy D a m ell p P hP hell hell4 hd F l)
  have hxy (j : Fin ((ell-1)+(4-ell))) :
      |base*(((Fin.append x.2.1 x.2.2 j:ℤ):ℝ)+1/2)-
        base*(((Fin.append y.2.1 y.2.2 j:ℤ):ℝ)+1/2)| ≤ 6*Delta := by
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · simp only [Fin.append_left]
      dsimp only [x,y]
      rw [coarseXY_x,coarseXY_x]
      have hg := scalar_center_gap hbasep
        (x:=tangentCoordinates P ell hd (rawPoint D a m p k) j)
        (y:=tangentCoordinates P ell hd (rawPoint D a m p l) j)
      have hj := hX j
      change 512*mu m ≤ Delta at hsmall
      change base ≤ Delta at hbase
      nlinarith only [hg,hj,hsmall,hbase]
    · simp only [Fin.append_right]
      dsimp only [x,y]
      rw [coarseXY_y,coarseXY_y]
      have hg := scalar_center_gap hbasep
        (x:=quotientMap P hP ell hell hell4 hd (F (translatedHeight D a m k)) (rawPoint D a m p k) j)
        (y:=quotientMap P hP ell hell hell4 hd (F (translatedHeight D a m l)) (rawPoint D a m p l) j)
      have hj := hY j
      change 512*mu m ≤ Delta at hsmall
      change base ≤ Delta at hbase
      nlinarith only [hg,hj,hsmall,hbase]
  apply (dist_pi_le_iff (by positivity : (0:ℝ) ≤ 6*Delta)).mpr
  intro j
  simpa only [realized,encode,Fin.lastCases_castSucc,Real.dist_eq] using
    hxy (Fin.cast (dimension_sum ell hell hell4).symm j)

/-- Exact dyadic grid readback of the base XY centers. -/
lemma base_center_readback {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m ell : ℕ)
    (p : Parent) (P : Submodule ℝ E4) (hP : P ≤ heightKernel) (hell : 1 ≤ ell) (hell4 : ell ≤ 4)
    (hd : Module.finrank ℝ P=ell-1) (F : ℤ → Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ)
    (R0 : ℕ) (k : Index) :
    NativeLiteralGridOverlap.center ((R0:ℝ)*mu m)
      (label ((R0:ℝ)*mu m) (realized (mu m) (encodedPoint D a m ell p P hP hell hell4 hd F k)))=
    realized ((R0:ℝ)*mu m) (encode (dimension_sum ell hell hell4)
      (coarseXY ell R0 (pxy D a m ell p P hP hell hell4 hd F k))) := by
  rw [realized_coarse_label _ (mu_pos m)]
  funext j
  have he : encodedPoint D a m ell p P hP hell hell4 hd F k j.castSucc/(R0:ℤ)=
      encode (dimension_sum ell hell hell4)
        (coarseXY ell R0 (pxy D a m ell p P hP hell hell4 hd F k)) j.castSucc := by
    simp only [encodedPoint,encode,Fin.lastCases_castSucc,coarseXY]
    exact (append_div _ _ R0 _).symm
  simp only [NativeLiteralGridOverlap.center,realized,he]

/-- Local base-key population on the same original slice. The coarse mesh
is mu*R0, so no fine-point cardinality or R0-power tax is introduced. -/
theorem source_height_cell_base_keys {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (m level ell : ℕ) (hm : 12 ≤ m) (hdy : D.thickness=(2:ℝ)⁻¹^level)
    (hf : NativeSquaredGrainQueries.phaseDepth m ≤ level) (p : Parent)
    (S T : Finset (Fin n × Index)) (hST : S⊆T)
    (hT : T⊆incidences original) (hp : ∀z∈T,parentLabel D a (2^m) z.1=p)
    (P : Submodule ℝ E4) (hP : P ≤ heightKernel) (hell : 1 ≤ ell) (hell4 : ell ≤ 4)
    (hd : Module.finrank ℝ P=ell-1)
    (F : ℤ → Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ) (hF : ∀t,‖F t‖ ≤ (1/4:ℝ))
    (R0 depth : ℕ) (hR0 : 0<R0) (hdepth : 6 ≤ depth)
    (hsmall : 512*mu m ≤ 64/((2^depth:ℕ):ℝ))
    (hbase : (R0:ℝ)*mu m ≤ 64/((2^depth:ℕ):ℝ))
    (anchor : Fin n × Index) (hanchor : anchor∈S)
    (ht : ∀z∈S,translatedHeight D a m z.2=translatedHeight D a m anchor.2)
    (hcell : ∀z∈S,physicalCell D a (2^m) (2^depth) p z.2=
      physicalCell D a (2^m) (2^depth) p anchor.2)
    {K t : ℝ} (hK : 1 ≤ K) (ht0 : 0 ≤ t)
    (H : FiniteVoronoiRealADCoarsening.ADBounds
      (realizedSlice (T.image (fun z => encodedPoint D a m ell p P hP hell hell4 hd F z.2))
        (mu m) (translatedHeight D a m anchor.2)) (mu m) K t) :
    ((S.image (fun z => coarseXY ell R0 (pxy D a m ell p P hP hell hell4 hd F z.2))).card:ℝ) ≤
      ((9^3:ℕ):ℝ)*(((13^3:ℕ):ℝ))^2*K^2*(6:ℝ)^t*
        ((6*(64/((2^depth:ℕ):ℝ)))/((R0:ℝ)*mu m))^t := by
  let height := translatedHeight D a m anchor.2
  let base : ℝ := (R0:ℝ)*mu m
  let radius : ℝ := 6*(64/((2^depth:ℕ):ℝ))
  let xy := fun z : Fin n × Index => encodedPoint D a m ell p P hP hell hell4 hd F z.2
  let A := realizedSlice (T.image xy) (mu m) height
  let q := fun z : Fin n × Index => label base (realized (mu m) (xy z))
  let center := fun z : Fin n × Index => NativeLiteralGridOverlap.center base (q z)
  let U := T.filter (fun z => dist (center z) (center anchor) ≤ radius)
  have hSU : S⊆U := by
    intro z hz
    apply mem_filter.mpr
    refine ⟨hST hz,?_⟩
    dsimp only [center,q,xy]
    rw [base_center_readback,base_center_readback]
    exact base_XY_footprint h m ell (by omega) p anchor.1 (hp anchor (hST hanchor))
      P hP hell hell4 hd F hF R0 depth hR0 hsmall hbase z.2 anchor.2 (ht z hz) (hcell z hz)
  have hc := coarse_xy_image_card D a m ell p P hP hell hell4 hd F S U hSU height ht R0
  have hsub : ((realizedSlice (U.image xy) (mu m) height).image (label base)) ⊆
      (A.image (label base)).filter (fun k => dist (NativeLiteralGridOverlap.center base k) (center anchor) ≤ radius) := by
    intro k hk
    simp only [realizedSlice,NativeSliceCountComparison.heightSlice,mem_image,mem_filter] at hk
    obtain ⟨v,⟨w,⟨⟨z,hz,rfl⟩,hheight⟩,rfl⟩,rfl⟩ := hk
    obtain ⟨hzT,hzclose⟩ := mem_filter.mp hz
    apply mem_filter.mpr
    refine ⟨?_,hzclose⟩
    apply mem_image.mpr
    refine ⟨realized (mu m) (xy z),?_,rfl⟩
    apply mem_image.mpr
    exact ⟨xy z,mem_filter.mpr ⟨mem_image_of_mem xy hzT,hheight⟩,rfl⟩
  have hbasep : 0<base := mul_pos (by exact_mod_cast hR0) (mu_pos m)
  have hR1 : (1:ℝ) ≤ R0 := by exact_mod_cast hR0
  have hmubase : mu m ≤ base := le_mul_of_one_le_left (mu_pos m).le hR1
  have hwidth : (64/((2^depth:ℕ):ℝ)) ≤ 1 := by
    have hh : (64:ℝ) ≤ ((2^depth:ℕ):ℝ) := by
      exact_mod_cast Nat.pow_le_pow_right (by norm_num : 0<(2:ℕ)) hdepth
    exact (div_le_one (by positivity)).mpr hh
  have hbase1 : base ≤ 1 := hbase.trans hwidth
  have hbr : base ≤ radius := by
    have hh : (0:ℝ)<64/((2^depth:ℕ):ℝ) := by positivity
    dsimp only [radius]
    linarith only [hbase,hh]
  have hbox := source_realized_box h original horiginal ha m level ell hm hdy hf p T hT hp
    P hP hell hell4 hd F hF height
  have hb := NativeGridSupportLocal.occupied_ball_upper A (mu_pos m) hmubase hbase1 hK ht0 H hbox
    (center anchor) radius hbr
  exact (Nat.cast_le.mpr (hc.trans (card_le_card hsub))).trans hb

end NativeJointLocalXYGeometry
