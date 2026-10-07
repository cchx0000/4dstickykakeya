/- UNVERIFIED direct actual third-source instance of planar Lemma 5.3.
The sole remaining payment input is the explicit numerical fine-Y cost. -/
import Theorems.Thm_StickyKakeya4_native_third_single_height_Y_ad
import Theorems.Thm_StickyKakeya4_native_literal_Y_height_alignment

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 5000000
noncomputable section
namespace NativeThirdPlanarHeightAlignment
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeLiteralYHeightAlignment NativeThirdSingleHeightYAD NativeSingleHeightCoarseYAD
open NativeReferenceXYGridPoints NativeReferenceXYGridField NativeReferenceXYGridMaps
open NativeGrainQuotientFibers NativeHorizontalGrainSlice NativeTranslatedGrainHeightOverlap
open NativeSquaredGrainQueries NativeThirdXYSourceData NativeThirdXYData NativeEncodedQuotientAD
open NativeConfiguredThirdRelation CanonicalConfiguredE4Bridge NativeFixedCompactKakeyaExponent
open NativeRetainedSliceCore FiniteVoronoiRealADCoarsening NativeConfiguredYQuarterSquare
open scoped Matrix.Norms.Elementwise

/-- The planar eta0, chi and cutoff precede the original native datum.
Its SAME third T supplies every literal Y slice, source support, and the
entire one-height AD input. No planar-output or Y-retention premise occurs. -/
theorem exists_actual_height_alignment {zeta53 : ℝ} (hzeta53 : 0 < zeta53) :
    ∃eta0 chi : ℝ,0 < eta0 ∧ 0 < chi ∧
      ∀eta53 : ℝ,0 < eta53 → eta53 ≤ eta0 → ∃delta0 : ℝ,0 < delta0 ∧
      ∀(n d J : ℕ) (D : FiniteScaleSource n) (eta a zeta : ℝ)
        (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index),
      (∀i,D.shading i=wzCellShading (mesh D) original i) →
      (∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ)) →
      ∀(m level u : ℕ),12 ≤ m → D.thickness=(2:ℝ)⁻¹^level → phaseDepth m ≤ level →
      ∀(p : Parent) (plane : Index → Submodule ℝ E4)
        (E Hgraph S T : Finset (Fin n × Index)),
      S⊆incidences original → (∀z∈S,parentLabel D a (2^m) z.1=p) →
      ∀(P : Submodule ℝ E4) (hP : P≤heightKernel) (hd : Module.finrank ℝ P=1)
        (Fraw Fcfg : ℤ → Matrix (Fin 2) (Fin 1) ℝ)
        (population PL PU : ℝ) (Qref : ℕ) (lambda G Cpre threshold : ℝ) (L3 : ℕ)
        (Rel : Fin d → (Fin n × Index) → (Fin n × Index) → Prop) (CX : ℝ)
        (R : ℕ),0 < R → mu m*(R:ℝ)=(2:ℝ)⁻¹^u →
      extremalExponent ≤ 2 →
      HasThirdXYSourceData (J:=J) D zeta a m plane E Hgraph S T P hP
        (by norm_num) (by norm_num) hd Fraw p population PL PU Qref lambda G Cpre threshold L3 Rel CX →
      let Sq := NativeWeightedGrainQuotientGeometry.retained D a m 2 plane Hgraph P hP
        (by norm_num) (by norm_num) hd (physicalMesh m (phaseDepth m)/8)
      let F := fixedField D a m 2 plane Sq Fraw
      let key := fun z : Fin n × Index => coarseYKey D a m p .oneTwo P hP hd F Fcfg R z.2
      let Q3 := NativeSourceSizeBounds.radix S.card L3
      let F3 := refinementCost (d+2) (J+1) L3
      let KXY := xyConstant D.thickness zeta population PL PU lambda (G*Cpre*(F3:ℝ)) Qref Q3 J m
      let KY := quotientConstant 1 2 (1/(32*CX)) KXY (3-extremalExponent)
      (∀z∈T,F (translatedHeight D a m z.2)=Fcfg (translatedHeight D a m z.2/((8*R:ℕ):ℤ))) →
      (∀z∈T,∀w∈T,translatedHeight D a m z.2/((8*R:ℕ):ℤ)=
        translatedHeight D a m w.2/((8*R:ℕ):ℤ) → translatedHeight D a m z.2=translatedHeight D a m w.2) →
      (2:ℝ)⁻¹^u/512 ≤ delta0 →
      finalConstant KY (2-extremalExponent) ≤ (((2:ℝ)⁻¹^u/512)^(-eta53)) →
      Nonempty (∀height : {height : ℤ // height∈(T.image key).image Prod.fst},
        HeightAlignment (T.image key) u (2-extremalExponent) zeta53 chi height.val) := by
  obtain ⟨eta0,chi,heta0,hchi,H⟩ := NativeLiteralYHeightAlignment.exists_height_alignment hzeta53
  refine ⟨eta0,chi,heta0,hchi,?_⟩
  intro eta53 he53 he53top
  obtain ⟨delta0,hd0,Hplanar⟩ := H eta53 he53 he53top
  refine ⟨delta0,hd0,?_⟩
  intro n d J D eta a zeta h original horiginal ha m level u hm hdy hf p plane E Hgraph S T
    hS hp P hP hd Fraw Fcfg population PL PU Qref lambda G Cpre threshold L3 Rel CX R hR
    hbaseEq hk Hdata Sq F key Q3 F3 KXY KY hfreeze Hsingle hsmall hcost
  have hbase : mu m*(R:ℝ) ≤ 1 := by
    rw [hbaseEq]
    exact pow_le_one₀ (by norm_num) (by norm_num)
  have hmesh : mu m*(R:ℝ)/512=(2:ℝ)⁻¹^u/512 := congrArg (fun x : ℝ => x/512) hbaseEq
  have hAD := NativeThirdSingleHeightYAD.from_third_data h original horiginal ha m level hm hdy hf
    p plane E Hgraph S T hS hp P hP hd Fraw Fcfg population PL PU Qref lambda G Cpre threshold
    L3 Rel CX R hR hbase hk Hdata hfreeze Hsingle
  have hTS : T⊆S := Hdata.1.1
  have Hcopy := Hdata.1
  rcases Hcopy with ⟨_hTS,_hTn,_hCost,_hTH,_hFinal,_hExtra,_hOld,_hXY,_hClass,
    _hGrain,_hKey,_hThreshold,_hRet,_Hxy,_hRead,hNorm⟩
  have hbox := source_quarter_square h original horiginal ha m level hm hdy hf p T
    (hTS.trans hS) (fun z hz => hp z (hTS hz)) P hP hd F Fcfg hNorm R hR hbase hfreeze
  have ht : 0 ≤ 2-extremalExponent := by linarith only [hk]
  have ht2 : 2-extremalExponent ≤ 2 := by linarith only [extremalExponent_nonneg]
  apply Hplanar (T.image key) u (2-extremalExponent) hsmall ht ht2
  · intro height hh x hx y hy
    rw [heightPoints_image_keys] at hx hy
    obtain ⟨z,hz,rfl⟩ := mem_image.mp hx
    obtain ⟨w,hw,rfl⟩ := mem_image.mp hy
    apply (dist_pi_le_iff (by norm_num : (0:ℝ) ≤ 1)).mpr
    intro j
    have hxj := hbox z (mem_filter.mp hz).1 j
    have hyj := hbox w (mem_filter.mp hw).1 j
    rw [hmesh] at hxj hyj
    rw [Real.dist_eq]
    have hab := abs_sub
      (NativeQuotientGridCenters.center ((2:ℝ)⁻¹^u/512) (key z).2 j)
      (NativeQuotientGridCenters.center ((2:ℝ)⁻¹^u/512) (key w).2 j)
    linarith only [hab,hxj,hyj]
  · intro height hh
    rw [heightPoints_image_keys]
    have HH := hAD height hh
    rw [hmesh] at HH
    have hKY : 0 < KY := lt_of_lt_of_le (by norm_num) (quotientConstant_one_le _ _ _ _ _)
    have hC : 0 < finalConstant KY (2-extremalExponent) := by
      unfold finalConstant coarseConstant
      positivity
    intro x hx r hr hr1
    have HHr := HH x hx r hr hr1
    have hrpos : 0 < r := (show 0 < (2:ℝ)⁻¹^u/512 by positivity).trans_le hr
    have hpow : 0 ≤ (r/((2:ℝ)⁻¹^u/512))^(2-extremalExponent) :=
      Real.rpow_nonneg (by positivity) _
    exact ⟨(div_le_div_of_nonneg_left hpow hC hcost).trans HHr.1,
      HHr.2.trans (mul_le_mul_of_nonneg_right hcost hpow)⟩

end NativeThirdPlanarHeightAlignment
