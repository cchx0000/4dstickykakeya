/- UNVERIFIED same-T finest-only final-Y source reader. -/
import Theorems.Thm_StickyKakeya4_native_single_height_coarse_Y_ad
import Theorems.Thm_StickyKakeya4_native_third_XY_source_data

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
noncomputable section
namespace NativeThirdSingleHeightYAD
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeCubicalIncidenceCounts
open NativeSingleHeightCoarseYAD NativeGridCenterCoarsening NativeLiteralGridOverlap
open NativeReferenceXYGridSupport NativeReferenceXYGridPoints NativeReferenceXYGridMaps
open NativeReferenceXYGridField NativeHorizontalGrainSlice NativeGrainQuotientFibers
open NativeTranslatedGrainHeightOverlap NativeSquaredGrainQueries NativeThirdXYSourceData NativeThirdXYData
open NativeConfiguredThirdRelation CanonicalConfiguredE4Bridge NativeActualQuotientSupport
open NativeEncodedQuotientAD NativeFixedCompactKakeyaExponent NativeQuotientLatticeTransport
open FiniteVoronoiRealADCoarsening NativeRetainedSliceCore
open scoped Matrix.Norms.Elementwise

/-- Read the actual fine Y-AD from the sole third record, identify the
entire surviving coarse-height slice with its one old height, and transport
that same set to its literal final coarse-Y midpoint image. No AD lower is
inherited across a later arbitrary cut, and no larger time-window is asserted. -/
theorem from_third_data {n d J : ℕ} {D : FiniteScaleSource n} {eta a zeta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (m level : ℕ) (hm : 12 ≤ m) (hdy : D.thickness=(2:ℝ)⁻¹^level)
    (hf : phaseDepth m ≤ level) (p : Parent)
    (plane : Index → Submodule ℝ E4) (E Hgraph S T : Finset (Fin n × Index))
    (hS : S⊆incidences original) (hp : ∀z∈S,parentLabel D a (2^m) z.1=p)
    (P : Submodule ℝ E4) (hP : P≤heightKernel) (hd : Module.finrank ℝ P=1)
    (Fraw Fcfg : ℤ → Matrix (Fin 2) (Fin 1) ℝ)
    (population PL PU : ℝ) (Qref : ℕ) (lambda G Cpre threshold : ℝ) (L3 : ℕ)
    (Rel : Fin d → (Fin n × Index) → (Fin n × Index) → Prop) (CX : ℝ)
    (R : ℕ) (hR : 0 < R) (hbase : mu m*(R:ℝ) ≤ 1)
    (hdimension : extremalExponent ≤ 2)
    (Hdata : HasThirdXYSourceData (J:=J) (ell:=2) D zeta a m plane E Hgraph S T P hP
      (by norm_num) (by norm_num) hd Fraw p population PL PU Qref lambda G Cpre threshold L3 Rel CX) :
    let Sq := NativeWeightedGrainQuotientGeometry.retained D a m 2 plane Hgraph P hP
      (by norm_num) (by norm_num) hd (physicalMesh m (phaseDepth m)/8)
    let F := fixedField D a m 2 plane Sq Fraw
    let key := fun z : Fin n × Index => coarseYKey D a m p .oneTwo P hP hd F Fcfg R z.2
    let Q3 := NativeSourceSizeBounds.radix S.card L3
    let F3 := refinementCost (d+2) (J+1) L3
    let KXY := xyConstant D.thickness zeta population PL PU lambda (G*Cpre*(F3:ℝ)) Qref Q3 J m
    let KY := quotientConstant 1 2 (1/(32*CX)) KXY (3-extremalExponent)
    (∀z∈T,F (translatedHeight D a m z.2)=
      Fcfg (translatedHeight D a m z.2/((8*R:ℕ):ℤ))) →
    (∀z∈T,∀w∈T,translatedHeight D a m z.2/((8*R:ℕ):ℤ)=
      translatedHeight D a m w.2/((8*R:ℕ):ℤ) → translatedHeight D a m z.2=translatedHeight D a m w.2) →
    ∀height∈(T.image key).image Prod.fst,
      ADBounds ((T.filter (fun z => (key z).1=height)).image
        (fun z => NativeQuotientGridCenters.center (mu m*(R:ℝ)/512) (key z).2))
        (mu m*(R:ℝ)/512) (finalConstant KY (2-extremalExponent)) (2-extremalExponent) := by
  intro Sq F key Q3 F3 KXY KY hfreeze Hsingle height hheight
  have hTS : T⊆S := Hdata.1.1
  have Hcopy := Hdata.1
  rcases Hcopy with ⟨_hTS,_hTn,_hCost,_hTH,_hFinal,_hExtra,_hOld,_hXY,_hClass,
    _hGrain,_hKey,_hThreshold,_hRet,_Hxy,_hRead,hNorm⟩
  obtain ⟨q,hq,hqh⟩ := mem_image.mp hheight
  obtain ⟨z,hz,rfl⟩ := mem_image.mp hq
  let labels := fun x : Fin n × Index => pxy D a m 2 p P hP (by norm_num) (by norm_num) hd F x.2
  let Yfine := (productSlice (T.image labels) (labels z).1).image Prod.snd
  have hkey : ∀x∈T,key x=((labels x).1/((8*R:ℕ):ℤ),divide R (labels x).2.2) := by
    intro x hx
    have hh := coarseYKey_of_frozen D a m p .oneTwo P hP hd F Fcfg R x.2 (hfreeze x hx)
    simpa only [key,labels,pxy,divide,NativeActualConfiguredPoint.sourceLabel_oneTwo] using hh
  have hsingle : ∀x∈T,∀y∈T,(labels x).1/((8*R:ℕ):ℤ)=(labels y).1/((8*R:ℕ):ℤ) →
      (labels x).1=(labels y).1 := by
    intro x hx y hy he
    exact Hsingle x hx y hy he
  have hid := key_image_eq_one_height T labels key R hkey hsingle z hz
  have hFsupport := product_support h original horiginal ha m level 2 hm hdy hf p T
    (hTS.trans hS) (fun x hx => hp x (hTS hx)) P hP (by norm_num) (by norm_num) hd F hNorm (labels z).1
  have hsupport : ∀y∈Yfine,∀j : Fin 2,|mu m*(y j:ℝ)| ≤ 1 := by
    intro y hy j
    obtain ⟨xy,hxy,rfl⟩ := mem_image.mp hy
    have hb := hFsupport.2 xy hxy j
    have hcast : |(xy.2 j:ℝ)| ≤ 2*(halfWidth m:ℝ) := by exact_mod_cast hb
    rw [abs_mul,abs_of_pos (mu_pos m)]
    exact (mul_le_mul_of_nonneg_left hcast (mu_pos m).le).trans_eq (mu_fullWidth m (by omega))
  have hKY : 1 ≤ KY := quotientConstant_one_le _ _ _ _ _
  have Hfine : ADBounds (Yfine.image (center (mu m))) (mu m) KY (2-extremalExponent) := by
    have hh := Hdata.2.2.2.1 (labels z).1
    simpa only [Yfine,labels,KY,Nat.reduceSub,Nat.cast_ofNat,pow_one,
      show (4:ℝ)-2=2 by norm_num] using hh
  have hAD := coarse_contracted_AD Yfine (mu_pos m) hKY (by linarith only [hdimension])
    R hR hbase hsupport Hfine
  have heq : (T.filter (fun x => (key x).1=height)).image
      (fun x => NativeQuotientGridCenters.center (mu m*(R:ℝ)/512) (key x).2)=
      (Yfine.image (divide R)).image (center (mu m*(R:ℝ)/512)) := by
    rw [←hid]
    rw [image_image]
    rw [hqh]
    rfl
  rw [heq]
  exact hAD

end NativeThirdSingleHeightYAD
