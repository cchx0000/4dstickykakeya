import Theorems.Thm_StickyKakeya4_native_joint_xy_support_count
import Theorems.Thm_StickyKakeya4_native_third_XY_data

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 6000000
noncomputable section
namespace NativeJointHeightSpatialPopulation
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeReferenceXYGridPoints NativeReferenceXYGridField NativeSquaredGrainQueries NativeHorizontalGrainSlice
open NativeThirdXYData NativeJointXYSupportCount NativeTranslatedGrainHeightOverlap NativeGrainQuotientFibers
open NativeRetainedSliceCore NativeFixedCompactKakeyaExponent NativeNormalizedCellRelativeMenu
open scoped Matrix.Norms.Elementwise

/-- The genuine configured joint-depth guards provide the required coarse
XY mesh and the512 fine-to-coarse ratio internally. -/
lemma joint_ratio (m u depth : ℕ) (hbase : u+6 ≤ m) (hdepth : depth ≤ u+3) :
    512 ≤ 2^(m+6-depth) ∧ ((2^(m+6-depth):ℕ):ℝ)*mu m=64/((2^depth:ℕ):ℝ) := by
  have hexp : 9 ≤ m+6-depth := by omega
  constructor
  · simpa only [show (2:ℕ)^9=512 by norm_num] using
      Nat.pow_le_pow_right (by norm_num : 0<(2:ℕ)) hexp
  · have hh : (2^(m+6-depth):ℕ)*2^depth=2^m*64 := by
      rw [←pow_add,Nat.sub_add_cancel (by omega),pow_add]
      norm_num
    have hr : ((2^(m+6-depth):ℕ):ℝ)*((2^depth:ℕ):ℝ)=((2^m:ℕ):ℝ)*64 := by exact_mod_cast hh
    have hmu : mu m=1/((2^m:ℕ):ℝ) := by unfold mu rho; ring
    rw [hmu]
    apply (eq_div_iff (by positivity : ((2^depth:ℕ):ℝ)≠0)).mpr
    field_simp
    nlinarith only [hr]

/-- The original third-core XY AD field, original source support and the
actual single-old-height property imply the spatial projection bound for
joint keys. The full third dimension and factor remain in KXY. No spatial
support-count, covering-number or recoded AD certificate is assumed. -/
theorem from_third_data {n d J : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (m level ell u : ℕ) (hu : 6 ≤ u) (hbase : u+6 ≤ m)
    (hdy : D.thickness=(2:ℝ)⁻¹^level) (hf : phaseDepth m ≤ level)
    (zeta : ℝ) (plane : Index → Submodule ℝ E4)
    (E Hgraph S T : Finset (Fin n × Index)) (hE : E⊆incidences original)
    (P : Submodule ℝ E4) (hP : P ≤ heightKernel) (hell : 1 ≤ ell) (hell4 : ell ≤ 4)
    (hd : Module.finrank ℝ P=ell-1)
    (Fraw : ℤ → Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ)
    (p : Parent) (population profileLower profileUpper : ℝ) (Qref : ℕ)
    (lambda G Cpre threshold : ℝ) (L3 : ℕ)
    (Rel : Fin d → (Fin n × Index) → (Fin n × Index) → Prop)
    (hS : S⊆parentEdges D a (2^m) E p)
    (Hdata : HasThirdXYData (J:=J) D zeta a m plane E Hgraph S T P hP hell hell4 hd Fraw p
      population profileLower profileUpper Qref lambda G Cpre threshold L3 Rel)
    (Hsingle : ∀x∈T,∀y∈T,
      translatedHeight D a m x.2/((8*2^(m-u):ℕ):ℤ)=
        translatedHeight D a m y.2/((8*2^(m-u):ℕ):ℤ) →
      translatedHeight D a m x.2=translatedHeight D a m y.2) :
    let Q3:=NativeSourceSizeBounds.radix S.card L3
    let F3:=refinementCost (d+2) (J+1) L3
    let KXY:=xyConstant D.thickness zeta population profileLower profileUpper lambda
      (G*Cpre*(F3:ℝ)) Qref Q3 J m
    ∀depth : ℕ,6 ≤ depth → depth ≤ u+3 →
      ∀height∈T.image (fun z => translatedHeight D a m z.2/((8*2^(m-u):ℕ):ℤ)),
      (((T.filter (fun z => translatedHeight D a m z.2/((8*2^(m-u):ℕ):ℤ)=height)).image
        (fun z => physicalCell D a (2^m) (2^depth) p z.2)).card:ℝ)  ≤ 
      (((17^4*9^3*13^3:ℕ):ℝ))*KXY^2*
        ((64/((2^depth:ℕ):ℝ))/512)^(-(3-extremalExponent)) := by
  intro Q3 F3 KXY depth hdepth hdu height hheight
  let Sq := NativeWeightedGrainQuotientGeometry.retained D a m ell plane Hgraph P hP hell hell4 hd
    (physicalMesh m (phaseDepth m)/8)
  let F := fixedField D a m ell plane Sq Fraw
  have Hcopy:=Hdata
  rcases Hcopy with ⟨hTS,_hTn,_hCost,_hTH,_hFinal,_HExtra,_hOld,_hXY,_hClass,_hGrain,_hKey,
    _hThreshold,_hRet,hAD,_hRead,hNorm⟩
  have hTI : T⊆incidences original := hTS.trans (hS.trans ((filter_subset _ _).trans hE))
  have hp : ∀x∈T,parentLabel D a (2^m) x.1=p := fun x hx => (mem_filter.mp (hS (hTS hx))).2
  obtain ⟨x,hx,hxheight⟩ := mem_image.mp hheight
  let I := T.filter (fun z => translatedHeight D a m z.2/((8*2^(m-u):ℕ):ℤ)=height)
  have hIT : I⊆T := filter_subset _ _
  have ht : ∀z∈I,translatedHeight D a m z.2=translatedHeight D a m x.2 := by
    intro z hz
    exact Hsingle z (mem_filter.mp hz).1 x hx ((mem_filter.mp hz).2.trans hxheight.symm)
  have hK : 0 < KXY := lt_of_lt_of_le zero_lt_one (xyConstant_one_le _ _ _ _ _ _ _ _ _ _ _)
  have hR := joint_ratio m u depth hbase hdu
  have hbound := source_height_physical_card h original horiginal ha m level ell (by omega) hdy hf p I T
    hIT hTI hp x.1 (hp x hx) P hP hell hell4 hd F hNorm (translatedHeight D a m x.2) ht
    (2^(m+6-depth)) depth hR.1 hdepth hR.2 hK (hAD (translatedHeight D a m x.2))
  have hscale : (64/((2^depth:ℕ):ℝ))/512 ≤ 64/((2^depth:ℕ):ℝ) := by
    have hpw : (0:ℝ) < 64/((2^depth:ℕ):ℝ) := by positivity
    linarith only [hpw]
  have ht0 : 0 ≤ 3-extremalExponent := sub_nonneg.mpr extremalExponent_le_three
  have hpow := Real.rpow_le_rpow_of_nonpos (by positivity) hscale (neg_nonpos.mpr ht0)
  exact hbound.trans (mul_le_mul_of_nonneg_left hpow (by positivity))

end NativeJointHeightSpatialPopulation
