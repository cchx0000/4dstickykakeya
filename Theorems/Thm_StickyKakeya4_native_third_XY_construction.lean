import Theorems.Thm_StickyKakeya4_native_third_XY_data

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
noncomputable section
namespace NativeThirdXYConstruction
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeMiddleWindowBalance
open NativeOriginalParentDensityCore NativeJointUniformCoarseRelations NativeSquaredGrainQueries
open NativeAnisotropicSliceLabels NativeAnisotropicShortRowGeometry NativeReferenceSliceClassBounds
open NativeReferenceColumnExponents NativeRetainedSliceCore NativeSliceADConstant
open NativeParentGrainIncidenceCleanup NativeSpatialAngularGeometry NativeHorizontalGrainSlice
open NativeTranslatedGrainHeightSelection NativeTranslatedGrainHeightOverlap NativeTranslatedGrainHeightFibers
open NativeGrainQuotientFibers NativeReferenceXYGridField NativeReferenceXYGridPoints
open NativeTwoMapRetainedSliceActualCaps NativeSliceClassBalls NativeFixedCompactKakeyaExponent
open NativeThirdXYData NativeParentLocalXYGrainCore FiniteVoronoiRealADCoarsening SelfUniform
open scoped Matrix.Norms.Elementwise

/-- An arbitrary paid pre-third subset of the actual quotient/height core
is refined exactly once. The total field is fixed from the original graph
source before this refinement, including outside the surviving heights. -/
theorem construct_third_XY_data {n d J : ℕ} {D : FiniteScaleSource n} {eta zeta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (R : Finset (Fin n)) (level : ℕ) (Hbackbone : HasOriginalBackbone D original R a level zeta)
    (m : ℕ) (hm6 : 6 ≤ m) (hbL : phaseDepth m ≤ level) (hJ : 0 < J)
    (E : Finset (Fin n × Index)) (hE : E⊆retained original R) (p : Parent)
    (population : ℝ) (hpopulation : 0 < population)
    (hpop : population*(R.filter (fun i => parentLabel D a (2^m) i=p)).card ≤
      D.thickness*(parentEdges D a (2^m) E p).card)
    (profileLower profileUpper : ℝ) (hL : 0 < profileLower) (hU : 0 < profileUpper)
    (Hprofile : ∀j,HasColumnPowerProfile D a m (NativeFixedHorizontalMenu.depths J m j) E p
      profileLower profileUpper)
    (Qref : ℕ)
    (HPoint : HasUniformFibers (parentEdges D a (2^m) E p) Qref
      (fun z => slicePoint D a m p z.2))
    (HColumn : ∀j,HasUniformFibers (parentEdges D a (2^m) E p) Qref
      (fun z => columnLabel D a (2^m) p
        (64/((2^(NativeFixedHorizontalMenu.depths J m j):ℕ):ℝ)) (64/((2^m:ℕ):ℝ)) z.2))
    (ell : ℕ) (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hd : Module.finrank ℝ P=ell-1)
    (plane : Index → Submodule ℝ E4) (Hgraph S : Finset (Fin n × Index))
    (hH : Hgraph⊆parentEdges D a (2^m) E p) (hHn : Hgraph.Nonempty)
    (hS : S⊆second D a m ell plane
      (NativeWeightedGrainQuotientGeometry.retained D a m ell plane Hgraph P hP hell hell4 hd
        (physicalMesh m (phaseDepth m)/8)))
    (Fraw : ℤ → Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ) (hFraw : ∀height,‖Fraw height‖ ≤ (1/4:ℝ))
    (lambda G Cpre t : ℝ) (hlambda : 0 < lambda) (hG : 0 < G) (hCpre : 0 < Cpre)
    (hret : lambda*((parentEdges D a (2^m) E p).card:ℝ) ≤ G*Hgraph.card)
    (hpre : (Hgraph.card:ℝ) ≤ Cpre*S.card)
    (hgrain : ∀c∈Hgraph.image (mixedLabel D a m plane ell),
      t ≤ ((mixedFiber D a m plane ell Hgraph c).card:ℝ))
    (Rel : Fin d → (Fin n × Index) → (Fin n × Index) → Prop)
    (hrefl : ∀j x,Rel j x x) (hsym : ∀j x y,Rel j x y → Rel j y x)
    (L3 : ℕ) (hL3 : 0 < L3) :
    ∃T,HasThirdXYData (J:=J) D zeta a m plane E Hgraph S T P hP hell hell4 hd Fraw p
      population profileLower profileUpper Qref lambda G Cpre t L3 Rel := by
  let mu := physicalMesh m (phaseDepth m)/8
  let Sq := NativeWeightedGrainQuotientGeometry.retained D a m ell plane Hgraph P hP hell hell4 hd mu
  let field := fixedField D a m ell plane Sq Fraw
  let grain := mixedLabel D a m plane ell
  let key := referenceKey D a m ell plane P hP hell hell4 hd mu
  let Q3 := NativeSourceSizeBounds.radix S.card L3
  let F3 := refinementCost (d+2) (J+1) L3
  have hSH : S⊆Hgraph := hS.trans ((second_subset D a m ell plane Sq).trans
    (NativeWeightedGrainQuotientGeometry.retained_subset D a m ell plane Hgraph P hP hell hell4 hd mu))
  have hSn : S.Nonempty := by
    apply card_pos.mp
    by_contra hn
    have hz : S.card=0 := by omega
    have hpos : (0:ℝ)<Hgraph.card := by exact_mod_cast card_pos.mpr hHn
    rw [hz,Nat.cast_zero,mul_zero] at hpre
    linarith only [hpos,hpre]
  have hkey : ∀x y,x∈S → y∈S → grain x=grain y → key x=key y := by
    intro x y hx hy hxy
    apply mixed_reference_key_eq D a m ell plane Hgraph S P hP hell hell4 hd mu hS (grain x) x y
    · simp only [mixedFiber,RichDirectionalLayers.classFiber,mem_filter]
      exact ⟨hx,rfl⟩
    · simp only [mixedFiber,RichDirectionalLayers.classFiber,mem_filter]
      exact ⟨hy,hxy.symm⟩
  have hfiber (U : Finset (Fin n × Index)) (c : Parent × (Index × Index)) :
      mixedFiber D a m plane ell U c=U.filter (fun z => grain z=c) := by
    ext z
    simp only [mixedFiber,RichDirectionalLayers.classFiber,mem_filter,grain]
  obtain ⟨T,hTS,hTn,hcost,hExtra,hOld,hXY,hClass,hGrain,hKey,hMin,hRet,hAD⟩ :=
    exists_parent_local_xy_grain_core h original R level Hbackbone m hm6 hbL hJ E hE p
      population hpopulation hpop profileLower profileUpper hL hU Hprofile Qref HPoint HColumn
      ell P hP hell hell4 hd field (fixedField_norm D a m ell plane Sq Fraw hFraw)
      Hgraph S hH hSH hSn grain key hkey lambda G Cpre t hlambda hG hCpre hret hpre
      (fun c hc => by simpa only [←hfiber] using hgrain c hc) Rel hrefl hsym L3 hL3
  have hTH : T⊆Hgraph := hTS.trans hSH
  have hfinal : (Hgraph.card:ℝ) ≤ Cpre*(F3:ℝ)*T.card := by
    have hc : (S.card:ℝ) ≤ (F3:ℝ)*T.card := by exact_mod_cast hcost
    have hh := hpre.trans (mul_le_mul_of_nonneg_left hc hCpre.le)
    simpa only [mul_assoc] using hh
  refine ⟨T,?_⟩
  dsimp only [HasThirdXYData]
  refine ⟨hTS,hTn,hcost,hTH,hfinal,hExtra,hOld,hXY,hClass,hGrain,hKey,?_,hRet,hAD,?_,?_⟩
  · intro x hx
    rw [hfiber]
    exact hMin (grain x) (mem_image_of_mem grain hx)
  · intro x hx
    exact fixedField_readback D a m ell plane Sq Fraw x (hS (hTS hx))
  · exact fixedField_norm D a m ell plane Sq Fraw hFraw

end NativeThirdXYConstruction
