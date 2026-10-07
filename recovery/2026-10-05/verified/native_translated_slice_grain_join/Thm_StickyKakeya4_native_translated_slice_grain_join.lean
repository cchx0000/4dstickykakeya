import Theorems.Thm_StickyKakeya4_native_parent_local_slice_grain_ad
import Theorems.Thm_StickyKakeya4_native_weighted_grain_quotient_source
import Theorems.Thm_StickyKakeya4_native_translated_grain_height_fibers
import Theorems.Thm_StickyKakeya4_native_translated_grain_height_chart

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 12000000
noncomputable section
namespace NativeTranslatedSliceGrainJoin
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeOriginalParentDensityCore NativeJointUniformCoarseRelations NativeSquaredGrainQueries
open NativeAnisotropicSliceLabels NativeAnisotropicShortRowGeometry NativeReferenceSliceClassBounds
open NativeReferenceColumnExponents NativeRetainedSliceCore NativeSliceADConstant
open NativeParentGrainIncidenceCleanup NativeSpatialAngularGeometry NativeHorizontalGrainSlice
open NativeDirectionRankDichotomy NativeCompatibleNodeDirections NativeProjectorCellChart
open NativeWeightedGrainQuotientSource NativeWeightedGrainQuotientGeometry
open NativeTranslatedGrainHeightSelection NativeTranslatedGrainHeightOverlap
open NativeTranslatedGrainHeightMetric NativeTranslatedGrainHeightFibers NativeTranslatedGrainHeightChart
open NativeGrainQuotientFibers NativeParentLocalSliceGrainAD NativeHeightMetricMenu
open NativeFixedCompactKakeyaExponent FiniteVoronoiRealADCoarsening SelfUniform
open NativeMiddleWindowBalance NativeGrainHeightProjectionSource NativeReferenceSliceAllRadii
open scoped Matrix.Norms.Elementwise

/-- One actual weighted quotient, two weighted height cuts, and ONE third
refinement. The same original incidences carry AD, grains, translated slope,
and every translated-height/quotient X lower. -/
theorem construct_translated_slice_grain {n d J ell : ℕ} {D : FiniteScaleSource n} {eta zeta a q r : ℝ}
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
    (HPoint : HasUniformFibers (parentEdges D a (2^m) E p) Qref (fun z => slicePoint D a m p z.2))
    (HColumn : ∀j,HasUniformFibers (parentEdges D a (2^m) E p) Qref
      (fun z => columnLabel D a (2^m) p (64/((2^(NativeFixedHorizontalMenu.depths J m j):ℕ):ℝ))
        (64/((2^m:ℕ):ℝ)) z.2))
    (S0 : Finset Index) (point : Index → Index) (tuple : Index → Fin ell → (Fin n × Index))
    (anchor : Index → Fin ell → Fin n)
    (Hsys : IsNodeDirectionSystem D a m E S0 q ell point tuple anchor)
    (A : Index → Submodule ℝ E4) (hA : ∀k∈S0,Module.finrank ℝ (A k)=ell)
    (hnear : ∀z∈E,Metric.infDist (slopeVector D z.1) (A z.2:Set E4) ≤ r)
    (hq : 0 < q) (hq1 : q ≤ 1) (hr : 0 < r) (hrD : r ≤ 64/((2^m:ℕ):ℝ))
    (H : Finset (Fin n × Index)) (hH : H⊆parentEdges D a (2^m) E p) (hHn : H.Nonempty)
    (hpoints : ∀z∈H,z.2∈S0)
    (P : Submodule ℝ E4) (hP : P≤heightKernel) (hell : 1 ≤ ell) (hell4 : ell ≤ 4)
    (hd : Module.finrank ℝ P=ell-1)
    (hchart : ∀z∈H,cell P=cell (sliceSpace (nodePlane D tuple (spatialLabel D (2^m) z.2))))
    (Fraw : ℤ → Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ) (metric : ℝ) (hmetric : 0 ≤ metric)
    (hFraw : ∀t,‖Fraw t‖ ≤ (1/4:ℝ))
    (Hmetric : ∀x∈H,∀y∈H,‖Fraw (rawHeight D m x.2)-Fraw (rawHeight D m y.2)‖ ≤
      metric*|chartHeightCoordinate m 0 (rawHeight D m x.2)-chartHeightCoordinate m 0 (rawHeight D m y.2)|)
    (lambda G t Acap Ccap : ℝ) (hlambda : 0 < lambda) (hG : 0 < G) (hAcap : 0 ≤ Acap) (hCcap : 0 ≤ Ccap)
    (hret : lambda*((parentEdges D a (2^m) E p).card:ℝ) ≤ G*H.card)
    (hgrain : ∀c∈H.image (mixedLabel D a m (nodePlane D tuple) ell),
      t ≤ ((mixedFiber D a m (nodePlane D tuple) ell H c).card:ℝ))
    (Hcap : ∀c : Parent × (Index × Index),∀U⊆E,∀v : Index,
      (∀z∈U,parentLabel D a (2^m) z.1=c.1) →
      (∀z∈U,spatialLabel D (2^(phaseDepth m)) z.2=v) → Acap*(U.card:ℝ) ≤ Ccap)
    (Rel : Fin d → (Fin n × Index) → (Fin n × Index) → Prop)
    (hrefl : ∀j x,Rel j x x) (hsym : ∀j x y,Rel j x y → Rel j y x)
    (L3 : ℕ) (hL3 : 0 < L3) :
    let plane := nodePlane D tuple
    let mu := physicalMesh m (phaseDepth m)/8
    let Sq := NativeWeightedGrainQuotientGeometry.retained D a m ell plane H P hP hell hell4 hd mu
    let S := second D a m ell plane Sq
    let Cq : ℝ := 4*⌈quotientCap q⌉₊
    let Q3 := NativeSourceSizeBounds.radix S.card L3
    let F3 := refinementCost (d+1) (J+1) L3
    let pt := fun z : Fin n × Index => slicePoint D a m p z.2
    let grain := mixedLabel D a m plane ell
    let key := referenceKey D a m ell plane P hP hell hell4 hd mu
    let Flow := mapped D a m ell plane Sq Fraw
    let low := lowerCountCoefficient D.thickness zeta population profileUpper
    let up := upperCountCoefficient D.thickness zeta profileLower
    let gap : ℝ := max 8 ((2^((phaseDepth m-m)/J+1):ℕ):ℝ)
    let KAD := constant (lambda*(low/up)/((G*Cq*(F3:ℝ))*(Qref:ℝ)^2*(Q3:ℝ)^4))
      ((Qref:ℝ)^4*up/low) gap (3-extremalExponent)
    ∃T⊆S,T.Nonempty ∧ T⊆H ∧ H.card ≤ (4*⌈quotientCap q⌉₊)*F3*T.card ∧
      (∀j x y,x∈T → y∈T → degree (fun _ : Fin n × Index => 1) (Rel j) T x ≤
        Q3^2*degree (fun _ : Fin n × Index => 1) (Rel j) T y) ∧
      HasUniformFibers T Q3 pt ∧
      (∀j,HasUniformFibers T Q3 (fun z => sliceClass m (NativeFixedHorizontalMenu.depths J m j) (pt z))) ∧
      HasUniformFibers T Q3 grain ∧
      (∀x y,x∈T → y∈T → grain x=grain y → key x=key y) ∧
      (∀x∈T,t ≤ Cq*(F3:ℝ)*(Q3:ℝ)^2*(mixedFiber D a m plane ell T (grain x)).card) ∧
      (∀height : ℤ,ADBounds (NativeSliceClassBalls.realizedSlice (T.image pt)
        (horizontalMesh m) height) (horizontalMesh m) KAD (3-extremalExponent)) ∧
      (∀x∈T,Flow (translatedHeight D a m x.2)=Fraw (rawHeight D m x.2)) ∧
      (∀height,‖Flow height‖ ≤ (1/4:ℝ)) ∧
      (∀s∈T.image (fun z => translatedHeight D a m z.2),∀u∈T.image (fun z => translatedHeight D a m z.2),
        ‖Flow s-Flow u‖ ≤ (3*metric)*|referenceHeight m s-referenceHeight m u|) ∧
      ∀x∈T,Acap*t ≤ (Cq*(F3:ℝ)*(Q3:ℝ)^2)*Ccap*(((2^(phaseDepth m-m):ℕ):ℝ))*
        (referenceX D a m ell plane T P hP hell hell4 hd mu (key x)).card := by
  intro plane mu Sq S Cq Q3 F3 pt grain key Flow low up gap KAD
  have hHE : H⊆E := hH.trans (filter_subset _ _)
  obtain ⟨hSqH,hqret,_hkeys,_hlocal⟩ := source_retention h hq hq1 hr hm6 hell hell4
    Hsys A hA hnear hrD H hHE hpoints P hP hd hchart
  have hSSq : S⊆Sq := second_subset D a m ell plane Sq
  have hSH : S⊆H := hSSq.trans hSqH
  have hfour : Sq.card ≤ 4*S.card := card_retention_four D a m ell plane Sq
  have hHS : H.card ≤ (4*⌈quotientCap q⌉₊)*S.card := by nlinarith only [hqret,hfour]
  have hSn : S.Nonempty := card_pos.mp (by
    have hh := card_pos.mpr hHn
    by_contra hn
    have hzero : S.card=0 := by omega
    rw [hzero,mul_zero] at hHS
    omega)
  have hCq : 0 < Cq := by
    have hceil : (0:ℝ)<(⌈quotientCap q⌉₊:ℝ) :=
      (quotientCap_pos hq).trans_le (Nat.le_ceil (quotientCap q))
    dsimp [Cq]
    positivity
  have hquotient : ∀x y,x∈S → y∈S → grain x=grain y → key x=key y := by
    intro x y hx hy hxy
    apply mixed_reference_key_eq D a m ell plane H S P hP hell hell4 hd mu (Subset.refl S) (grain x) x y
    · simp only [mixedFiber,RichDirectionalLayers.classFiber,mem_filter]
      exact ⟨hx,rfl⟩
    · simp only [mixedFiber,RichDirectionalLayers.classFiber,mem_filter]
      exact ⟨hy,hxy.symm⟩
  have hfiber (U : Finset (Fin n × Index)) (c : Parent × (Index × Index)) :
      mixedFiber D a m plane ell U c=U.filter (fun z => grain z=c) := by
    ext z
    simp only [mixedFiber,RichDirectionalLayers.classFiber,mem_filter,grain]
  obtain ⟨T,hTS,hTn,hcost,hExtra,hTP,hTC,hTG,hTquot,hTgrain,hAD⟩ :=
    exists_parent_local_slice_grain_AD h original R level Hbackbone m hm6 hbL hJ E hE p
      population hpopulation hpop profileLower profileUpper hL hU Hprofile Qref HPoint HColumn
      H S hH hSH hSn grain key hquotient lambda G Cq t hlambda hG hCq hret
      (by dsimp only [Cq]; exact_mod_cast hHS) (fun c hc => by simpa only [←hfiber] using hgrain c hc) Rel hrefl hsym L3 hL3
  have hTH : T⊆H := hTS.trans hSH
  have hfinal : H.card ≤ (4*⌈quotientCap q⌉₊)*F3*T.card := by nlinarith only [hHS,hcost]
  have hmin : ∀x∈T,t ≤ Cq*(F3:ℝ)*(Q3:ℝ)^2*(mixedFiber D a m plane ell T (grain x)).card := by
    intro x hx
    rw [hfiber]
    exact hTgrain (grain x) (mem_image_of_mem grain hx)
  refine ⟨T,hTS,hTn,hTH,hfinal,hExtra,hTP,hTC,hTG,hTquot,hmin,hAD,?_,?_,?_,?_⟩
  · intro x hx
    exact mapped_readback D a m ell plane Sq Fraw x (hTS hx)
  · intro height
    exact hFraw _
  · exact mapped_chart_metric D a m ell plane Sq T hTS Fraw metric 0 hmetric
      (fun x hx y hy => Hmetric x (hTH hx) y (hTH hy))
  · exact every_reference_fiber_density_cross D a m ell (by dsimp [phaseDepth]; omega)
      plane E H T hHE P hP hell hell4 hd mu (by exact div_pos (physicalMesh_pos _ _) (by norm_num))
      le_rfl hTS Acap Ccap (Cq*(F3:ℝ)*(Q3:ℝ)^2) t hAcap hCcap (by positivity) Hcap hmin

end NativeTranslatedSliceGrainJoin
