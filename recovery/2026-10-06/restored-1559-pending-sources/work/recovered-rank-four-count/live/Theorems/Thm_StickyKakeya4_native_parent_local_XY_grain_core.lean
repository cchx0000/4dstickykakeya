import Theorems.Thm_StickyKakeya4_native_actual_XY_grain_core
import Theorems.Thm_StickyKakeya4_native_two_map_retained_slice_core
import Theorems.Thm_StickyKakeya4_native_two_map_retained_slice_actual_ad
import Theorems.Thm_StickyKakeya4_native_parent_slice_relation_readback

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
noncomputable section
namespace NativeParentLocalXYGrainCore
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalCellChartGeometry
open NativeOriginalParentSelection NativeOriginalParentDensityCore NativeCubicalIncidenceCounts
open NativeJointUniformCoarseRelations NativeFixedCompactKakeyaExponent NativeMiddleWindowBalance
open NativeAnisotropicShortRowGeometry NativeAnisotropicSliceLabels NativeSliceCountComparison
open NativeReferenceColumnExponents NativeReferenceSliceClassBounds NativeReferenceHorizontalMenu
open NativeReferenceSliceAllRadii NativeSliceClassBalls NativeSliceRadiusInterpolation
open NativeSquaredGrainQueries NativeSliceADConstant NativeRetainedSliceCore
open NativeRetainedGrainDensityCore NativeRetainedGrainDensityTransfer NativeTwoMapRetainedSliceCore
open NativeTwoMapRetainedSliceActualCaps NativeTwoMapRetainedSliceActualAD
open NativeReferenceXYGridPoints FiniteVoronoiRealADCoarsening SelfUniform
open scoped Matrix.Norms.Elementwise

open NativeActualXYGrainCore NativeParentSliceRelationReadback

theorem exists_parent_local_xy_grain_core {n d J : ℕ} {D : FiniteScaleSource n} {eta zeta a : ℝ}
    {Y V : Type*} [DecidableEq Y]
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
    (ell : ℕ) (P : Submodule ℝ E4) (hP : P≤NativeHorizontalGrainSlice.heightKernel)
    (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hd : Module.finrank ℝ P=ell-1)
    (field : ℤ → Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ) (hfield : ∀height,‖field height‖ ≤ (1/4:ℝ))
    (H S : Finset (Fin n × Index)) (hH : H⊆parentEdges D a (2^m) E p) (hSH : S⊆H) (hSn : S.Nonempty)
    (grain : (Fin n × Index) → Y) (quotient : (Fin n × Index) → V)
    (hquotient : ∀x y,x∈S → y∈S → grain x=grain y → quotient x=quotient y)
    (lambda G Cq t : ℝ) (hlambda : 0 < lambda) (hG : 0 < G) (hCq : 0 < Cq)
    (hret : lambda*((parentEdges D a (2^m) E p).card:ℝ) ≤ G*H.card)
    (hquotientRet : (H.card:ℝ) ≤ Cq*S.card)
    (hgrain : ∀g∈H.image grain,t ≤ ((H.filter (fun z => grain z=g)).card:ℝ))
    (Rel : Fin d → (Fin n × Index) → (Fin n × Index) → Prop)
    (hrefl : ∀j x,Rel j x x) (hsym : ∀j x y,Rel j x y → Rel j y x)
    (L3 : ℕ) (hL3 : 0 < L3) :
    let Q3 := NativeSourceSizeBounds.radix S.card L3
    let F3 := refinementCost (d+2) (J+1) L3
    let xy := fun z : Fin n × Index => encodedPoint D a m ell p P hP hell hell4 hd field z.2
    let low := lowerCountCoefficient D.thickness zeta population profileUpper
    let up := upperCountCoefficient D.thickness zeta profileLower
    let Ci : ℝ := ((201^3:ℕ):ℝ)
    let Cf : ℝ := ((1201^3:ℕ):ℝ)
    let gap : ℝ := max 64 ((2^((phaseDepth m-m)/J+1):ℕ):ℝ)
    let KXY := constant (lambda*(low/up)/((G*Cq*(F3:ℝ))*(Qref:ℝ)^2*Ci*Cf*(Q3:ℝ)^4))
      ((27*Cf)*(Cf*Ci*((Qref:ℝ)^4*up/low))) gap (3-extremalExponent)
    ∃T⊆S,T.Nonempty ∧ S.card ≤ F3*T.card ∧
      (∀j x y,x∈T → y∈T → degree (fun _ : Fin n × Index => 1) (Rel j) T x ≤
        Q3^2*degree (fun _ : Fin n × Index => 1) (Rel j) T y) ∧
      HasUniformFibers T Q3 Prod.snd ∧ HasUniformFibers T Q3 xy ∧
      (∀j,HasUniformFibers T Q3 (fun z => horizontalCoarsen (phaseDepth m)
        (NativeFixedHorizontalMenu.depths J m j) (xy z))) ∧
      HasUniformFibers T Q3 grain ∧
      (∀x y,x∈T → y∈T → grain x=grain y → quotient x=quotient y) ∧
      (∀g∈T.image grain,t ≤ Cq*(F3:ℝ)*(Q3:ℝ)^2*(T.filter (fun z => grain z=g)).card) ∧
      (lambda*((parentEdges D a (2^m) E p).card:ℝ) ≤ (G*Cq*(F3:ℝ))*T.card) ∧
      ∀height : ℤ,ADBounds (realizedSlice (T.image xy) (NativeReferenceXYGridPoints.mu m) height)
        (NativeReferenceXYGridPoints.mu m) KXY (3-extremalExponent) := by
  have hh := exists_actual_xy_grain_core h original R level Hbackbone m hm6 hbL hJ
    (parentEdges D a (2^m) E p) ((filter_subset _ _).trans hE) p population hpopulation
    (by simpa only [parentEdges_twice] using hpop)
    profileLower profileUpper hL hU
    (fun j => by simpa only [HasColumnPowerProfile,parentEdges_twice] using Hprofile j)
    Qref (parent_relations D a m (NativeFixedHorizontalMenu.depths J m)
      (fun j => (NativeFixedHorizontalMenu.depths_bounds J m hm6 j).2) E p Qref HPoint HColumn)
    ell P hP hell hell4 hd field hfield
    H S (by simpa only [parentEdges_twice] using hH) hSH hSn grain quotient hquotient
    lambda G Cq t hlambda hG hCq (by simpa only [parentEdges_twice] using hret)
    hquotientRet hgrain Rel hrefl hsym L3 hL3
  simpa only [parentEdges_twice] using hh

end NativeParentLocalXYGrainCore
