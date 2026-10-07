import Theorems.Thm_StickyKakeya4_native_weighted_grain_quotient_geometry
import Theorems.Thm_StickyKakeya4_native_source_parent_grain_cleanup

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 12000000
noncomputable section
namespace NativeWeightedGrainQuotientCap
open Classical Finset StickyKakeya4 NativeWeightedGrainQuotientGeometry
open NativeGrainQuotientFibers NativeGrainHeightProjectionFibers NativeHorizontalGrainSlice
open NativeCommonCubicalMesh NativeOriginalParentSelection NativeSquaredGrainQueries
open NativeParentGrainIncidenceCleanup NativeParentVertexMassCap NativeSourceParentGrainCleanup
open NativeSpatialAngularGeometry NativeQueriedVertexWeights NativeOriginalParentDensityCore
open NativeJointUniformCoarseRelations NativeFullCoarseShadow NativeMiddleWindowBalance
open NativeRetainedFinePairDensity NativeConditionedPairMenu NativeAllTwoScaleConfiguration
open NativeTwoScaleConfiguration NativeFixedCompactKakeyaExponent

/-- The already computed parent/raw-vertex cross cap applies to the literal
weighted selection, then the exact raw-height preimage count converts it
into an upper on original incidence mass per actual X fiber. -/
theorem selected_X_cross {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m ell : ℕ)
    (hm : m ≤ phaseDepth m) (plane : Index → Submodule ℝ E4)
    (E0 H : Finset (Fin n × Index)) (hHE0 : H⊆E0)
    (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hd : Module.finrank ℝ P=ell-1)
    (mu : ℝ) (hmu : 0 < mu) (hmesh : mu ≤ physicalMesh m (phaseDepth m)/8)
    (c : Parent × (Index × Index)) (A C : ℝ) (hC : 0 ≤ C)
    (HC : ∀T⊆E0,∀v : Index,(∀z∈T,parentLabel D a (2^m) z.1=c.1) →
      (∀z∈T,spatialLabel D (2^(phaseDepth m)) z.2=v) → A*(T.card:ℝ) ≤ C) :
    A*(mixedFiber D a m plane ell (retained D a m ell plane H P hP hell hell4 hd mu) c).card ≤
      C*(((2^(phaseDepth m-m):ℕ):ℝ))*
        (wholeX D a m ell plane H c P hP hell hell4 hd mu (pick D a m ell plane H P hP hell hell4 hd mu c)).card := by
  have hSE0 := (retained_subset D a m ell plane H P hP hell hell4 hd mu).trans hHE0
  have hcross := mixed_vertex_cross D a m (phaseDepth m) plane ell E0
    (retained D a m ell plane H P hP hell hell4 hd mu) hSE0 c A C HC
  have hvertices := retained_vertices_le_X D a m ell hm plane H P hP hell hell4 hd mu hmu hmesh c
  calc
    _ ≤ C*(mixedVertices D a m (phaseDepth m) plane ell (retained D a m ell plane H P hP hell hell4 hd mu) c).card := hcross
    _ ≤ C*((((2^(phaseDepth m-m):ℕ):ℝ))*
        (wholeX D a m ell plane H c P hP hell hell4 hd mu (pick D a m ell plane H P hP hell hell4 hd mu c)).card) :=
      mul_le_mul_of_nonneg_left hvertices hC
    _ = _ := by ring

/-- Direct original-source caller. The raw vertex cap is proved here from
the original pair/core data, never supplied as a new certificate. -/
theorem source_selected_X_cross {n d g level : ℕ} {D : FiniteScaleSource n}
    {eta zeta a seed tau : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta)
    (original : Fin n → Finset Index) (R : Finset (Fin n))
    (E1 E2 : Finset (Fin n × Index)) (h21 : E2⊆E1) (hE2 : E2.Nonempty) (L : ℕ)
    (schedule : Fin (g+1) → Fin (level+1))
    (Rel : Fin d → (Fin n × Index) → (Fin n × Index) → Prop)
    (htau : 0 < tau) (heta : 0 ≤ eta) (hseed : seed ≤ tau/16384)
    (hg : 0 < g) (hgl : g ≤ level)
    (hgrid : 1/(g:ℝ) < min (boundaryWindow tau) ((tau/16)/1000)/4)
    (Hbackbone : HasOriginalBackbone D original R a level zeta)
    (hschedule : schedule=fullSchedule tau htau g level)
    (Hcore : IsCore D original R a eta zeta d (g+1) L Rel
      (fun j => 2^(schedule j).val) E1)
    (hcost : (125*175616*16384:ℝ)*(factor d (g+1) L:ℝ)*(coreRadix original R L:ℝ)^2*
      D.thickness^(-eta) ≤ D.thickness^(-(seed/8)))
    (hconditioned : ∀i j,HasUniformFibers E1 (coreRadix original R L)
        (conditionedGlobalPair h R a level (schedule i).val (schedule j).val) ∧
      HasUniformFibers E1 (coreRadix original R L)
        (conditionedGlobalPoint h R a level (schedule i).val (schedule j).val))
    (hreference : ∀m f : ℕ,m ≤ f → f ≤ level → HasConditionalTwoScale h R E1 a level m f tau)
    (G : ℕ) (hG : 0 < G) (lambda : ℝ) (hlambda : 0 ≤ lambda)
    (hret : lambda*(E1.card:ℝ) ≤ (G:ℝ)*E2.card)
    (m ell Q2 : ℕ) (hm6 : 6 ≤ m) (hf : phaseDepth m ≤ level) (hsmall : D.thickness ≤ 1/8)
    (HP : HasUniformFibers E2 Q2 (physicalPair h R a level (phaseDepth m)))
    (HV : HasUniformFibers E2 Q2 (fun z => spatialLabel D (2^(phaseDepth m)) z.2))
    (plane : Index → Submodule ℝ E4) (H : Finset (Fin n × Index)) (hHE2 : H⊆E2)
    (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hd : Module.finrank ℝ P=ell-1)
    (mu : ℝ) (hmu : 0 < mu) (hmesh : mu ≤ physicalMesh m (phaseDepth m)/8)
    (c : Parent × (Index × Index)) :
    (lambda*D.thickness^(2*eta+2*zeta+4*tau)*(1/((2^m:ℕ):ℝ))^(-extremalExponent))*
      (mixedFiber D a m plane ell (retained D a m ell plane H P hP hell hell4 hd mu) c).card ≤
      (parentCapConstant*(factor d (g+1) L:ℝ)*G*(vertexCap E2 (spatialLabel D (2^(phaseDepth m))) Q2:ℝ))*
        (((2^(phaseDepth m-m):ℕ):ℝ))*
          (wholeX D a m ell plane H c P hP hell hell4 hd mu (pick D a m ell plane H P hP hell hell4 hd mu c)).card := by
  have hm : m ≤ phaseDepth m := by dsimp [phaseDepth]; omega
  have hf6 : 6 ≤ phaseDepth m := hm6.trans hm
  apply selected_X_cross D a m ell hm plane E2 H hHE2 P hP hell hell4 hd mu hmu hmesh c
  · have hp := parentCapConstant_pos
    positivity
  · intro T hTE v hparent hspace
    exact source_parent_vertex_cap h original R E1 E2 h21 hE2 L schedule Rel htau heta hseed hg hgl hgrid
      Hbackbone hschedule Hcore hcost hconditioned hreference G hG lambda hlambda hret
      m (phaseDepth m) Q2 hm hf6 hf hsmall HP HV T hTE c.1 v hparent hspace

/-- Re-run the original global cap cancellation after incidence-weighted
quotient selection. Both added losses stay explicit and the same M cancels. -/
theorem weighted_density_cap_cancellation {W M L N B T U A F X Cq Ht : ℝ}
    (hM : 0 < M) (hL : 0 < L) (hN : 0 < N) (hA : 0 < A)
    (hB : 0 ≤ B) (hT : 0 ≤ T) (hF : 0 ≤ F) (hCq : 0 ≤ Cq)
    (G : ℝ) (hcount : N ≤ B*G) (hgrain : M*L*G ≤ T)
    (hdense : W/(2*N) < Cq*F) (hcap : A*F ≤ U*M*Ht*X) :
    A*W*L < 2*B*T*U*Cq*Ht*X := by
  have hcap' : A*(Cq*F) ≤ (U*Cq*Ht)*M*X := by
    have hh := mul_le_mul_of_nonneg_left hcap hCq
    nlinarith only [hh]
  have hh := density_cap_cancellation hM hL hN hA hB hT (mul_nonneg hCq hF)
    G hcount hgrain hdense hcap'
  nlinarith only [hh]

/-- A local original mixed-incidence threshold gives X density in EVERY
retained mixed grain, not merely one maximum raw-vertex grain. -/
lemma local_threshold_to_X {A L Cq F U Ht X : ℝ} (hA : 0 < A) (hCq : 0 ≤ Cq)
    (hdense : L < Cq*F) (hcap : A*F ≤ U*Ht*X) : A*L < Cq*U*Ht*X := by
  have hl := mul_lt_mul_of_pos_left hdense hA
  have hu := mul_le_mul_of_nonneg_left hcap hCq
  nlinarith only [hl,hu]

end NativeWeightedGrainQuotientCap
