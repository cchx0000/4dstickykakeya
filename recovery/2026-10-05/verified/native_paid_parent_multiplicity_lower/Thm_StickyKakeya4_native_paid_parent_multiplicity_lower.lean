import Theorems.Thm_StickyKakeya4_native_scheduled_pair_parent_transfer
import Theorems.Thm_StickyKakeya4_native_uniform_retention_transfer
import Theorems.Thm_StickyKakeya4_native_two_scale_configuration

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

noncomputable section
namespace NativePaidParentMultiplicityLower
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalCellChartGeometry
open NativeOriginalParentSelection NativeOriginalParentDensityCore NativeCubicalIncidenceCounts
open NativeJointUniformCoarseRelations NativeConditionedPairMenu NativeDyadicParentCells
open NativeCoarseScaleInterpolation NativeScheduledPairParentTransfer NativeUniformRetentionTransfer
open NativeTwoScaleConfiguration NativeFixedCompactKakeyaExponent

/-- Paid literal edge retention in an arbitrary parent yields a genuine
coarse multiplicity lower. Only one FINER installed first-stage pair relation
is used; no off-menu parent-specific pair uniformity is assumed. -/
theorem parent_full_source_retained_lower {n : ℕ} {D : FiniteScaleSource n} {eta a theta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (R : Finset (Fin n)) (E1 E2 : Finset (Fin n × Index))
    (hE1 : E1⊆incidences original) (hER : ∀z∈E1,z.1∈R) (hE21 : E2⊆E1)
    (level m f fine : ℕ) (hdy : D.thickness=(2:ℝ)⁻¹^level)
    (hmf : m ≤ f) (hff : f ≤ fine) (hfL : fine ≤ level) (Q : ℕ)
    (HU : HasUniformFibers E1 Q (conditionedGlobalPair h R a level fine fine))
    (p : Parent) (hp : (parentEdges D a (2^m) E1 p).Nonempty)
    (htheta : 0 < theta)
    (hret : theta*((parentEdges D a (2^m) E1 p).card:ℝ) ≤ (parentEdges D a (2^m) E2 p).card) :
    (theta/(729*(((2^(fine-f):ℕ):ℝ)^10)*(Q:ℝ)^2))*
        (NativeFiniteKakeyaCounts.multiplicity
          (NativeFullCoarseShadow.fullSource h R a level f (parentEdges D a (2^m) E1 p))).toReal ≤
      (NativeFiniteKakeyaCounts.multiplicity
        (NativeFullCoarseShadow.fullSource h R a level f (parentEdges D a (2^m) E2 p))).toReal := by
  let A := parentEdges D a (2^m) E1 p
  let B := parentEdges D a (2^m) E2 p
  have hBA : B⊆A := filter_subset_filter _ hE21
  have hAo : A⊆incidences original := (filter_subset _ _).trans hE1
  have hAR : ∀z∈A,z.1∈R := fun z hz => hER z (mem_filter.mp hz).1
  have hBR : ∀z∈B,z.1∈R := fun z hz => hAR z (hBA hz)
  have hU := diagonal_parent_uniformity h R a level m fine (hmf.trans hff) E1 Q HU p
  have hh := retained_image_multiplicity A B hBA hp
    (actualPair h R a level f) (actualPair h R a level fine) Q (27*(2^(fine-f))^10) 27 hU
    (fun v _hv => NativeCoarseScaleReverse.pair_fiber_image_card_le h original horiginal ha
      R A hAo hAR level f fine hdy hff hfL v)
    (fun v _hv => coarse_pair_over_fine_card_le h original horiginal ha
      R A hAo hAR level f fine hdy hff hfL v) theta htheta hret
  have hden : (((27*(2^(fine-f))^10:ℕ):ℝ)*(27:ℝ)*(Q:ℝ)^2)=
      729*(((2^(fine-f):ℕ):ℝ)^10)*(Q:ℝ)^2 := by push_cast; ring
  norm_num only [Nat.cast_ofNat] at hh
  rw [hden] at hh
  rw [NativeCoarsePointMultiplicity.full_source_multiplicity_real h R a level f _ hAR,
    NativeCoarsePointMultiplicity.full_source_multiplicity_real h R a level f _ hBR]
  exact hh

/-- Apply the actual E1 conditional power profile after paying E2's
literal parent retention. The same original R and representatives remain. -/
theorem parent_conditional_power_lower {n : ℕ} {D : FiniteScaleSource n} {eta a theta tau : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (R : Finset (Fin n)) (E1 E2 : Finset (Fin n × Index))
    (hE1 : E1⊆incidences original) (hER : ∀z∈E1,z.1∈R) (hE21 : E2⊆E1)
    (level m f fine : ℕ) (hdy : D.thickness=(2:ℝ)⁻¹^level)
    (hmf : m ≤ f) (hff : f ≤ fine) (hfL : fine ≤ level) (Q : ℕ)
    (HU : HasUniformFibers E1 Q (conditionedGlobalPair h R a level fine fine))
    (p : Parent) (hp : (parentEdges D a (2^m) E1 p).Nonempty)
    (htheta : 0 < theta)
    (hret : theta*((parentEdges D a (2^m) E1 p).card:ℝ) ≤ (parentEdges D a (2^m) E2 p).card)
    (Hreference : HasConditionalTwoScale h R E1 a level m f tau) :
    (theta/(729*(((2^(fine-f):ℕ):ℝ)^10)*(Q:ℝ)^2))*D.thickness^tau*
        ((64/((2^f:ℕ):ℝ))/(64/((2^m:ℕ):ℝ)))^(-extremalExponent) ≤
      (NativeFiniteKakeyaCounts.multiplicity
        (NativeFullCoarseShadow.fullSource h R a level f (parentEdges D a (2^m) E2 p))).toReal := by
  have hh := parent_full_source_retained_lower h original horiginal ha R E1 E2 hE1 hER hE21
    level m f fine hdy hmf hff hfL Q HU p hp htheta hret
  have hlo := (Hreference p hp).1
  calc
    _ = (theta/(729*(((2^(fine-f):ℕ):ℝ)^10)*(Q:ℝ)^2))*
        (D.thickness^tau*((64/((2^f:ℕ):ℝ))/(64/((2^m:ℕ):ℝ)))^(-extremalExponent)) := by ring
    _ ≤ (theta/(729*(((2^(fine-f):ℕ):ℝ)^10)*(Q:ℝ)^2))*
        (NativeFiniteKakeyaCounts.multiplicity
          (NativeFullCoarseShadow.fullSource h R a level f (parentEdges D a (2^m) E1 p))).toReal :=
      mul_le_mul_of_nonneg_left hlo (by positivity)
    _ ≤ _ := hh

end NativePaidParentMultiplicityLower
