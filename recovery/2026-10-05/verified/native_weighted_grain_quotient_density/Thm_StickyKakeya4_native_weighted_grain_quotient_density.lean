import Theorems.Thm_StickyKakeya4_native_weighted_grain_quotient_hereditary
import Theorems.Thm_StickyKakeya4_native_weighted_grain_quotient_source

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 12000000
noncomputable section
namespace NativeWeightedGrainQuotientDensity
open Classical Finset StickyKakeya4 NativeWeightedGrainQuotientGeometry NativeWeightedGrainQuotientFibers
open NativeWeightedGrainQuotientCap NativeWeightedGrainQuotientHereditary
open NativeGrainQuotientFibers NativeGrainHeightProjectionFibers NativeHorizontalGrainSlice
open NativeCommonCubicalMesh NativeOriginalParentSelection NativeSquaredGrainQueries
open NativeParentGrainIncidenceCleanup NativeSpatialAngularGeometry

/-- For EVERY retained coarse-height/quotient fiber, combine the original
mixed-edge threshold, incidence-weighted retention, actual parent vertex
cap, and raw-height preimage cap on the same retained occurrences. -/
theorem every_retained_fiber_density {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m ell : ℕ)
    (hm : m ≤ phaseDepth m) (plane : Index → Submodule ℝ E4)
    (E0 H : Finset (Fin n × Index)) (hHE0 : H⊆E0)
    (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hd : Module.finrank ℝ P=ell-1)
    (mu : ℝ) (hmu : 0 < mu) (hmesh : mu ≤ physicalMesh m (phaseDepth m)/8)
    (A C Cq L : ℝ) (hA : 0 < A) (hC : 0 ≤ C) (hCq : 0 ≤ Cq)
    (HC : ∀c : Parent × (Index × Index),∀T⊆E0,∀v : Index,
      (∀z∈T,parentLabel D a (2^m) z.1=c.1) →
      (∀z∈T,spatialLabel D (2^(phaseDepth m)) z.2=v) → A*(T.card:ℝ) ≤ C)
    (hthreshold : ∀x∈H,L < ((mixedFiber D a m plane ell H (mixedLabel D a m plane ell x)).card:ℝ))
    (hret : ∀c : Parent × (Index × Index),((mixedFiber D a m plane ell H c).card:ℝ) ≤
      Cq*(mixedFiber D a m plane ell (retained D a m ell plane H P hP hell hell4 hd mu) c).card) :
    let S := retained D a m ell plane H P hP hell hell4 hd mu
    ∀x∈S,A*L < Cq*C*(((2^(phaseDepth m-m):ℕ):ℝ))*
      (fullX D a m ell plane S P hP hell hell4 hd mu (key D a m ell plane P hP hell hell4 hd mu x)).card := by
  intro S x hx
  have hdense := (hthreshold x (retained_subset D a m ell plane H P hP hell hell4 hd mu hx)).trans_le (hret _)
  have hcross := selected_X_cross D a m ell hm plane E0 H hHE0 P hP hell hell4 hd mu hmu hmesh
    (mixedLabel D a m plane ell x) A C hC (HC _)
  have hl := local_threshold_to_X hA hCq hdense hcross
  have hsub := wholeX_subset_fullX D a m ell plane H P hP hell hell4 hd mu x hx
  exact hl.trans_le (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (card_le_card hsub))
    (mul_nonneg (mul_nonneg hCq hC) (Nat.cast_nonneg _)))

/-- After a later uniform H3 refinement, the worker-supplied old-grain
threshold applies to H3 itself. The same original cap and hereditary
geometric count then give density in EVERY actual H3 final fiber. -/
theorem every_H3_fiber_density {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m ell : ℕ)
    (hm : m ≤ phaseDepth m) (plane : Index → Submodule ℝ E4)
    (E0 H H3 : Finset (Fin n × Index)) (hHE0 : H⊆E0)
    (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hd : Module.finrank ℝ P=ell-1)
    (mu : ℝ) (hmu : 0 < mu) (hmesh : mu ≤ physicalMesh m (phaseDepth m)/8)
    (h3S : H3⊆retained D a m ell plane H P hP hell hell4 hd mu)
    (A C L : ℝ) (hA : 0 < A) (hC : 0 ≤ C)
    (HC : ∀c : Parent × (Index × Index),∀T⊆E0,∀v : Index,
      (∀z∈T,parentLabel D a (2^m) z.1=c.1) →
      (∀z∈T,spatialLabel D (2^(phaseDepth m)) z.2=v) → A*(T.card:ℝ) ≤ C)
    (hthreshold : ∀x∈H3,L < ((mixedFiber D a m plane ell H3 (mixedLabel D a m plane ell x)).card:ℝ)) :
    ∀x∈H3,A*L < C*(((2^(phaseDepth m-m):ℕ):ℝ))*
      (fullX D a m ell plane H3 P hP hell hell4 hd mu (key D a m ell plane P hP hell hell4 hd mu x)).card := by
  intro x hx
  have hcross := hereditary_X_cross D a m ell hm plane E0 H H3 hHE0 P hP hell hell4 hd mu hmu hmesh h3S
    (mixedLabel D a m plane ell x) A C hC (HC _)
  have hl := (mul_lt_mul_of_pos_left (hthreshold x hx) hA).trans_le hcross
  have hsub := hereditary_mixed_X_subset_fullX D a m ell plane H H3 P hP hell hell4 hd mu h3S x hx
  exact hl.trans_le (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (card_le_card hsub))
    (mul_nonneg hC (Nat.cast_nonneg _)))

/-- Cross form matching the SAME H3 uniform-refinement output exactly:
the old threshold t is bounded by B times each retained old-grain mass.
No division, additional cut, or factor2 is inserted. -/
theorem every_H3_fiber_density_cross {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m ell : ℕ)
    (hm : m ≤ phaseDepth m) (plane : Index → Submodule ℝ E4)
    (E0 H H3 : Finset (Fin n × Index)) (hHE0 : H⊆E0)
    (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hd : Module.finrank ℝ P=ell-1)
    (mu : ℝ) (hmu : 0 < mu) (hmesh : mu ≤ physicalMesh m (phaseDepth m)/8)
    (h3S : H3⊆retained D a m ell plane H P hP hell hell4 hd mu)
    (A C B t : ℝ) (hA : 0 ≤ A) (hC : 0 ≤ C) (hB : 0 ≤ B)
    (HC : ∀c : Parent × (Index × Index),∀T⊆E0,∀v : Index,
      (∀z∈T,parentLabel D a (2^m) z.1=c.1) →
      (∀z∈T,spatialLabel D (2^(phaseDepth m)) z.2=v) → A*(T.card:ℝ) ≤ C)
    (hthreshold : ∀x∈H3,t ≤ B*((mixedFiber D a m plane ell H3 (mixedLabel D a m plane ell x)).card:ℝ)) :
    ∀x∈H3,A*t ≤ B*C*(((2^(phaseDepth m-m):ℕ):ℝ))*
      (fullX D a m ell plane H3 P hP hell hell4 hd mu (key D a m ell plane P hP hell hell4 hd mu x)).card := by
  intro x hx
  have hcross := hereditary_X_cross D a m ell hm plane E0 H H3 hHE0 P hP hell hell4 hd mu hmu hmesh h3S
    (mixedLabel D a m plane ell x) A C hC (HC _)
  have hsub := hereditary_mixed_X_subset_fullX D a m ell plane H H3 P hP hell hell4 hd mu h3S x hx
  have hlocal : A*t ≤ B*C*(((2^(phaseDepth m-m):ℕ):ℝ))*
      ((mixedFiber D a m plane ell H3 (mixedLabel D a m plane ell x)).image (edgeX D a m ell P hd mu)).card := by
    have hl := mul_le_mul_of_nonneg_left (hthreshold x hx) hA
    have hu := mul_le_mul_of_nonneg_left hcross hB
    nlinarith only [hl,hu]
  exact hlocal.trans (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (card_le_card hsub))
    (mul_nonneg (mul_nonneg hB hC) (Nat.cast_nonneg _)))

end NativeWeightedGrainQuotientDensity
