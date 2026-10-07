import Theorems.Thm_StickyKakeya4_native_relative_parent_profiles
import Theorems.Thm_StickyKakeya4_native_coarse_scale_reverse

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 5000000

noncomputable section
namespace NativeConfiguredPhaseFibers
open Classical Finset StickyKakeya4 NativeOriginalParentSelection NativeCommonCubicalMesh
open NativeRelativeParentLabels NativeRelativeParentProfiles NativeLocalParentSource
open NativeDyadicParentCells NativeCoarseScaleReverse NativeCoarseDirectionThinning

/-- The actual second-source phase determines a finite set of original
phase labels, with the six-dimensional scale loss retained explicitly. -/
theorem relative_phase_fiber_card {n : ℕ} (D : FiniteScaleSource n)
    (A : Finset (Fin n)) (a : ℝ) (m ell f : ℕ) (p q : Parent) :
    ((A.filter (fun i => relativeLabel D a (2^m) p (2^ell) i = q)).image
      (parentLabel D a (2^f))).card ≤ 512^3 * (2^(f-(m+ell)))^6 := by
  let B := A.filter (fun i => relativeLabel D a (2^m) p (2^ell) i = q)
  have hprod : (2:ℕ)^ell * 2^m = 2^(m+ell) := by rw [pow_add, Nat.mul_comm]
  have hbox (i : Fin n) (hi : i ∈ B) :
      parentLabel D a (2^(m+ell)) i ∈ projectionBox p (2^ell) q := by
    apply projection_mem_box
    rw [← hprod, ← relativeLabel_eq_projection]
    exact (mem_filter.mp hi).2
  by_cases hle : m+ell ≤ f
  · have hsub : B.image (parentLabel D a (2^f)) ⊆
        (projectionBox p (2^ell) q).biUnion (parentMenu (2^(f-(m+ell)))) := by
      intro z hz
      obtain ⟨i, hi, rfl⟩ := mem_image.mp hz
      apply mem_biUnion.mpr
      exact ⟨_, hbox i hi, parent_mem_menu (m+ell) f _ _ (parent_ancestor_eq D a hle i)⟩
    calc
      _ ≤ ((projectionBox p (2^ell) q).biUnion (parentMenu (2^(f-(m+ell))))).card := card_le_card hsub
      _ ≤ (projectionBox p (2^ell) q).card * (2^(f-(m+ell)))^6 :=
        card_biUnion_le_card_mul _ _ _ (fun z _ => (parentMenu_card _ (by positivity) z).le)
      _ = _ := by rw [projectionBox_card]
  · have hfl : f ≤ m+ell := by omega
    have he : B.image (parentLabel D a (2^f)) =
        (B.image (parentLabel D a (2^(m+ell)))).image (ancestor (m+ell) f) := by
      rw [image_image]
      congr 1
      funext i
      exact (parent_ancestor_eq D a hfl i).symm
    have hc : (B.image (parentLabel D a (2^(m+ell)))).card ≤ 512^3 := by
      exact (card_le_card (fun z hz => by
        obtain ⟨i, hi, rfl⟩ := mem_image.mp hz
        exact hbox i hi)).trans_eq (projectionBox_card p (2^ell) q)
    change (B.image _).card ≤ _
    rw [he, Nat.sub_eq_zero_of_le hfl]
    simpa only [pow_zero, one_pow, mul_one] using card_image_le.trans hc

/-- The source label is read back through its actual original-label
enumeration. No fresh source or new original tube subset is selected. -/
theorem local_source_phase_fiber_card {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (E : Finset (Fin n × Index)) (a : ℝ) (m ell f : ℕ) (p q : Parent)
    (A : Finset (Fin (parentLabels D R a (2^m) p).card)) :
    ((A.filter (fun i => parentLabel (source h R E a m p) 0 (2^ell) i = q)).image
      (fun i => parentLabel D a (2^f)
        (NativePaddedCellSource.originalLabel (parentLabels D R a (2^m) p) i))).card ≤
      512^3 * (2^(f-(m+ell)))^6 := by
  let old := NativePaddedCellSource.originalLabel (parentLabels D R a (2^m) p)
  have hsub : (A.filter (fun i => parentLabel (source h R E a m p) 0 (2^ell) i = q)).image
      (fun i => parentLabel D a (2^f) (old i)) ⊆
      (((A.image old).filter (fun i => relativeLabel D a (2^m) p (2^ell) i = q)).image
        (parentLabel D a (2^f))) := by
    intro z hz
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hz
    refine mem_image.mpr ⟨old i, mem_filter.mpr ⟨mem_image_of_mem _ (mem_filter.mp hi).1, ?_⟩, rfl⟩
    exact (source_parentLabel h R E a m p (2^ell) i).symm.trans (mem_filter.mp hi).2
  exact (card_le_card hsub).trans (relative_phase_fiber_card D (A.image old) a m ell f p q)

/-- Passing from an occupied second-source phase to its actual global
representative does not add another phase ambiguity. -/
theorem local_source_representative_fiber_card {n : ℕ} {D : FiniteScaleSource n} {eta etaS : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (E : Finset (Fin n × Index)) (a : ℝ) (m ell f : ℕ) (p : Parent)
    (hS : IsWangZakharovNativeFiniteInput (source h R E a m p) etaS)
    (A : Finset (Fin (parentLabels D R a (2^m) p).card))
    (j : Fin (parentLabels D R a (2^m) p).card) :
    ((A.filter (fun i => representative hS univ 0 (2^ell)
      (parentLabel (source h R E a m p) 0 (2^ell) i) = j)).image
      (fun i => parentLabel D a (2^f)
        (NativePaddedCellSource.originalLabel (parentLabels D R a (2^m) p) i))).card ≤
      512^3 * (2^(f-(m+ell)))^6 := by
  apply (card_le_card (image_subset_image (show
      A.filter (fun i => representative hS univ 0 (2^ell)
        (parentLabel (source h R E a m p) 0 (2^ell) i) = j) ⊆
      A.filter (fun i => parentLabel (source h R E a m p) 0 (2^ell) i =
        parentLabel (source h R E a m p) 0 (2^ell) j) from ?_))).trans
    (local_source_phase_fiber_card h R E a m ell f p _ A)
  intro i hi
  refine mem_filter.mpr ⟨(mem_filter.mp hi).1, ?_⟩
  have hh := (representative_spec hS univ 0 (2^ell)
    (mem_image_of_mem (parentLabel (source h R E a m p) 0 (2^ell)) (mem_univ i))).2
  rw [(mem_filter.mp hi).2] at hh
  exact hh.symm

end NativeConfiguredPhaseFibers
