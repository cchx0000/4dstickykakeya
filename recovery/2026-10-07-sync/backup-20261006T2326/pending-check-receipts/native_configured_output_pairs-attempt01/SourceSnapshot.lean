import Theorems.Thm_StickyKakeya4_native_actual_configured_tube
import Theorems.Thm_StickyKakeya4_native_relative_parent_profiles
import Theorems.Thm_StickyKakeya4_native_dyadic_parent_cells

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 2400000
noncomputable section
namespace NativeConfiguredIncidenceFibers
open Classical Finset StickyKakeya4 NativeOriginalParentSelection NativeCommonCubicalMesh
open NativeLocalParentSource NativeRelativeParentLabels NativeRelativeParentProfiles

/-- The canonical index of an unchanged original tube in its full admitted
parent source. The fallback is never used on the retained parent graph. -/
def localIndex {n : ℕ} {D : FiniteScaleSource n} {eta etaS : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (E : Finset (Fin n × Index)) (a : ℝ) (m : ℕ) (p : Parent)
    (hS : IsWangZakharovNativeFiniteInput (source h R E a m p) etaS)
    (i : Fin n) : Fin (parentLabels D R a (2^m) p).card :=
  if hi : i ∈ parentLabels D R a (2^m) p then
    (parentLabels D R a (2^m) p).equivFin ⟨i, hi⟩ else ⟨0, hS.1.1⟩

lemma localIndex_readback {n : ℕ} {D : FiniteScaleSource n} {eta etaS : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (E : Finset (Fin n × Index)) (a : ℝ) (m : ℕ) (p : Parent)
    (hS : IsWangZakharovNativeFiniteInput (source h R E a m p) etaS)
    (i : Fin n) (hi : i ∈ parentLabels D R a (2^m) p) :
    NativePaddedCellSource.originalLabel (parentLabels D R a (2^m) p)
      (localIndex h R E a m p hS i)=i := by
  simp only [localIndex, dif_pos hi, NativePaddedCellSource.originalLabel,
    Equiv.symm_apply_apply]

/-- The actual finite index set of the complete second coarse source. -/
abbrev OutputIndex {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (E : Finset (Fin n × Index)) (a : ℝ) (m ell : ℕ) (p : Parent) :=
  Fin (((univ : Finset (Fin (parentLabels D R a (2^m) p).card)).image
    (parentLabel (source h R E a m p) 0 (2^ell))).card)

/-- The actual index of the fullSource tube containing the configured
point. Its unchanged original representative is chosen inside fullSource. -/
def outputTube {n : ℕ} {D : FiniteScaleSource n} {eta etaS : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (E : Finset (Fin n × Index)) (a : ℝ) (m ell : ℕ) (p : Parent)
    (hS : IsWangZakharovNativeFiniteInput (source h R E a m p) etaS) (i : Fin n) :
    OutputIndex h R E a m ell p :=
  NativeActualConfiguredTube.fullIndex (source h R E a m p) ell (localIndex h R E a m p hS i)

/-- The selector may install the literal relative phase before the
full-source index is named; this is its exact later index readback. -/
theorem outputTube_readback {n : ℕ} {D : FiniteScaleSource n} {eta etaS : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (E : Finset (Fin n × Index)) (a : ℝ) (m ell : ℕ) (p : Parent)
    (hS : IsWangZakharovNativeFiniteInput (source h R E a m p) etaS)
    (i : Fin n) (hi : i∈parentLabels D R a (2^m) p) :
    NativeCoarseCellSource.parentIndex
      ((univ : Finset (Fin (parentLabels D R a (2^m) p).card)).image
        (parentLabel (source h R E a m p) 0 (2^ell)))
      (outputTube h R E a m ell p hS i) = relativeLabel D a (2^m) p (2^ell) i := by
  rw [outputTube, NativeActualConfiguredTube.fullIndex_readback, source_parentLabel,
    localIndex_readback h R E a m p hS i hi]

/-- The original relative phase relation is exactly equality of actual
output indices, so pair-fiber uniformity survives the index realization. -/
theorem outputTube_eq_iff {n : ℕ} {D : FiniteScaleSource n} {eta etaS : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (E : Finset (Fin n × Index)) (a : ℝ) (m ell : ℕ) (p : Parent)
    (hS : IsWangZakharovNativeFiniteInput (source h R E a m p) etaS)
    (i j : Fin n) (hi : i∈parentLabels D R a (2^m) p)
    (hj : j∈parentLabels D R a (2^m) p) :
    outputTube h R E a m ell p hS i=outputTube h R E a m ell p hS j ↔
      relativeLabel D a (2^m) p (2^ell) i=relativeLabel D a (2^m) p (2^ell) j := by
  rw [← outputTube_readback h R E a m ell p hS i hi,
    ← outputTube_readback h R E a m ell p hS j hj]
  exact (NativeCoarseCellSource.parentIndex_injective _).eq_iff.symm

/-- The selector's phase-first key is equivalent to the actual
point-first output pair, for the same fixed configured-point map. -/
theorem outputPair_eq_iff {n : ℕ} {D : FiniteScaleSource n} {eta etaS : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (E : Finset (Fin n × Index)) (a : ℝ) (m ell : ℕ) (p : Parent)
    (hS : IsWangZakharovNativeFiniteInput (source h R E a m p) etaS)
    (configured : Index → E4) (z w : Fin n × Index)
    (hz : z.1∈parentLabels D R a (2^m) p)
    (hw : w.1∈parentLabels D R a (2^m) p) :
    (relativeLabel D a (2^m) p (2^ell) z.1, configured z.2) =
      (relativeLabel D a (2^m) p (2^ell) w.1, configured w.2) ↔
    (configured z.2, outputTube h R E a m ell p hS z.1) =
      (configured w.2, outputTube h R E a m ell p hS w.1) := by
  constructor
  · intro he
    exact Prod.ext (congrArg Prod.snd he)
      ((outputTube_eq_iff h R E a m ell p hS z.1 w.1 hz hw).mpr (congrArg Prod.fst he))
  · intro he
    exact Prod.ext
      ((outputTube_eq_iff h R E a m ell p hS z.1 w.1 hz hw).mp (congrArg Prod.snd he))
      (congrArg Prod.fst he)

/-- The exact phase key used by the third selector and the actual
configured-point/full-source-index graph have identical cardinalities. -/
theorem outputPair_image_card {n : ℕ} {D : FiniteScaleSource n} {eta etaS : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (E : Finset (Fin n × Index)) (a : ℝ) (m ell : ℕ) (p : Parent)
    (hS : IsWangZakharovNativeFiniteInput (source h R E a m p) etaS)
    (configured : Index → E4) (H : Finset (Fin n × Index))
    (hH : ∀z∈H, z.1∈parentLabels D R a (2^m) p) :
    (H.image (fun z => (relativeLabel D a (2^m) p (2^ell) z.1, configured z.2))).card =
      (H.image (fun z => (configured z.2,outputTube h R E a m ell p hS z.1))).card := by
  let parents := (univ : Finset (Fin (parentLabels D R a (2^m) p).card)).image
    (parentLabel (source h R E a m p) 0 (2^ell))
  let forget := fun z : E4 × OutputIndex h R E a m ell p =>
    (NativeCoarseCellSource.parentIndex parents z.2,z.1)
  have hinj : Function.Injective forget := by
    intro z w he
    exact Prod.ext (congrArg Prod.snd he)
      (NativeCoarseCellSource.parentIndex_injective parents (congrArg Prod.fst he))
  have himage :
      (H.image (fun z => (configured z.2,outputTube h R E a m ell p hS z.1))).image forget =
      H.image (fun z => (relativeLabel D a (2^m) p (2^ell) z.1,configured z.2)) := by
    rw [Finset.image_image]
    apply Finset.image_congr
    intro z hz
    exact Prod.ext (outputTube_readback h R E a m ell p hS z.1 (hH z hz)) rfl
  rw [←himage,Finset.card_image_of_injective _ hinj]

/-- The selector's pair fibers are the literal geometric pair fibers,
including every retained original occurrence before deduplication. -/
theorem outputPair_fiber_eq {n : ℕ} {D : FiniteScaleSource n} {eta etaS : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (E : Finset (Fin n × Index)) (a : ℝ) (m ell : ℕ) (p : Parent)
    (hS : IsWangZakharovNativeFiniteInput (source h R E a m p) etaS)
    (configured : Index → E4) (H : Finset (Fin n × Index))
    (hH : ∀z∈H, z.1∈parentLabels D R a (2^m) p)
    (w : Fin n × Index) (hw : w∈H) :
    H.filter (fun z =>
      (relativeLabel D a (2^m) p (2^ell) z.1, configured z.2) =
        (relativeLabel D a (2^m) p (2^ell) w.1, configured w.2)) =
    H.filter (fun z =>
      (configured z.2,outputTube h R E a m ell p hS z.1) =
        (configured w.2,outputTube h R E a m ell p hS w.1)) := by
  apply Finset.filter_congr
  intro z hz
  exact outputPair_eq_iff h R E a m ell p hS configured z w (hH z hz) (hH w hw)

/-- Every coarser old relative phase is read from the same fullSource
index by literal dyadic ancestry. No charted phase label is substituted. -/
theorem outputTube_ancestor_readback {n : ℕ} {D : FiniteScaleSource n} {eta etaS : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (E : Finset (Fin n × Index)) (a : ℝ) (m b c : ℕ) (hc : c ≤ b) (p : Parent)
    (hS : IsWangZakharovNativeFiniteInput (source h R E a m p) etaS)
    (i : Fin n) (hi : i∈parentLabels D R a (2^m) p) :
    NativeDyadicParentCells.ancestor b c
      (NativeCoarseCellSource.parentIndex
        ((univ : Finset (Fin (parentLabels D R a (2^m) p).card)).image
          (parentLabel (source h R E a m p) 0 (2^b)))
        (outputTube h R E a m b p hS i)) = relativeLabel D a (2^m) p (2^c) i := by
  rw [outputTube, NativeActualConfiguredTube.fullIndex_readback,
    NativeDyadicParentCells.parent_ancestor_eq _ _ hc, source_parentLabel,
    localIndex_readback h R E a m p hS i hi]

end NativeConfiguredIncidenceFibers
