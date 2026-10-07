import Theorems.Thm_StickyKakeya4_native_local_parent_source
import Theorems.Thm_StickyKakeya4_native_coarse_direction_thinning

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

noncomputable section
namespace NativeShadingIndependentRepresentatives
open Classical Finset StickyKakeya4 NativeOriginalParentSelection
open NativeLocalParentSource

/-- The geometric representative needs a nonempty index type, but no shading
or native-density input. It is therefore fixed before an incidence refinement. -/
def chooseRepresentative {n : ℕ} (D : FiniteScaleSource n) (hn : 0 < n)
    (R : Finset (Fin n)) (a : ℝ) (N : ℕ) (p : Parent) : Fin n :=
  if hp : p ∈ R.image (parentLabel D a N) then
    Classical.choose (mem_image.mp hp) else ⟨0,hn⟩

lemma chooseRepresentative_eq_canonical {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (a : ℝ) (N : ℕ) (p : Parent) :
    chooseRepresentative D h.1.1 R a N p =
      NativeCoarseDirectionThinning.representative h R a N p := rfl

/-- Changing only shading and other nongeometric metadata does not change
any representative, including the harmless empty-parent fallback. -/
theorem chooseRepresentative_eq_of_geometry {n : ℕ} (D D' : FiniteScaleSource n)
    (hn hn' : 0 < n) (hd : D.thickness = D'.thickness) (hl : D.line = D'.line)
    (R : Finset (Fin n)) (a : ℝ) (N : ℕ) (p : Parent) :
    chooseRepresentative D hn R a N p = chooseRepresentative D' hn' R a N p := by
  have hf : parentLabel D a N = parentLabel D' a N := by
    funext i
    simp only [parentLabel, mesh, shift, hd, hl]
  simp only [chooseRepresentative, hf]

/-- Fix relative representatives on the entire original local backbone with
empty reference shading. No assertion that this empty shading is native is made. -/
def relativeRepresentative {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (a : ℝ) (m : ℕ) (p : Parent)
    (hQ : (parentLabels D R a (2^m) p).Nonempty) (M : ℕ) (q : Parent) :
    Fin (parentLabels D R a (2^m) p).card :=
  chooseRepresentative (source h R ∅ a m p) (card_pos.mpr hQ) univ 0 M q

/-- Once the actual retained local source is admitted, its canonical relative
representative is exactly the one fixed before the choice of retained cells. -/
theorem relativeRepresentative_eq_canonical {n : ℕ} {D : FiniteScaleSource n}
    {eta e : ℝ} (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (E : Finset (Fin n × NativeCommonCubicalMesh.Index)) (a : ℝ) (m : ℕ) (p : Parent)
    (hQ : (parentLabels D R a (2^m) p).Nonempty) (M : ℕ) (q : Parent)
    (hS : IsWangZakharovNativeFiniteInput (source h R E a m p) e) :
    relativeRepresentative h R a m p hQ M q =
      NativeCoarseDirectionThinning.representative hS univ 0 M q := by
  unfold relativeRepresentative
  exact (chooseRepresentative_eq_of_geometry _ _ _ _ rfl (by funext i; rfl)
    univ 0 M q).trans (chooseRepresentative_eq_canonical hS univ 0 M q)

end NativeShadingIndependentRepresentatives
