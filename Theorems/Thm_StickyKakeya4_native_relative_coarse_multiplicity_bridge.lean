import Theorems.Thm_StickyKakeya4_native_relative_coarse_point_menu
import Theorems.Thm_StickyKakeya4_native_relative_coarse_parameter_bridge
import Theorems.Thm_StickyKakeya4_native_bounded_parent_point_transfer

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000

noncomputable section
namespace NativeRelativeCoarseMultiplicityBridge
open Classical Finset StickyKakeya4 NativeOriginalParentSelection NativeCommonCubicalMesh
open NativeCubicalIncidenceCounts NativeRelativeParentLabels NativeRelativeCoarsePointMenu
open NativeRelativeCoarseParameterBridge NativeIncidenceMultiplicityTower

def globalPair {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (K : ℕ)
    (rep : Parent → Fin n) (z : Fin n × Index) : Parent × Index :=
  (parentLabel D a K z.1,globalLabel D a K (rep (parentLabel D a K z.1)) z.2)

def relativePair {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (N M : ℕ) (p : Parent)
    (rep : Parent → Fin n) (z : Fin n × Index) : Parent × Index :=
  (relativeLabel D a N p M z.1,
    doubleLabel D a N M p (rep (relativeLabel D a N p M z.1)) z.1 z.2)

/-- Exact identification with the original full physical coarse pair map. -/
lemma globalPair_eq_actualPair {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n)) (a : ℝ)
    (level f : ℕ) (hdy : D.thickness=(2:ℝ)⁻¹^level) (hf : f ≤ level)
    (z : Fin n × Index) :
    globalPair D a (2^f) (NativeCoarseDirectionThinning.representative h R a (2^f)) z =
      NativeCoarseScaleInterpolation.actualPair h R a level f z := by
  apply Prod.ext
  · rfl
  · exact globalLabel_eq_projected D a (2^f) (NativeCoarseDyadicShading.block level f)
      (NativeCoarseDyadicShading.block_mesh hdy hf) _ z.2

/-- Actual finite-image (113) bridge inside a fixed original N-parent.
Both pair/point uniformities are on the SAME original E, conditioned on this
parent. The relative source may be read back afterwards; no desired output
profile or inverse spatial-menu bound is assumed here. -/
theorem conditional_global_relative_multiplicity {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta)
    (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i) ∈ Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (level m ell : ℕ) (hdy : D.thickness=(2:ℝ)⁻¹^level) (hell : 6 ≤ ell)
    (hfl : m+ell-6 ≤ level) (p : Parent) (globalRep relativeRep : Parent → Fin n)
    (E : Finset (Fin n × Index)) (hE : E⊆incidences original)
    (hp : ∀z∈E,parentLabel D a (2^m) z.1=p)
    (hg : ∀z∈E,parentLabel D a (2^(m+ell-6))
      (globalRep (parentLabel D a (2^(m+ell-6)) z.1))=parentLabel D a (2^(m+ell-6)) z.1)
    (hr : ∀z∈E,relativeLabel D a (2^m) p (2^ell)
      (relativeRep (relativeLabel D a (2^m) p (2^ell) z.1))=relativeLabel D a (2^m) p (2^ell) z.1)
    (rad : ℕ)
    (hpair : ∀x∈E,∀y∈E,
      (E.filter (fun z => relativePair D a (2^m) (2^ell) p relativeRep z=
        relativePair D a (2^m) (2^ell) p relativeRep x)).card ≤
      rad^2*(E.filter (fun z => relativePair D a (2^m) (2^ell) p relativeRep z=
        relativePair D a (2^m) (2^ell) p relativeRep y)).card)
    (hpoint : ∀x∈E,∀y∈E,
      (E.filter (fun z => (relativePair D a (2^m) (2^ell) p relativeRep z).2=
        (relativePair D a (2^m) (2^ell) p relativeRep x).2)).card ≤
      rad^2*(E.filter (fun z => (relativePair D a (2^m) (2^ell) p relativeRep z).2=
        (relativePair D a (2^m) (2^ell) p relativeRep y).2)).card) :
    multiplicity (E.image (globalPair D a (2^(m+ell-6)) globalRep)) ≤
      (41472:ℝ)*(rad:ℝ)^4*
        multiplicity (E.image (relativePair D a (2^m) (2^ell) p relativeRep)) := by
  have hparent (q : Parent) :
      ((E.filter (fun z => (relativePair D a (2^m) (2^ell) p relativeRep z).1=q)).image
        (fun z => (globalPair D a (2^(m+ell-6)) globalRep z).1)).card ≤ 512 := by
    rw [←globalBox_card p (2^(ell-6)) q]
    apply card_le_card
    intro u hu
    obtain ⟨z,hz,rfl⟩ := mem_image.mp hu
    have hh := relative_global_box D a m ell hell p z.1
    have hzq : relativeLabel D a (2^m) p (2^ell) z.1=q := (mem_filter.mp hz).2
    rwa [hzq] at hh
  have hmenu (q : Index) :
      ((E.filter (fun z => (globalPair D a (2^(m+ell-6)) globalRep z).2=q)).image
        (fun z => (relativePair D a (2^m) (2^ell) p relativeRep z).2)).card ≤ 81 :=
    dyadic_point_fiber_image_card_le h original horiginal ha level m ell hdy hell hfl p
      (fun z => globalRep (parentLabel D a (2^(m+ell-6)) z.1))
      (fun z => relativeRep (relativeLabel D a (2^m) p (2^ell) z.1)) E hE hp hg hr q
  have hh := NativeBoundedParentPointTransfer.uniform_images_multiplicity E
    (globalPair D a (2^(m+ell-6)) globalRep)
    (relativePair D a (2^m) (2^ell) p relativeRep) 512 81 rad hparent hmenu hpair hpoint
  norm_num at hh ⊢
  exact hh

end NativeRelativeCoarseMultiplicityBridge
