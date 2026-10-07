import Theorems.Thm_StickyKakeya4_native_conditioned_pair_menu
import Theorems.Thm_StickyKakeya4_native_coarse_uniform_image_degrees
import Theorems.Thm_StickyKakeya4_native_scale_menu_successor

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2800000

noncomputable section
namespace NativeConditionalCoarseInterpolation
open Classical Finset StickyKakeya4 NativeOriginalParentSelection NativeCommonCubicalMesh
open NativeOriginalParentDensityCore NativeDyadicParentCells NativeJointUniformCoarseRelations
open NativeIncidenceMultiplicityTower NativeCoarseUniformImageDegrees
open scoped BigOperators

/-- Uniformity is needed only in the original set. Any literal subfamily's
image has average multiplicity bounded by the original image point degrees. -/
theorem subset_image_multiplicity {A P X : Type*} [DecidableEq A] [DecidableEq P]
    [DecidableEq X] (E F : Finset A) (hFE : F ⊆ E) (f : A → P × X) (rad : ℕ)
    (hpair : HasUniformFibers E rad f)
    (hpoint : HasUniformFibers E rad (fun z => (f z).2)) :
    multiplicity (F.image f) ≤ (rad:ℝ)^4*multiplicity (E.image f) := by
  by_cases hF : F.Nonempty
  · have hs : (0:ℝ) < ((F.image f).image Prod.snd).card := by
      exact_mod_cast card_pos.mpr ((hF.image f).image Prod.snd)
    have hc : ((F.image f).card:ℝ) ≤
        ((F.image f).image Prod.snd).card*((rad:ℝ)^4*multiplicity (E.image f)) := by
      have he : ((F.image f).card:ℝ) =
          ∑x∈(F.image f).image Prod.snd,(((F.image f).filter (fun z => z.2=x)).card:ℝ) := by
        exact_mod_cast card_eq_sum_card_image Prod.snd (F.image f)
      rw [he]
      calc
        _ ≤ ∑_x∈(F.image f).image Prod.snd,
            (rad:ℝ)^4*multiplicity (E.image f) := by
          apply sum_le_sum
          intro x _hx
          have hsub : (F.image f).filter (fun z => z.2=x) ⊆
              (E.image f).filter (fun z => z.2=x) := filter_subset_filter _ (image_subset_image hFE)
          have hb := image_point_degree_le_multiplicity E f (rad^2) (rad^2) hpair hpoint x
          have heq : ((rad^2:ℕ):ℝ)*((rad^2:ℕ):ℝ)=(rad:ℝ)^4 := by push_cast; ring
          rw [heq] at hb
          exact (show (((F.image f).filter (fun z => z.2=x)).card:ℝ) ≤
            ((E.image f).filter (fun z => z.2=x)).card by exact_mod_cast card_le_card hsub).trans hb
        _ = _ := by simp
    apply (div_le_iff₀ hs).mpr
    simpa only [mul_comm] using hc
  · rw [not_nonempty_iff_eq_empty.mp hF]
    simp only [image_empty,NativeIncidenceMultiplicityTower.multiplicity,card_empty,Nat.cast_zero,div_zero]
    positivity

/-- A parent label determined by an image pair commutes exactly with taking
that image. This is the crucial absence of a new representative choice. -/
lemma image_parent_filter {A P X Q : Type*} [DecidableEq A] [DecidableEq P]
    [DecidableEq X] [DecidableEq Q] (E : Finset A) (f : A → P × X)
    (outer : A → Q) (ancestor : P → Q)
    (H : ∀z∈E,ancestor (f z).1=outer z) (q : Q) :
    (E.filter (fun z => outer z=q)).image f = parent (E.image f) ancestor q := by
  ext b
  simp only [mem_image,mem_filter,parent]
  constructor
  · rintro ⟨z,⟨hz,hq⟩,rfl⟩
    exact ⟨⟨z,hz,rfl⟩,(H z hz).trans hq⟩
  · rintro ⟨⟨z,hz,rfl⟩,hq⟩
    exact ⟨z,⟨hz,(H z hz).symm.trans hq⟩,rfl⟩

lemma physicalPair_parent {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (a : ℝ) (level f : ℕ) (z : Fin n × Index) :
    (physicalPair h R a level f z).1=parentLabel D a (2^f) z.1 := rfl

/-- The global f-coarse image of an original m-parent is its literal ancestor
fiber in the one global image. The source R and every representative stay fixed. -/
theorem physical_image_parent {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (E : Finset (Fin n × Index)) (a : ℝ) (level m f : ℕ) (hmf : m ≤ f) (p : Parent) :
    (parentEdges D a (2^m) E p).image (physicalPair h R a level f) =
      parent (E.image (physicalPair h R a level f)) (ancestor f m) p := by
  apply image_parent_filter E (physicalPair h R a level f)
    (fun z => parentLabel D a (2^m) z.1) (ancestor f m)
  intro z _hz
  rw [physicalPair_parent,parent_ancestor_eq D a hmf z.1]

/-- Off-menu outer-parent upper interpolation, at one unchanged physical
projection scale. Uniformity is imposed only on the scheduled ancestor. -/
theorem finer_outer_parent_upper {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (E : Finset (Fin n × Index)) (a : ℝ) (level coarse fine f rad : ℕ)
    (hcf : coarse ≤ fine) (q : Parent)
    (hpair : HasUniformFibers (parentEdges D a (2^coarse) E (ancestor fine coarse q))
      rad (physicalPair h R a level f))
    (hpoint : HasUniformFibers (parentEdges D a (2^coarse) E (ancestor fine coarse q))
      rad (fun z => (physicalPair h R a level f z).2)) :
    multiplicity ((parentEdges D a (2^fine) E q).image (physicalPair h R a level f)) ≤
      (rad:ℝ)^4*multiplicity
        ((parentEdges D a (2^coarse) E (ancestor fine coarse q)).image (physicalPair h R a level f)) :=
  subset_image_multiplicity _ _
    (NativeLocalMenuInterpolation.parentEdges_subset_ancestor D a E hcf q) _ rad hpair hpoint

/-- A lower bound on every finer outer fiber survives their union after the
same physical projection. This requires fine≤f so the physical parent labels
really determine the finer outer partition. -/
theorem coarser_outer_parent_lower {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (E : Finset (Fin n × Index)) (a : ℝ) (level coarse fine f : ℕ)
    (hcf : coarse ≤ fine) (hff : fine ≤ f) (L : ℝ) (hL : 0 ≤ L)
    (H : ∀q,(parentEdges D a (2^fine) E q).Nonempty →
      L ≤ multiplicity ((parentEdges D a (2^fine) E q).image (physicalPair h R a level f)))
    (p : Parent) (hp : (parentEdges D a (2^coarse) E p).Nonempty) :
    L ≤ multiplicity ((parentEdges D a (2^coarse) E p).image (physicalPair h R a level f)) := by
  apply NativeScaleMenuSuccessor.partition_multiplicity_lower _ (ancestor f fine) L hL
    (hp.image (physicalPair h R a level f))
  intro q hq
  have hn := parent_nonempty _ (ancestor f fine) hq
  rw [←physical_image_parent h R (parentEdges D a (2^coarse) E p) a level fine f hff q] at hn ⊢
  have hne : (parentEdges D a (2^fine) (parentEdges D a (2^coarse) E p) q).Nonempty :=
    Nonempty.of_image hn
  have he := NativeScaleMenuSuccessor.nested_parentEdges_eq D a E hcf p q hne
  rw [he]
  exact H q (he ▸ hne)

end NativeConditionalCoarseInterpolation
