import Theorems.Thm_StickyKakeya4_native_finite_tuple_fibers
import Theorems.Thm_StickyKakeya4_native_two_stage_transverse_tuples
import Theorems.Thm_StickyKakeya4_native_rank_one_reference_upper

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 3200000

noncomputable section
namespace NativeOriginalCoarseTupleMenu
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeOriginalParentDensityCore NativeJointUniformCoarseRelations
open NativeDirectionRankDichotomy NativeIncidentRankSelection NativeTwoStageTransverseTuples
open scoped BigOperators

/-- The actual original-parent tuple, retaining the order of the original fine
tuple. No new representative or coarse tuple is chosen. -/
def coarseTuple {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m : ℕ)
    (xs : List (Fin n × Index)) : List Parent :=
  xs.map (fun z => parentLabel D a (2^m) z.1)

def coarseMenu {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m : ℕ)
    (E : Finset (Fin n × Index)) (k : Index) (q : ℝ) (ell : ℕ) : Finset (List Parent) :=
  (chains (pointSet E k) (fun z => slopeVector D z.1) q ell).image (coarseTuple D a m)

/-- The installed original parent/fine-point relation gives actual point
uniformity inside each original parent. This hypothesis is at the stated
installed depth m; an all-depth average bound alone does not imply it. -/
theorem formal_uniform_in_parent {n : ℕ} (D : FiniteScaleSource n)
    (E : Finset (Fin n × Index)) (a : ℝ) (m Q : ℕ)
    (H : HasUniformFibers E Q (formalPair D a m)) (p : Parent) :
    HasUniformFibers (parentEdges D a (2^m) E p) Q Prod.snd := by
  exact NativeConditionedPairMenu.conditioned_uniformity E
    (fun z => parentLabel D a (2^m) z.1) Prod.snd Q H p

/-- Original-reference parent averages and the installed formal relation bound
every actual parent-label fiber at each unchanged original point. -/
theorem reference_point_parent_fiber_upper {n : ℕ} (D : FiniteScaleSource n)
    (E : Finset (Fin n × Index)) (a : ℝ) (m Q : ℕ)
    (H : HasUniformFibers E Q (formalPair D a m)) (U : ℝ) (hU : 0 ≤ U)
    (hupper : ∀p,(parentEdges D a (2^m) E p).Nonempty →
      NativeIncidenceMultiplicityTower.multiplicity (parentEdges D a (2^m) E p) ≤ U)
    (k : Index) (p : Parent) :
    (((pointSet E k).filter (fun z => parentLabel D a (2^m) z.1=p)).card:ℝ) ≤
      (Q:ℝ)^2*U := by
  let I := parentEdges D a (2^m) E p
  have he : (pointSet E k).filter (fun z => parentLabel D a (2^m) z.1=p) =
      I.filter (fun z => z.2=k) := by
    ext z
    simp only [pointSet,I,parentEdges,mem_filter]
    tauto
  rw [he]
  by_cases hI : I.Nonempty
  · have hb := NativeRankOneReferenceUpper.point_degree_le_reference_mean I Q
      (formal_uniform_in_parent D E a m Q H p) k
    exact hb.trans (mul_le_mul_of_nonneg_left (hupper p hI) (sq_nonneg _))
  · rw [not_nonempty_iff_eq_empty.mp hI]
    simp only [filter_empty,card_empty,Nat.cast_zero]
    exact mul_nonneg (sq_nonneg _) hU

/-- Literal deletion preserves the reference fiber upper without an inverse
retention factor. The analytic input still concerns the original E1 parent. -/
theorem retained_point_parent_fiber_upper {n : ℕ} (D : FiniteScaleSource n)
    (E1 E2 : Finset (Fin n × Index)) (h21 : E2 ⊆ E1) (a : ℝ) (m Q : ℕ)
    (H : HasUniformFibers E1 Q (formalPair D a m)) (U : ℝ) (hU : 0 ≤ U)
    (hupper : ∀p,(parentEdges D a (2^m) E1 p).Nonempty →
      NativeIncidenceMultiplicityTower.multiplicity (parentEdges D a (2^m) E1 p) ≤ U)
    (k : Index) (p : Parent) :
    (((pointSet E2 k).filter (fun z => parentLabel D a (2^m) z.1=p)).card:ℝ) ≤
      (Q:ℝ)^2*U := by
  have hs : (pointSet E2 k).filter (fun z => parentLabel D a (2^m) z.1=p) ⊆
      (pointSet E1 k).filter (fun z => parentLabel D a (2^m) z.1=p) :=
    filter_subset_filter _ (filter_subset_filter _ h21)
  exact (show (((pointSet E2 k).filter (fun z => parentLabel D a (2^m) z.1=p)).card:ℝ) ≤
      ((pointSet E1 k).filter (fun z => parentLabel D a (2^m) z.1=p)).card by
    exact_mod_cast card_le_card hs).trans
      (reference_point_parent_fiber_upper D E1 a m Q H U hU hupper k p)

/-- Actual coarse tuple-menu lower bound from the same E2 transverse chains.
The tuple family is constructed from the earlier-rank profile and actual global
retention; the parent-map fiber bound is derived from the ORIGINAL E1 reference.
No arbitrary tuple-cover bound, tuple family or output cardinality is assumed. -/
theorem previous_rank_coarse_tuple_menu {ι : Type*} [DecidableEq ι] {n : ℕ}
    (D : FiniteScaleSource n) (E1 F E2 : Finset (Fin n × Index))
    (hF1 : F ⊆ E1) (h2F : E2 ⊆ F) (Q1 Q2 : ℕ)
    (H1 : HasUniformFibers E1 Q1 Prod.snd) (H2 : HasUniformFibers E2 Q2 Prod.snd)
    (lambda G : ℝ) (hlambda : 0 < lambda) (hG : 0 ≤ G)
    (hret : lambda*(E1.card:ℝ) ≤ G*E2.card)
    (rank previous : Fin 4) (hprevious : previous.val+1=rank.val)
    (allowed : Fin 4 → Finset ι) (radius : ι → ℝ) (eta : Fin 4 → ℝ)
    (test : ι) (htest : test∈allowed previous) (hq : 0 < radius test)
    (Hfailed : ∀k∈F.image Prod.snd, ∀rank' : Fin 4, rank'<rank →
      ∀j∈allowed rank', ∀P : Submodule ℝ E4, Module.finrank ℝ P ≤ rank'.val+1 →
      ((pointNear D E1 k (radius j) P).card:ℝ) <
        (radius j)^(eta rank')*((pointSet E1 k).card:ℝ))
    (hbudget : (radius test)^(eta previous)*G*(Q1:ℝ)^2*(Q2:ℝ)^2 ≤ lambda/2)
    (a : ℝ) (m : ℕ) (Href : HasUniformFibers E1 Q1 (formalPair D a m))
    (U : ℝ) (hU : 0 ≤ U)
    (hupper : ∀p,(parentEdges D a (2^m) E1 p).Nonempty →
      NativeIncidenceMultiplicityTower.multiplicity (parentEdges D a (2^m) E1 p) ≤ U) :
    ∀k∈E2.image Prod.snd,
      let A := pointSet E2 k
      let v := fun z : Fin n × Index => slopeVector D z.1
      let C := chains A v (radius test) (rank.val+1)
      let T := coarseMenu D a m E2 k (radius test) (rank.val+1)
      T.Nonempty ∧
        (((A.card:ℝ)/2)^(rank.val+1))/(((Q1:ℝ)^2*U)^(rank.val+1)) ≤ (T.card:ℝ) ∧
        ∀ps∈T, ps.length=rank.val+1 ∧
          ∃xs∈C, coarseTuple D a m xs=ps ∧ xs.length=rank.val+1 ∧
            (∀z∈xs,z∈E2 ∧ z.2=k) ∧
            LinearIndependent ℝ (fun i : Fin xs.length => v (xs.get i)) ∧
            (radius test)^(2*(rank.val+1)) ≤
              (Matrix.gram ℝ (fun i : Fin xs.length => v (xs.get i))).det := by
  intro k hk
  let A := pointSet E2 k
  let v := fun z : Fin n × Index => slopeVector D z.1
  let C := chains A v (radius test) (rank.val+1)
  let f := fun z : Fin n × Index => parentLabel D a (2^m) z.1
  have hT := previous_rank_menu_transverse_chains D E1 F E2 hF1 h2F Q1 Q2 H1 H2
    lambda G hlambda hG hret rank previous hprevious allowed radius eta test htest hq
    Hfailed hbudget k hk
  obtain ⟨hC,hcount,hfine⟩ := hT
  have hfiber (p : Parent) : ((A.filter (fun z => f z=p)).card:ℝ) ≤ (Q1:ℝ)^2*U :=
    retained_point_parent_fiber_upper D E1 E2 (h2F.trans hF1) a m Q1 Href U hU hupper k p
  have hB : 0 < (Q1:ℝ)^2*U := by
    obtain ⟨z,hz,hzk⟩ := mem_image.mp hk
    have hzA : z∈A := mem_filter.mpr ⟨hz,hzk⟩
    have hp : (0:ℝ) < (A.filter (fun w => f w=f z)).card := by
      have hn : (A.filter (fun w => f w=f z)).Nonempty :=
        ⟨z,mem_filter.mpr ⟨hzA,rfl⟩⟩
      exact_mod_cast card_pos.mpr hn
    exact hp.trans_le (hfiber (f z))
  refine ⟨hC.image (coarseTuple D a m),?_,?_⟩
  · exact NativeFiniteTupleFibers.coarse_tuple_card_lower A C f (rank.val+1)
      (fun xs hxs => (hfine xs hxs).1)
      (fun xs hxs z hz => mem_filter.mpr ((hfine xs hxs).2.1 z hz))
      ((Q1:ℝ)^2*U) hB hfiber (((A.card:ℝ)/2)^(rank.val+1)) hcount
  · intro ps hps
    obtain ⟨xs,hxs,hmap⟩ := mem_image.mp hps
    obtain ⟨hlen,hlabels,_hsep,hli,hgram⟩ := hfine xs hxs
    refine ⟨?_,xs,hxs,hmap,hlen,hlabels,hli,hgram⟩
    rw [←hmap,coarseTuple,List.length_map,hlen]

end NativeOriginalCoarseTupleMenu
