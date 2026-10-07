import Theorems.Thm_StickyKakeya4_native_original_coarse_tuple_menu
import Theorems.Thm_StickyKakeya4_native_point_angular_parent_fibers

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000

noncomputable section
namespace NativeOriginalAngularTupleMenu
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeCubicalIncidenceCounts NativeIncidentRankSelection NativeDirectionRankDichotomy
open NativeDirectionRankWedge NativeOriginalCoarseTupleMenu NativePointAngularParentFibers

/-- Angular projection of the actual phase-parent tuple. -/
def angularTuple {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m : ℕ)
    (xs : List (Fin n × Index)) : List (Fin 3 → ℤ) :=
  (coarseTuple D a m xs).map Prod.fst

def angularMenu {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m : ℕ)
    (E : Finset (Fin n × Index)) (k : Index) (q : ℝ) (ell : ℕ) :
    Finset (List (Fin 3 → ℤ)) :=
  (chains (pointSet E k) (fun z => slopeVector D z.1) q ell).image (angularTuple D a m)

lemma angularMenu_eq_image_coarseMenu {n : ℕ} (D : FiniteScaleSource n)
    (a : ℝ) (m : ℕ) (E : Finset (Fin n × Index)) (k : Index) (q : ℝ) (ell : ℕ) :
    angularMenu D a m E k q ell =
      (coarseMenu D a m E k q ell).image (List.map Prod.fst) := by
  simp only [angularMenu,coarseMenu,image_image,Function.comp_def]
  rfl

/-- Each coarse tuple uses only the actual parents incident to this same old
point, with the original fine tuple's length. -/
lemma coarse_member_labels {n : ℕ} (D : FiniteScaleSource n)
    (a : ℝ) (m : ℕ) (E : Finset (Fin n × Index)) (k : Index) (q : ℝ) (ell : ℕ)
    (ps : List Parent) (hps : ps∈coarseMenu D a m E k q ell) :
    ps.length=ell ∧ ∀p∈ps,p∈pointParents D a (2^m) E k := by
  obtain ⟨xs,hxs,rfl⟩ := mem_image.mp hps
  constructor
  · rw [coarseTuple,List.length_map]
    exact chains_length _ _ _ _ xs hxs
  · intro p hp
    obtain ⟨z,hz,hzp⟩ := List.mem_map.mp hp
    exact mem_image.mpr ⟨z,chains_labels _ _ _ _ xs hxs z hz,hzp⟩

/-- The actual pointwise phase-to-angular fiber capacity gives precisely the
343^ell tuple loss. This comparison does not identify phase and angular menus
or assume a tuple-cover certificate. It holds at every scale with N*delta≤1. -/
theorem coarse_to_angular_card_lower {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (m : ℕ) (hscale : ((2^m:ℕ):ℝ)*D.thickness≤1)
    (E : Finset (Fin n × Index)) (hE : E⊆incidences original)
    (k : Index) (q : ℝ) (ell : ℕ) :
    ((coarseMenu D a m E k q ell).card:ℝ)/(343:ℝ)^ell ≤
      ((angularMenu D a m E k q ell).card:ℝ) := by
  rw [angularMenu_eq_image_coarseMenu]
  apply NativeFiniteTupleFibers.coarse_tuple_card_lower
    (pointParents D a (2^m) E k) (coarseMenu D a m E k q ell) Prod.fst ell
    (fun ps hps => (coarse_member_labels D a m E k q ell ps hps).1)
    (fun ps hps => (coarse_member_labels D a m E k q ell ps hps).2)
    343 (by norm_num) _ _ le_rfl
  intro theta
  exact_mod_cast point_parent_fiber_card_le h original horiginal ha (2^m) hscale E hE k theta

/-- Angular projection retains a genuine original transverse fine-chain
witness. No transversality of the rounded angular tuple is asserted here. -/
theorem angular_member_fine_witness {n : ℕ} (D : FiniteScaleSource n)
    (a : ℝ) (m : ℕ) (E : Finset (Fin n × Index)) (k : Index)
    (q : ℝ) (hq : 0 < q) (ell : ℕ) (angles : List (Fin 3 → ℤ))
    (hangles : angles∈angularMenu D a m E k q ell) :
    ∃xs∈chains (pointSet E k) (fun z => slopeVector D z.1) q ell,
      angularTuple D a m xs=angles ∧ xs.length=ell ∧
      (∀z∈xs,z∈E ∧ z.2=k) ∧
      LinearIndependent ℝ (fun i : Fin xs.length => slopeVector D (xs.get i).1) ∧
      q^(2*ell) ≤ (Matrix.gram ℝ (fun i : Fin xs.length => slopeVector D (xs.get i).1)).det := by
  obtain ⟨xs,hxs,hmap⟩ := mem_image.mp hangles
  refine ⟨xs,hxs,hmap,chains_length _ _ _ _ xs hxs,?_,?_,?_⟩
  · intro z hz
    exact mem_filter.mp (chains_labels _ _ _ _ xs hxs z hz)
  · exact separated_linearIndependent _ q hq xs (chains_separated _ _ _ _ xs hxs)
  · exact chains_gram_det_lower _ _ q hq ell xs hxs

end NativeOriginalAngularTupleMenu
