import Theorems.Thm_StickyKakeya4_native_original_angular_tuple_menu
import Theorems.Thm_StickyKakeya4_native_angular_packet_readback
import Mathlib.Data.List.OfFn

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2800000

noncomputable section
namespace NativeGlobalAngularRepresentatives
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeCubicalIncidenceCounts NativeOriginalCellChartGeometry NativeDirectionRankDichotomy
open NativeIncidentRankSelection NativeOriginalAngularTupleMenu

/-- The actual global family of occupied angular tuples, formed from the
unchanged retained original point fibers. -/
def globalAngularMenu {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m : ℕ)
    (E : Finset (Fin n × Index)) (q : ℝ) (ell : ℕ) : Finset (List (Fin 3 → ℤ)) :=
  (E.image Prod.snd).biUnion (fun k => angularMenu D a m E k q ell)

/-- An occupied global angular tuple has an actual original fine-chain witness.
Its proven length supplies a fixed Fin ell coordinate type without replacing
any original label or asserting transversality of rounded angular vectors. -/
theorem global_fine_representative {n : ℕ} (D : FiniteScaleSource n)
    (a : ℝ) (m : ℕ) (E : Finset (Fin n × Index)) (q : ℝ) (hq : 0 < q)
    (ell : ℕ) (angles : List (Fin 3 → ℤ))
    (hangles : angles∈globalAngularMenu D a m E q ell) :
    ∃k∈E.image Prod.snd, ∃t : Fin ell → (Fin n × Index),
      (∀j,t j∈E ∧ (t j).2=k) ∧
      List.ofFn t∈chains (pointSet E k) (fun z => slopeVector D z.1) q ell ∧
      angularTuple D a m (List.ofFn t)=angles ∧
      LinearIndependent ℝ (fun j => slopeVector D (t j).1) ∧
      q^(2*ell) ≤ (Matrix.gram ℝ (fun j => slopeVector D (t j).1)).det := by
  obtain ⟨k,hk,hlocal⟩ := mem_biUnion.mp hangles
  obtain ⟨xs,hxs,hmap,hlen,hlabels,hli,hgram⟩ :=
    angular_member_fine_witness D a m E k q hq ell angles hlocal
  subst ell
  refine ⟨k,hk,xs.get,?_,?_,?_,hli,hgram⟩
  · exact fun j => hlabels (xs.get j) (List.get_mem xs j)
  · simpa only [List.ofFn_get] using hxs
  · simpa only [List.ofFn_get] using hmap

/-- Choose one genuine fine tuple ONCE per occupied global angular tuple.
The chosen point records its provenance; the vectors and original labels are
then fixed for all later uses of that angular tuple. -/
theorem exists_global_representatives {n : ℕ} (D : FiniteScaleSource n)
    (a : ℝ) (m : ℕ) (E : Finset (Fin n × Index)) (q : ℝ) (hq : 0 < q) (ell : ℕ) :
    ∃ (point : (globalAngularMenu D a m E q ell) → Index)
      (tuple : (globalAngularMenu D a m E q ell) → Fin ell → (Fin n × Index)),
      ∀tau, point tau∈E.image Prod.snd ∧
        (∀j,tuple tau j∈E ∧ (tuple tau j).2=point tau) ∧
        List.ofFn (tuple tau)∈chains (pointSet E (point tau))
          (fun z => slopeVector D z.1) q ell ∧
        angularTuple D a m (List.ofFn (tuple tau))=tau.val ∧
        LinearIndependent ℝ (fun j => slopeVector D (tuple tau j).1) ∧
        q^(2*ell) ≤ (Matrix.gram ℝ (fun j => slopeVector D (tuple tau j).1)).det := by
  have H (tau : globalAngularMenu D a m E q ell) :=
    global_fine_representative D a m E q hq ell tau.val tau.property
  choose point hpoint tuple htuple using H
  exact ⟨point,tuple,fun tau => ⟨hpoint tau,htuple tau⟩⟩

/-- The globally chosen original fine witnesses retain their proved Gram bound
and control the genuine old tube packets at EVERY matching old incidence.
Each packet is anchored at its current old cell, which may differ from the
representative's own witness point. No new incidence or marked-time witness is
substituted, and rounded angular labels are not declared transverse. -/
theorem exists_global_transverse_packets {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (a : ℝ) (m : ℕ) (hlarge : 64/((2^m:ℕ):ℝ) ≤ 1)
    (hscale : D.thickness ≤ (64/((2^m:ℕ):ℝ))^2)
    (E : Finset (Fin n × Index)) (hE : E⊆incidences original)
    (q : ℝ) (hq : 0 < q) (ell : ℕ) :
    ∃ (point : (globalAngularMenu D a m E q ell) → Index)
      (tuple : (globalAngularMenu D a m E q ell) → Fin ell → (Fin n × Index)),
      ∀tau, point tau∈E.image Prod.snd ∧
        (∀j,tuple tau j∈E ∧ tuple tau j∈incidences original ∧
          (tuple tau j).2=point tau) ∧
        List.ofFn (tuple tau)∈chains (pointSet E (point tau))
          (fun z => slopeVector D z.1) q ell ∧
        angularTuple D a m (List.ofFn (tuple tau))=tau.val ∧
        LinearIndependent ℝ (fun j => slopeVector D (tuple tau j).1) ∧
        q^(2*ell) ≤ (Matrix.gram ℝ (fun j => slopeVector D (tuple tau j).1)).det ∧
        ∀j : Fin ell, ∀i : Fin n, ∀k : Index, (i,k)∈incidences original →
          (parentLabel D a (2^m) i).1=(parentLabel D a (2^m) (tuple tau j).1).1 →
          ∀y : E4, y∈markedUnitTube (D.line i) D.thickness →
            |y (3:Fin 4)-cellCenter (mesh D) k (3:Fin 4)| ≤ 64/((2^m:ℕ):ℝ) →
            Metric.infDist (y-cellCenter (mesh D) k)
              (Submodule.span ℝ {slopeVector D (tuple tau j).1}:Set E4) ≤
                14*(64/((2^m:ℕ):ℝ))^2 := by
  obtain ⟨point,tuple,H⟩ := exists_global_representatives D a m E q hq ell
  refine ⟨point,tuple,?_⟩
  intro tau
  obtain ⟨hp,hlabels,hchain,hmap,hli,hgram⟩ := H tau
  refine ⟨hp,?_,hchain,hmap,hli,hgram,?_⟩
  · intro j
    exact ⟨(hlabels j).1,hE (hlabels j).1,(hlabels j).2⟩
  · intro j i k hik hangular y hy hheight
    exact NativeAngularPacketReadback.original_tube_packet_from_angular_label
      h original horiginal a (2^m) (by positivity) hlarge hscale hik
      (tuple tau j).1 hangular hy hheight

end NativeGlobalAngularRepresentatives
