import Theorems.Thm_StickyKakeya4_native_compatible_node_directions
import Theorems.Thm_StickyKakeya4_native_local_plane_packet_transfer

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 3200000

noncomputable section
namespace NativeCompatiblePlaneVariation
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeSpatialAngularGeometry
open NativeDirectionRankDichotomy NativeIncidentRankSelection NativeOriginalAngularTupleMenu
open NativeOriginalCoarseTupleMenu NativeCompatibleAngularCandidates NativeSeparatedSpanControl

/-- Coarsening an installed representative uses the same terminal original
witness, so no arbitrary angular ancestor compatibility is assumed. -/
theorem installed_word_coarsens {n : ℕ} (D : FiniteScaleSource n) (a : ℝ)
    (stop f m : ℕ) (hfs : f ≤ stop) (hmf : m ≤ f)
    (E : Finset (Fin n × Index)) (q : ℝ) (ell : ℕ)
    (p : Index × List (Fin 3 → ℤ)) (hp : p∈terminalFamily D a stop E q ell)
    (xs : List (Fin n × Index))
    (hx : angularTuple D a f xs=projectWord stop f p.2) :
    angularTuple D a m xs=projectWord stop m p.2 := by
  obtain ⟨zs,_hz,hword,_hlen,_hlabels⟩ := terminal_member D a stop E q ell p hp
  rw [←projectWord_angularTuple D a hmf xs,hx,←hword,
    projectWord_angularTuple D a hfs,
    projectWord_angularTuple D a hmf,
    projectWord_angularTuple D a (hmf.trans hfs)]

/-- Actual angular compatibility controls the entire chosen span, with the
explicit separation cost. It does not compare rounded independent frames. -/
theorem matching_word_span_variation {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (a : ℝ) (m : ℕ)
    (xs ys : List (Fin n × Index))
    (he : angularTuple D a m xs=angularTuple D a m ys)
    (A : Finset (Fin n × Index)) (q : ℝ) (hq : 0 < q) (ell : ℕ)
    (hy : ys∈chains A (fun z => slopeVector D z.1) q ell)
    (w : E4) (hw : w∈spanOf (fun z : Fin n × Index => slopeVector D z.1) ys) :
    Metric.infDist w (spanOf (fun z : Fin n × Index => slopeVector D z.1) xs:Set E4) ≤
      (4/((2^m:ℕ):ℝ))*coefficientCost 2 q ell*‖w‖ := by
  let P := spanOf (fun z : Fin n × Index => slopeVector D z.1) xs
  have hxnear : ∀z∈xs,Metric.infDist (slopeVector D z.1) (P:Set E4) ≤ 0 := by
    intro z hz
    obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hz
    have hm : slopeVector D (xs.get i).1∈P := Submodule.subset_span ⟨i,rfl⟩
    exact le_of_eq (Metric.infDist_zero_of_mem hm)
  have hynear := NativeLocalPlanePacketTransfer.matching_word_near_plane D a m xs ys he P 0 hxnear
  have ht := span_near_plane (fun z : Fin n × Index => slopeVector D z.1) q 2
    (2/((2^m:ℕ):ℝ)) hq (by norm_num) (by positivity) ys
    (chains_separated _ _ _ _ _ hy)
    (fun z _hz => NativeRankOneSlopeCap.slopeVector_norm_le_two h z.1) P
    (by simpa only [zero_add] using hynear) w hw
  have hlen := chains_length _ _ _ _ _ hy
  rw [hlen] at ht
  convert ht using 1
  ring

/-- Two already selected node tuples inherit the plane variation at every
common coarser original node. The same original tuple choices are retained. -/
theorem compatible_installed_span_variation {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (a : ℝ)
    (stop f g m : ℕ) (hfs : f ≤ stop) (hgs : g ≤ stop) (hmf : m ≤ f) (hmg : m ≤ g)
    (E : Finset (Fin n × Index)) (q : ℝ) (hq : 0 < q) (ell : ℕ)
    (P : Finset (Index × List (Fin 3 → ℤ))) (hP : P⊆terminalFamily D a stop E q ell)
    (HC : ∀x y,x∈P → y∈P → spatialLabel D (2^m) x.1=spatialLabel D (2^m) y.1 →
      projectWord stop m x.2=projectWord stop m y.2)
    (p t : Index × List (Fin 3 → ℤ)) (hp : p∈P) (ht : t∈P)
    (hnode : spatialLabel D (2^m) p.1=spatialLabel D (2^m) t.1)
    (xs ys : List (Fin n × Index))
    (hx : angularTuple D a f xs=projectWord stop f p.2)
    (hy : angularTuple D a g ys=projectWord stop g t.2)
    (A : Finset (Fin n × Index)) (hys : ys∈chains A (fun z => slopeVector D z.1) q ell)
    (w : E4) (hw : w∈spanOf (fun z : Fin n × Index => slopeVector D z.1) ys) :
    Metric.infDist w (spanOf (fun z : Fin n × Index => slopeVector D z.1) xs:Set E4) ≤
      (4/((2^m:ℕ):ℝ))*coefficientCost 2 q ell*‖w‖ := by
  apply matching_word_span_variation h a m xs ys _ A q hq ell hys w hw
  exact (installed_word_coarsens D a stop f m hfs hmf E q ell p (hP hp) xs hx).trans
    ((HC p t hp ht hnode).trans
      (installed_word_coarsens D a stop g m hgs hmg E q ell t (hP ht) ys hy).symm)

end NativeCompatiblePlaneVariation
