import Theorems.Thm_StickyKakeya4_native_short_row_packets
import Theorems.Thm_StickyKakeya4_native_scaled_line_packets
import Theorems.Thm_StickyKakeya4_native_squared_grain_queries

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000

noncomputable section
namespace NativeOriginalPacketReference
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalCellChartGeometry
open NativeOriginalParentSelection NativeCubicalIncidenceCounts NativeSpatialAngularGeometry
open NativeShortRowPackets NativeScaledLinePackets NativeQuantizedLinePackets NativeSquaredGrainQueries
open NativeDirectionRankDichotomy

/-- The actual center of the physical vertex containing an original microcell. -/
def rawVertex {n : ℕ} (D : FiniteScaleSource n) (p : ℕ) (k : Index) : E4 :=
  cellCenter (64/((2^p:ℕ):ℝ)) (spatialLabel D (2^p) k)

/-- Complete original vertex fibers lie in the literal fixed packet label.
Both numerical packet predicates follow from the genuine original short row;
neither an approximate-line nor a height certificate is an input. -/
theorem full_fiber_mem_packet {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (level m : ℕ) (hdy : D.thickness=(2:ℝ)⁻¹^level) (hmL : m ≤ level) (hm6 : 6 ≤ m)
    (hlarge : 64/((2^m:ℕ):ℝ) ≤ 1)
    (hscale : D.thickness ≤ (64/((2^m:ℕ):ℝ))^2)
    (rep : Parent → Fin n) (E : Finset (Fin n × Index)) (hE : E⊆incidences original)
    (anchor : Fin n × Index) (hanchor : anchor∈E) (j : Fin n)
    (hangular : (parentLabel D a (2^m) anchor.1).1=(parentLabel D a (2^m) j).1)
    (k : Index) (hk : k∈shortVertexClosure D a level (phaseDepth m) m rep E anchor) :
    k∈E.image Prod.snd ∧
      NativeScaledLinePackets.packet (slopeVector D j) (64/((2^(phaseDepth m):ℕ):ℝ)) (64/((2^m:ℕ):ℝ)) 64 512
        (packetLabel (slopeVector D j) (64/((2^(phaseDepth m):ℕ):ℝ)) (64/((2^m:ℕ):ℝ))
          (rawVertex D (phaseDepth m) anchor.2)) (rawVertex D (phaseDepth m) k) := by
  obtain ⟨hkE,hkv⟩ := mem_filter.mp hk
  have hsq := squared_scale_identity m hm6
  have hy := cellCenter_mem (show (0:ℝ)<64/((2^(phaseDepth m):ℕ):ℝ) by positivity)
    (spatialLabel D (2^(phaseDepth m)) k)
  have hline := short_vertex_rounded_packet h original horiginal ha level (phaseDepth m) m hdy hmL
    hscale (phase_inverse_le_square m hm6) hsq.le rep E hE anchor hanchor j hangular _ hkv hy
  have hheight := short_vertex_rounded_height a level (phaseDepth m) m hdy hmL hlarge hsq.le rep E anchor _ hkv hy
  refine ⟨hkE,?_⟩
  apply packetLabel_mem_neighbors_of_row (slopeVector D j)
    (64/((2^(phaseDepth m):ℕ):ℝ)) (64/((2^m:ℕ):ℝ)) (by positivity) (by positivity)
    64 512 (by norm_num) (rawVertex D (phaseDepth m) anchor.2) (rawVertex D (phaseDepth m) k)
  · dsimp only [rawVertex]
    exact hline.trans (by rw [hsq]; nlinarith [sq_nonneg (64/((2^m:ℕ):ℝ))])
  · exact hheight

end NativeOriginalPacketReference
