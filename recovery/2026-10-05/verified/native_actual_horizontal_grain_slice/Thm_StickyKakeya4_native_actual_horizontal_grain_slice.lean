import Theorems.Thm_StickyKakeya4_native_horizontal_grain_slice

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 3200000

noncomputable section
namespace NativeActualHorizontalGrainSlice
open Classical Finset StickyKakeya4 NativeDirectionRankDichotomy NativeIncidentRankSelection
open NativeCompatibleNodeDirections NativeHorizontalGrainSlice
open NativeCommonCubicalMesh

/-- The actual original tuple supplies the graph direction and the exact
horizontal rank. Neither is a separate geometric certificate. -/
theorem node_graph_direction {n ell m : ℕ} {D : FiniteScaleSource n} {a q : ℝ}
    {E : Finset (Fin n × Index)} {S : Finset Index}
    {point : Index → Index} {tuple : Index → Fin ell → (Fin n × Index)}
    {anchor : Index → Fin ell → Fin n}
    (H : IsNodeDirectionSystem D a m E S q ell point tuple anchor)
    (hell : 0 < ell) (hq : 0 < q) (Q : Index) (hQ : Q∈nodes D m S) :
    let P := spanOf (fun z : Fin n × Index => slopeVector D z.1) (List.ofFn (tuple Q))
    Module.finrank ℝ (sliceSpace P)=ell-1 ∧
      ∃v∈P, v (3:Fin 4)=1 ∧ ‖v‖ ≤ 2 := by
  intro P
  let i : Fin ell := ⟨0,hell⟩
  let v := slopeVector D (tuple Q i).1
  have hm : tuple Q i∈List.ofFn (tuple Q) := List.mem_ofFn.mpr ⟨i,rfl⟩
  obtain ⟨j,hj⟩ := List.mem_iff_get.mp hm
  have hvP : v∈P := by
    apply Submodule.subset_span
    exact ⟨j,congrArg (fun z : Fin n × Index => slopeVector D z.1) hj⟩
  have hv := H.2.2 Q i
  have hd := NativeActualTuplePlaneTransfer.chain_span_finrank D (pointSet E (point Q)) q hq ell
    (List.ofFn (tuple Q)) (H.1 Q hQ).2.2.1
  have hs := sliceSpace_finrank P hvP hv.2
  change Module.finrank ℝ P=ell at hd
  refine ⟨by omega,v,hvP,hv.2,hv.1⟩

/-- Equal-height vertices of an actual node grain lie near its horizontal
ell-minus-one plane. Existing original node directions remain fixed. -/
theorem actual_node_horizontal_slice {n ell m : ℕ} {D : FiniteScaleSource n} {a q : ℝ}
    {E : Finset (Fin n × Index)} {S : Finset Index}
    {point : Index → Index} {tuple : Index → Fin ell → (Fin n × Index)}
    {anchor : Index → Fin ell → Fin n}
    (H : IsNodeDirectionSystem D a m E S q ell point tuple anchor)
    (hell : 0 < ell) (hq : 0 < q) (Q : Index) (hQ : Q∈nodes D m S)
    (x y : E4) (hxy : x (3:Fin 4)=y (3:Fin 4)) (h : ℝ)
    (hnear : Metric.infDist (x-y)
      (spanOf (fun z : Fin n × Index => slopeVector D z.1) (List.ofFn (tuple Q)):Set E4) ≤ h) :
    let P := spanOf (fun z : Fin n × Index => slopeVector D z.1) (List.ofFn (tuple Q))
    Module.finrank ℝ (sliceSpace P)=ell-1 ∧
      Metric.infDist (x-y) (sliceSpace P:Set E4) ≤ 3*h := by
  intro P
  obtain ⟨hd,v,hvP,hv,hvn⟩ := node_graph_direction H hell hq Q hQ
  have ht := near_horizontal_slice P hvP hv hvn hnear
  have he : removeHeight v (x-y)=x-y := by
    change x-y-(x (3:Fin 4)-y (3:Fin 4)) • v=x-y
    rw [hxy,sub_self,zero_smul,sub_zero]
  exact ⟨hd,by simpa only [he] using ht⟩

end NativeActualHorizontalGrainSlice
