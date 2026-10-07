import Theorems.Thm_StickyKakeya4_native_grain_quotient_image

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 10000000
noncomputable section
namespace NativeGrainQuotientSource
open Classical Finset StickyKakeya4 NativeGrainQuotientGeometry NativeGrainQuotientBins
open NativeGrainQuotientFibers NativeGrainQuotientImage NativeHorizontalGrainSlice
open NativeCommonCubicalMesh NativeOriginalParentSelection NativeSquaredGrainQueries
open NativeParentGrainIncidenceCleanup NativeProjectorCellChart NativeDirectionRankDichotomy
open NativeCompatibleNodeDirections NativeActualHorizontalGrainSlice NativeActualProjectedGrainCount

/-- The genuine original tuple supplies rank and graph direction in the
source caller; only the selected fixed chart and the literal terminal mesh
are passed through. The raw vertex lower bound comes from source cleanup. -/
theorem node_system_full_image_lower {n ell m : ℕ} {D : FiniteScaleSource n} {a q : ℝ}
    {E0 : Finset (Fin n × Index)} {S : Finset Index}
    {point : Index → Index} {tuple : Index → Fin ell → (Fin n × Index)}
    {anchor : Index → Fin ell → Fin n}
    (H : IsNodeDirectionSystem D a m E0 S q ell point tuple anchor)
    (hm : m ≤ phaseDepth m) (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hq : 0 < q)
    (E : Finset (Fin n × Index)) (c : Parent × (Index × Index))
    (hnode : c.2.1∈nodes D m S)
    (P : Submodule ℝ E4) (hP : P≤heightKernel) (hd : Module.finrank ℝ P=ell-1)
    (hc : cell P=cell (sliceSpace
      (spanOf (fun z : Fin n × Index => slopeVector D z.1) (List.ofFn (tuple c.2.1)))))
    (mu : ℝ) (hmu : 0 < mu) (hmesh : mu ≤ physicalMesh m (phaseDepth m)/8) :
    let plane := fun node => spanOf (fun z : Fin n × Index => slopeVector D z.1) (List.ofFn (tuple node))
    (mixedVertices D a m (phaseDepth m) plane ell E c).card ≤
      (((2^(phaseDepth m-m):ℕ):ℝ)*(2*diameter m ell/mu+2)^(4-ell))*
        ((mixedVertices D a m (phaseDepth m) plane ell E c).image
          (fun k => label mu (rawTangent D a m ell c.1 P hd k))).card := by
  intro plane
  by_cases hV : (mixedVertices D a m (phaseDepth m) plane ell E c).Nonempty
  · obtain ⟨hr,v,hvR,hv,hvn⟩ := node_graph_direction H hell hq c.2.1 hnode
    exact full_tangent_image_lower D a m ell hm plane E c hV P hP hell hell4 hd
      (hd.trans hr.symm) hc v hvR hv hvn mu hmu hmesh
  · rw [not_nonempty_iff_eq_empty] at hV
    simp only [hV,card_empty,Nat.cast_zero,image_empty,mul_zero,le_refl]

/-- Source-native dense X fiber, with original raw vertex multiplicity
preserved and the entire exact-height loss visible. -/
theorem node_system_exists_dense_X {n ell m : ℕ} {D : FiniteScaleSource n} {a q : ℝ}
    {E0 : Finset (Fin n × Index)} {S : Finset Index}
    {point : Index → Index} {tuple : Index → Fin ell → (Fin n × Index)}
    {anchor : Index → Fin ell → Fin n}
    (H : IsNodeDirectionSystem D a m E0 S q ell point tuple anchor)
    (hm : m ≤ phaseDepth m) (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hq : 0 < q)
    (E : Finset (Fin n × Index)) (c : Parent × (Index × Index))
    (hnode : c.2.1∈nodes D m S)
    (P : Submodule ℝ E4) (hP : P≤heightKernel) (hd : Module.finrank ℝ P=ell-1)
    (hc : cell P=cell (sliceSpace
      (spanOf (fun z : Fin n × Index => slopeVector D z.1) (List.ofFn (tuple c.2.1)))))
    (mu : ℝ) (hmu : 0 < mu) (hmesh : mu ≤ physicalMesh m (phaseDepth m)/8) :
    let plane := fun node => spanOf (fun z : Fin n × Index => slopeVector D z.1) (List.ofFn (tuple node))
    (mixedVertices D a m (phaseDepth m) plane ell E c).Nonempty →
    ∃t : ℤ,∃b : Fin (4-ell) → ℤ,
      (X D a m ell plane E c t P hP hell hell4 hd mu b).Nonempty ∧
      (mixedVertices D a m (phaseDepth m) plane ell E c).card ≤
        (((2^(phaseDepth m-m):ℕ):ℝ)*(2*diameter m ell/mu+2)^(4-ell))*
          (X D a m ell plane E c t P hP hell hell4 hd mu b).card := by
  intro plane hV
  obtain ⟨hr,v,hvR,hv,hvn⟩ := node_graph_direction H hell hq c.2.1 hnode
  exact exists_dense_X D a m ell hm plane E c hV P hP hell hell4 hd
    (hd.trans hr.symm) hc v hvR hv hvn mu hmu hmesh

/-- Transport a previously computed source-grain density to ALL original
vertices' tangent image, preserving the literal transverse q factor. -/
theorem node_system_source_density {n ell m : ℕ} {D : FiniteScaleSource n} {a q : ℝ}
    {E0 : Finset (Fin n × Index)} {S : Finset Index}
    {point : Index → Index} {tuple : Index → Fin ell → (Fin n × Index)}
    {anchor : Index → Fin ell → Fin n}
    (H : IsNodeDirectionSystem D a m E0 S q ell point tuple anchor)
    (hm : m ≤ phaseDepth m) (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hq : 0 < q)
    (E : Finset (Fin n × Index)) (c : Parent × (Index × Index))
    (hnode : c.2.1∈nodes D m S)
    (P : Submodule ℝ E4) (hP : P≤heightKernel) (hd : Module.finrank ℝ P=ell-1)
    (hc : cell P=cell (sliceSpace
      (spanOf (fun z : Fin n × Index => slopeVector D z.1) (List.ofFn (tuple c.2.1)))))
    (mu : ℝ) (hmu : 0 < mu) (hmesh : mu ≤ physicalMesh m (phaseDepth m)/8)
    (L C : ℝ) (hC : 0 ≤ C) :
    let plane := fun node => spanOf (fun z : Fin n × Index => slopeVector D z.1) (List.ofFn (tuple node))
    L < (C*transverseCost q ell)*(mixedVertices D a m (phaseDepth m) plane ell E c).card →
    L < (C*transverseCost q ell)*((2^(phaseDepth m-m):ℕ):ℝ)*(2*diameter m ell/mu+2)^(4-ell)*
      ((mixedVertices D a m (phaseDepth m) plane ell E c).image
        (fun k => label mu (rawTangent D a m ell c.1 P hd k))).card := by
  intro plane hsource
  have hretain := node_system_full_image_lower H hm hell hell4 hq E c hnode P hP hd hc mu hmu hmesh
  exact density_transfer (mul_nonneg hC (transverseCost_pos hq ell).le) hsource hretain

end NativeGrainQuotientSource
