import Theorems.Thm_StickyKakeya4_native_queried_vertex_weights
import Theorems.Thm_StickyKakeya4_native_short_row_packets
import Theorems.Thm_StickyKakeya4_native_refined_short_row_density

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 3200000

noncomputable section
namespace NativeShortRowVertexConversion
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalCellChartGeometry
open NativeCubicalIncidenceCounts NativeOriginalParentSelection NativeOriginalPaddedCells
open NativeCoarseShadingUniformity NativeSpatialAngularGeometry NativeShortRowPackets
open NativeQueriedVertexWeights NativeJointUniformCoarseRelations NativeFullCoarseShadow
open NativeOriginalParentDensityCore NativeRefinedShortRowDensity NativeTwoStageTransversalityBudget
open NativeCoarseDirectionThinning NativeLocalPairFibers
open WeightedRichDirectionalLayers
open scoped BigOperators

lemma shortCells_subset {n : ℕ} (D : FiniteScaleSource n) (a : ℝ)
    (level p m : ℕ) (rep : Parent → Fin n) (E : Finset (Fin n × Index))
    (anchor : Fin n × Index) : shortCells D a level p m rep E anchor⊆E.image Prod.snd :=
  image_subset_image (filter_subset _ _)

/-- The literal short-row edges are paid by their unchanged E2 point weights. -/
lemma shortEdges_le_weight {n : ℕ} (D : FiniteScaleSource n) (a : ℝ)
    (level p m : ℕ) (rep : Parent → Fin n) (E : Finset (Fin n × Index))
    (anchor : Fin n × Index) :
    (shortEdges D a level p m rep E anchor).card ≤
      mass (shortCells D a level p m rep E anchor) (pointWeight E) := by
  rw [mass_pointWeight]
  apply card_le_card
  intro z hz
  exact mem_filter.mpr ⟨(mem_filter.mp hz).1,mem_image_of_mem Prod.snd hz⟩

/-- Projected child counts enter through their literal old-incidence witnesses. -/
lemma rowChildren_le_weight {n : ℕ} {D : FiniteScaleSource n} (a : ℝ)
    (level p m : ℕ) (hdy : D.thickness=(2:ℝ)⁻¹^level) (hmp : m ≤ p) (hpL : p ≤ level)
    (rep : Parent → Fin n) (E : Finset (Fin n × Index)) (anchor : Fin n × Index) :
    (rowChildren D a level p m rep E (parentLabel D a (2^p) anchor.1)
      (fixedPair D a level p m rep anchor).2).card ≤
      mass (shortCells D a level p m rep E anchor) (pointWeight E) := by
  rw [←projected_image_eq_rowChildren a level p m hdy hmp hpL rep E anchor]
  exact card_image_le.trans (shortEdges_le_weight D a level p m rep E anchor)

/-- Actual weighted short rows are bounded by their distinct physical vertices,
using only the installed raw query on the unchanged reference E2. -/
theorem short_weight_le_vertices {n : ℕ} (D : FiniteScaleSource n) (a : ℝ)
    (level p m : ℕ) (rep : Parent → Fin n) (E : Finset (Fin n × Index))
    (Q : ℕ) (HU : HasUniformFibers E Q (fun z => spatialLabel D (2^p) z.2))
    (anchor : Fin n × Index) :
    mass (shortCells D a level p m rep E anchor) (pointWeight E) ≤
      (shortVertices D a level p m rep E anchor).card*vertexCap E (spatialLabel D (2^p)) Q := by
  rw [shortVertices_eq_cells_image]
  exact mass_le_vertices_mul_cap E _ Q HU _ (shortCells_subset D a level p m rep E anchor)

lemma cap_le_second_cost {T X V : Type*} [DecidableEq T] [DecidableEq X] [DecidableEq V]
    {delta eta2 c2 : ℝ} (hd : 0 < delta) (hd1 : delta ≤ 1) (heta2 : 0 ≤ eta2)
    (E : Finset (T × X)) (f : X → V) (F2 Q2 : ℕ) (hF2 : 0 < F2)
    (hcost2 : (125*175616*16384:ℝ)*(F2:ℝ)*(Q2:ℝ)^2*delta^(-eta2) ≤ delta^(-c2)) :
    (vertexCap E f Q2:ℝ) ≤ delta^(-c2)*vertexMultiplicity E f := by
  have hQ : (Q2:ℝ)^2 ≤ delta^(-c2) := by
    simpa only [one_mul] using retention_radix_le_of_transfer_cost hd hd1 heta2 F2 Q2 1
      (by exact_mod_cast (show 1 ≤ F2 by omega)) hcost2
  exact (vertexCap_le_average E f Q2).trans
    (mul_le_mul_of_nonneg_right hQ (by unfold vertexMultiplicity; positivity))

/-- The extra raw vertex radix costs exactly one additional second-stage loss. -/
lemma absorb_vertex_cost {delta coefficient loss cost ratio mu : ℝ}
    (hd : 0 < delta) (n M : ℕ)
    (hrow : coefficient*delta^loss*ratio ≤ (n:ℝ)*(M:ℝ))
    (hcap : (M:ℝ) ≤ delta^(-cost)*mu) :
    coefficient*delta^(loss+cost)*ratio ≤ mu*n := by
  have hh := hrow.trans (mul_le_mul_of_nonneg_left hcap (Nat.cast_nonneg n))
  have hh' := mul_le_mul_of_nonneg_left hh (Real.rpow_pos_of_pos hd cost).le
  calc
    _ = delta^cost*(coefficient*delta^loss*ratio) := by rw [Real.rpow_add hd]; ring
    _ ≤ delta^cost*((n:ℝ)*(delta^(-cost)*mu)) := hh'
    _ = mu*n := by
      have he : delta^cost*delta^(-cost)=1 := by rw [←Real.rpow_add hd]; simp
      calc
        _ = (delta^cost*delta^(-cost))*(mu*n) := by ring
        _ = _ := by rw [he,one_mul]

/-- Fully source-facing queried short-row conversion. Both row relations and
the separate squared-mesh raw point relation belong to this SAME E2.
The rank-retention coefficient lambda is preserved explicitly. -/
theorem queried_short_vertex_lower {n level : ℕ} {D : FiniteScaleSource n}
    {eta eta2 a lambda c1 c2 : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (R : Finset (Fin n)) (E : Finset (Fin n × Index)) (hE : E ⊆ incidences original)
    (F1 F2 G Q1 Q2 : ℕ) (hF1 : 0 < F1) (hG : 0 < G) (hQ2 : 0 < Q2)
    (hQ1 : 1 ≤ Q1) (hGF : G ≤ F2) (heta2 : 0 ≤ eta2)
    (hdy : D.thickness=(2:ℝ)⁻¹^level) (hlambda : 0 < lambda)
    (hRich : ∀e,e∈E → D.thickness^eta*(2^level:ℕ)/
      (16384*(((F1:ℝ)/lambda)*(G:ℝ))*(Q2:ℝ)^2) ≤
        (pairFiber D a (2^level) E (localPair D a (2^level) e)).card)
    (hcost1 : (125*175616*16384:ℝ)*(F1:ℝ)*(Q1:ℝ)^2*D.thickness^(-eta) ≤ D.thickness^(-c1))
    (hcost2 : (125*175616*16384:ℝ)*(F2:ℝ)*(Q2:ℝ)^2*D.thickness^(-eta2) ≤ D.thickness^(-c2))
    (p m : ℕ) (hmp : m ≤ p) (hpL : p ≤ level) (hm6 : 6 ≤ m)
    (HF : HasUniformFibers E Q2 (fixedPair D a level p p (representative h R a (2^p))))
    (HC : HasUniformFibers E Q2 (fixedPair D a level p m (representative h R a (2^p))))
    (HV : HasUniformFibers E Q2 (fun z => spatialLabel D (2^p) z.2))
    (anchor : Fin n × Index) (hanchor : anchor∈E) :
    lambda*D.thickness^(c1+4*c2)*
      ((64/((2^m:ℕ):ℝ))/(64/((2^p:ℕ):ℝ))) ≤
      vertexMultiplicity E (spatialLabel D (2^p))*
        (shortVertices D a level p m (representative h R a (2^p)) E anchor).card := by
  let rep := representative h R a (2^p)
  have hq : (fixedPair D a level p m rep anchor).2∈
      rowCells D a level p m rep E (parentLabel D a (2^p) anchor.1) := by
    apply (mem_rowCells D a level p m rep E _ _).mpr
    exact mem_image_of_mem _ hanchor
  have hrow := queried_short_row_lower h original horiginal ha R E hE F1 F2 G Q1 Q2
    hF1 hG hQ2 hQ1 hGF heta2 hdy hlambda hRich hcost1 hcost2 p m hmp hpL hm6 HF HC
    (parentLabel D a (2^p) anchor.1) (fixedPair D a level p m rep anchor).2 hq
  have hcount := (rowChildren_le_weight a level p m hdy hmp hpL rep E anchor).trans
    (short_weight_le_vertices D a level p m rep E Q2 HV anchor)
  have hrow' := hrow.trans (show
      ((rowChildren D a level p m rep E (parentLabel D a (2^p) anchor.1)
        (fixedPair D a level p m rep anchor).2).card:ℝ) ≤
      ((shortVertices D a level p m rep E anchor).card:ℝ)*vertexCap E (spatialLabel D (2^p)) Q2 by
    exact_mod_cast hcount)
  have hcap := cap_le_second_cost h.1.2.1 h.1.2.2.1 heta2 E (spatialLabel D (2^p)) F2 Q2
    (hG.trans_le hGF) hcost2
  have hh := absorb_vertex_cost h.1.2.1 _ _ hrow' hcap
  simpa only [show c1+3*c2+c2=c1+4*c2 by ring] using hh

/-- The literal short-row union is converted to the actual approximate fiber
of squared-mesh vertices. Its integer threshold is its computed E2 weight. -/
theorem weighted_short_packet_vertices {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (level p m : ℕ) (hdy : D.thickness=(2:ℝ)⁻¹^level) (hmL : m ≤ level)
    (hscale : D.thickness ≤ (64/((2^m:ℕ):ℝ))^2)
    (hparentScale : 1/((2^p:ℕ):ℝ) ≤ (64/((2^m:ℕ):ℝ))^2)
    (hvertexScale : 64/((2^p:ℕ):ℝ) ≤ (64/((2^m:ℕ):ℝ))^2)
    (rep : Parent → Fin n) (E : Finset (Fin n × Index)) (hE : E⊆incidences original)
    (Q : ℕ) (HV : HasUniformFibers E Q (fun z => spatialLabel D (2^p) z.2))
    (anchor : Fin n × Index) (hanchor : anchor∈E) (j : Fin n)
    (hangular : (parentLabel D a (2^m) anchor.1).1=(parentLabel D a (2^m) j).1) :
    mass (shortCells D a level p m rep E anchor) (pointWeight E) ⌈/⌉
        vertexCap E (spatialLabel D (2^p)) Q ≤
      (NativeApproximateFiberCount.fiber (64/((2^p:ℕ):ℝ)) (vertices E (spatialLabel D (2^p)))
        (Submodule.span ℝ {NativeDirectionRankDichotomy.slopeVector D j})
        (cellCenter (64/((2^p:ℕ):ℝ)) (spatialLabel D (2^p) anchor.2))
        (52*(64/((2^m:ℕ):ℝ))^2)).card := by
  apply weighted_approximate_predecessor_vertices E ⟨anchor,hanchor⟩ (spatialLabel D (2^p)) Q HV
    (E.image Prod.snd) (shortCells D a level p m rep E anchor) (Subset.refl _)
    (shortCells_subset D a level p m rep E anchor)
  · exact le_rfl
  · intro b hb
    have hv : spatialLabel D (2^p) b∈shortVertices D a level p m rep E anchor := by
      rw [shortVertices_eq_cells_image]
      exact mem_image_of_mem _ hb
    exact short_vertex_rounded_packet h original horiginal ha level p m hdy hmL
      hscale hparentScale hvertexScale rep E hE anchor hanchor j hangular _ hv
      (cellCenter_mem (by positivity) _)

end NativeShortRowVertexConversion
