import Theorems.Thm_StickyKakeya4_native_queried_vertex_weights
import Theorems.Thm_StickyKakeya4_native_short_row_packets
import Theorems.Thm_StickyKakeya4_native_refined_short_row_density
import Theorems.Thm_StickyKakeya4_native_spatial_shadow_point_menu

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 4200000

noncomputable section
namespace NativeFullVertexFiberDensity
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalCellChartGeometry
open NativeCubicalIncidenceCounts NativeOriginalParentSelection NativeOriginalPaddedCells
open NativeCoarseShadingUniformity NativeSpatialAngularGeometry NativeShortRowPackets
open NativeQueriedVertexWeights NativeJointUniformCoarseRelations NativeCoarseDirectionThinning
open NativeOriginalParentDensityCore NativeLocalPairFibers NativeRefinedShortRowDensity
open NativeSpatialShadowPointMenu RichDirectionalLayers WeightedRichDirectionalLayers
open scoped BigOperators

/-- Every occupied reference vertex carries at least the computed cap divided
by Q-fourth. This is a consequence of the installed raw relation. -/
lemma cap_le_vertex_mass {T X V : Type*} [DecidableEq T] [DecidableEq X] [DecidableEq V]
    (E : Finset (T × X)) (f : X → V) (Q : ℕ)
    (HU : HasUniformFibers E Q (fun z => f z.2)) (v : V) (hv : v∈vertices E f) :
    vertexCap E f Q ≤ Q^4*mass (classFiber (E.image Prod.snd) f v) (pointWeight E) := by
  have hs : 0 < (vertices E f).card := card_pos.mpr ⟨v,hv⟩
  apply (mul_le_mul_iff_left₀ hs).mp
  calc
    _ ≤ Q^2*E.card := Nat.div_mul_le_self _ _
    _ ≤ Q^2*(Q^2*mass (classFiber (E.image Prod.snd) f v) (pointWeight E)*(vertices E f).card) :=
      Nat.mul_le_mul_left _ (vertex_lower_cross E f Q HU v hv)
    _ = _ := by ring

lemma full_vertex_fiber_mass {T X V : Type*} [DecidableEq T] [DecidableEq X] [DecidableEq V]
    (E : Finset (T × X)) (f : X → V) (S : Finset V) :
    mass ((E.image Prod.snd).filter (fun k => f k∈S)) (pointWeight E)=
      ∑v∈S,mass (classFiber (E.image Prod.snd) f v) (pointWeight E) := by
  dsimp only [mass]
  calc
    _ = ∑v∈S,∑k∈(E.image Prod.snd).filter (fun k => f k=v),pointWeight E k :=
      (sum_fiberwise_eq_sum_filter (E.image Prod.snd) S f (pointWeight E)).symm
    _ = _ := by
      apply sum_congr rfl
      intro v _hv
      apply sum_congr
      · ext k
        simp only [classFiber,mem_filter]
      · intro k _hk
        rfl

/-- Full original microcell fibers over a vertex set retain their complete
reference weight, even when other tubes occupy those same vertices. -/
theorem full_vertex_fibers_lower {T X V : Type*} [DecidableEq T] [DecidableEq X] [DecidableEq V]
    (E : Finset (T × X)) (f : X → V) (Q : ℕ)
    (HU : HasUniformFibers E Q (fun z => f z.2)) (S : Finset V) (hS : S⊆vertices E f) :
    vertexCap E f Q*S.card ≤
      Q^4*mass ((E.image Prod.snd).filter (fun k => f k∈S)) (pointWeight E) := by
  rw [full_vertex_fiber_mass,mul_sum]
  calc
    _ = ∑_v∈S,vertexCap E f Q := by simp [Nat.mul_comm]
    _ ≤ _ := sum_le_sum (fun v hv => cap_le_vertex_mass E f Q HU v (hS hv))

/-- The closure contains exactly the same physical vertex set, while keeping
all original E-point fibers over those vertices. -/
lemma short_closure_image {n : ℕ} (D : FiniteScaleSource n) (a : ℝ)
    (level p m : ℕ) (rep : Parent → Fin n) (E : Finset (Fin n × Index))
    (anchor : Fin n × Index) :
    (shortVertexClosure D a level p m rep E anchor).image (spatialLabel D (2^p))=
      shortVertices D a level p m rep E anchor := by
  ext v
  constructor
  · intro hv
    obtain ⟨k,hk,rfl⟩ := mem_image.mp hv
    exact (mem_filter.mp hk).2
  · intro hv
    obtain ⟨z,hz,hzv⟩ := mem_image.mp hv
    refine mem_image.mpr ⟨z.2,mem_filter.mpr ⟨?_,?_⟩,hzv⟩
    · exact mem_image_of_mem Prod.snd (mem_filter.mp hz).1
    · rw [hzv]
      exact hv

lemma anchor_mem_short_closure {n : ℕ} (D : FiniteScaleSource n) (a : ℝ)
    (level p m : ℕ) (rep : Parent → Fin n) (E : Finset (Fin n × Index))
    (anchor : Fin n × Index) (hanchor : anchor∈E) :
    anchor.2∈shortVertexClosure D a level p m rep E anchor := by
  refine mem_filter.mpr ⟨mem_image_of_mem Prod.snd hanchor,?_⟩
  exact mem_image.mpr ⟨anchor,mem_filter.mpr ⟨hanchor,rfl⟩,rfl⟩

/-- One physical squared-mesh vertex contains at most2401 of the actual
projected child labels in a fixed fine-parent short row. -/
theorem short_children_le_vertices {n level : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (R : Finset (Fin n)) (E : Finset (Fin n × Index)) (hE : E⊆incidences original)
    (hER : ∀z∈E,z.1∈R) (p m : ℕ) (hmp : m ≤ p) (hpL : p ≤ level)
    (hdy : D.thickness=(2:ℝ)⁻¹^level) (anchor : Fin n × Index) :
    (rowChildren D a level p m (representative h R a (2^p)) E
      (parentLabel D a (2^p) anchor.1)
      (fixedPair D a level p m (representative h R a (2^p)) anchor).2).card ≤
      2401*(shortVertices D a level p m (representative h R a (2^p)) E anchor).card := by
  let rep := representative h R a (2^p)
  let F := shortEdges D a level p m rep E anchor
  have hFE : F⊆E := filter_subset _ _
  have hscale : ((2^p:ℕ):ℝ)*D.thickness ≤ 1 := by
    rw [NativeLocalParentScales.relative_scale hdy hpL]
    exact pow_le_one₀ (by norm_num) (by norm_num)
  have hh := NativeTangentGridCoarsening.image_card_le_real_mul_of_fiber_images F
    (fun z => (fixedPair D a level p p rep z).2)
    (fun z => spatialLabel D (2^p) z.2) 2401 (by
      intro q _hq
      have hqF : F.filter (fun z => spatialLabel D (2^p) z.2=q)⊆E :=
        (filter_subset _ _).trans hFE
      have hc := spatial_point_image_card h original horiginal ha (2^p)
        (NativeCoarseDyadicShading.block level p) (by positivity) hscale
        (NativeCoarseDyadicShading.block_mesh hdy hpL) rep
        (F.filter (fun z => spatialLabel D (2^p) z.2=q)) (hqF.trans hE)
        (fun z hz => (representative_spec h R a (2^p) (mem_image_of_mem _ (hER z (hqF hz)))).2)
        q (fun z hz => (mem_filter.mp hz).2)
      exact_mod_cast hc)
  rw [projected_image_eq_rowChildren a level p m hdy hmp hpL rep E anchor] at hh
  exact_mod_cast hh

/-- No multiplicity is discarded: the full raw-fiber lift contains enough
weight relative to the computed vertex cap to pay the projected child count. -/
theorem short_closure_weight_cross {n level : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (R : Finset (Fin n)) (E : Finset (Fin n × Index)) (hE : E⊆incidences original)
    (hER : ∀z∈E,z.1∈R) (p m : ℕ) (hmp : m ≤ p) (hpL : p ≤ level)
    (hdy : D.thickness=(2:ℝ)⁻¹^level) (Q : ℕ)
    (HV : HasUniformFibers E Q (fun z => spatialLabel D (2^p) z.2)) (anchor : Fin n × Index) :
    vertexCap E (spatialLabel D (2^p)) Q*
      (rowChildren D a level p m (representative h R a (2^p)) E
        (parentLabel D a (2^p) anchor.1)
        (fixedPair D a level p m (representative h R a (2^p)) anchor).2).card ≤
      2401*Q^4*mass (shortVertexClosure D a level p m (representative h R a (2^p)) E anchor)
        (pointWeight E) := by
  let rep := representative h R a (2^p)
  have hV : shortVertices D a level p m rep E anchor⊆vertices E (spatialLabel D (2^p)) := by
    rw [shortVertices_eq_cells_image]
    exact image_subset_image (image_subset_image (filter_subset _ _))
  have hfull := full_vertex_fibers_lower E (spatialLabel D (2^p)) Q HV _ hV
  have hchild := short_children_le_vertices h original horiginal ha R E hE hER p m hmp hpL hdy anchor
  calc
    _ ≤ vertexCap E (spatialLabel D (2^p)) Q*
        (2401*(shortVertices D a level p m rep E anchor).card) := Nat.mul_le_mul_left _ hchild
    _ = 2401*(vertexCap E (spatialLabel D (2^p)) Q*
        (shortVertices D a level p m rep E anchor).card) := by ring
    _ ≤ 2401*(Q^4*mass (shortVertexClosure D a level p m rep E anchor) (pointWeight E)) :=
      Nat.mul_le_mul_left _ hfull
    _ = _ := by ring

lemma vertex_lift_cost {delta eta2 c2 : ℝ} (hd : 0 < delta) (hd1 : delta ≤ 1)
    (heta2 : 0 ≤ eta2) (F2 Q2 : ℕ) (hF2 : 0 < F2)
    (hcost2 : (125*175616*16384:ℝ)*(F2:ℝ)*(Q2:ℝ)^2*delta^(-eta2) ≤ delta^(-c2)) :
    (2401:ℝ)*(Q2:ℝ)^4 ≤ delta^(-(2*c2)) := by
  have hh := (NativePairScaleBudget.radix_four_cost hd hd1 heta2 F2 Q2 hF2 hcost2).1
  exact (mul_le_mul_of_nonneg_right (by norm_num : (2401:ℝ)≤41472)
    (pow_nonneg (Nat.cast_nonneg Q2) 4)).trans hh

/-- Source-derived reference density on complete physical vertex fibers.
The only loss beyond the queried short row is its actual Q-fourth vertex cost. -/
theorem queried_short_closure_lower {n level : ℕ} {D : FiniteScaleSource n}
    {eta eta2 a lambda c1 c2 : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (R : Finset (Fin n)) (E : Finset (Fin n × Index)) (hE : E ⊆ incidences original)
    (hER : ∀z∈E,z.1∈R)
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
    (vertexCap E (spatialLabel D (2^p)) Q2:ℝ)*lambda*D.thickness^(c1+5*c2)*
      ((64/((2^m:ℕ):ℝ))/(64/((2^p:ℕ):ℝ))) ≤
      mass (shortVertexClosure D a level p m (representative h R a (2^p)) E anchor) (pointWeight E) := by
  let rep := representative h R a (2^p)
  let M := vertexCap E (spatialLabel D (2^p)) Q2
  let W := mass (shortVertexClosure D a level p m rep E anchor) (pointWeight E)
  have hq : (fixedPair D a level p m rep anchor).2∈
      rowCells D a level p m rep E (parentLabel D a (2^p) anchor.1) := by
    apply (mem_rowCells D a level p m rep E _ _).mpr
    exact mem_image_of_mem _ hanchor
  have hrow := queried_short_row_lower h original horiginal ha R E hE F1 F2 G Q1 Q2
    hF1 hG hQ2 hQ1 hGF heta2 hdy hlambda hRich hcost1 hcost2 p m hmp hpL hm6 HF HC
    (parentLabel D a (2^p) anchor.1) (fixedPair D a level p m rep anchor).2 hq
  have hcross := short_closure_weight_cross h original horiginal ha R E hE hER p m hmp hpL hdy Q2 HV anchor
  have hcost := vertex_lift_cost h.1.2.1 h.1.2.2.1 heta2 F2 Q2 (hG.trans_le hGF) hcost2
  have htotal : (M:ℝ)*(lambda*D.thickness^(c1+3*c2)*
      ((64/((2^m:ℕ):ℝ))/(64/((2^p:ℕ):ℝ)))) ≤ D.thickness^(-(2*c2))*W := by
    calc
      _ ≤ (M:ℝ)*(rowChildren D a level p m rep E (parentLabel D a (2^p) anchor.1)
          (fixedPair D a level p m rep anchor).2).card :=
        mul_le_mul_of_nonneg_left hrow (Nat.cast_nonneg M)
      _ ≤ (2401:ℝ)*(Q2:ℝ)^4*W := by exact_mod_cast hcross
      _ ≤ _ := mul_le_mul_of_nonneg_right hcost (Nat.cast_nonneg W)
  have ht := mul_le_mul_of_nonneg_left htotal (Real.rpow_pos_of_pos h.1.2.1 (2*c2)).le
  calc
    _ = D.thickness^(2*c2)*((M:ℝ)*(lambda*D.thickness^(c1+3*c2)*
        ((64/((2^m:ℕ):ℝ))/(64/((2^p:ℕ):ℝ))))) := by
      rw [show c1+5*c2=(c1+3*c2)+2*c2 by ring,Real.rpow_add h.1.2.1]
      ring
    _ ≤ D.thickness^(2*c2)*(D.thickness^(-(2*c2))*W) := ht
    _ = W := by rw [←mul_assoc,←Real.rpow_add h.1.2.1]; simp

end NativeFullVertexFiberDensity
