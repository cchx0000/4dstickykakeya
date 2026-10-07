import Theorems.Thm_StickyKakeya4_native_actual_height_slope_variation

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 7000000
noncomputable section
namespace NativeCoarseHeightSlopeVariation
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeSpatialAngularGeometry
open NativeDirectionRankDichotomy NativeOriginalAngularTupleMenu NativeCompatibleAngularCandidates
open NativeCompatibleNodeDirections NativeCompatiblePlaneVariation NativeActualHeightSlopeVariation
open NativeHorizontalGrainSlice NativeSeparatedSpanControl NativeProjectorCellChart
open NativeHorizontalGraphCoordinates NativeHeightSlopeCoordinates
open scoped BigOperators Matrix.Norms.Elementwise

lemma node_pair_witness {n : ℕ} (D : FiniteScaleSource n) (f : ℕ)
    (P : Finset (Index × List (Fin 3 → ℤ))) (u : Index) (hu : u∈nodes D f (P.image Prod.fst)) :
    ∃p∈P,spatialLabel D (2^f) p.1=u := by
  obtain ⟨k,hk,hku⟩ := mem_image.mp hu
  obtain ⟨p,hp,hpk⟩ := mem_image.mp hk
  refine ⟨p,hp,?_⟩
  rw [hpk]
  exact hku

/-- Same original coarse ancestor transports the prescribed terminal tuple
compatibility to the installed fine-node words. -/
theorem same_ancestor_installed_word {n ell : ℕ} (D : FiniteScaleSource n) (a : ℝ)
    (stop f m : ℕ) (hfs : f ≤ stop) (hmf : m ≤ f)
    (E : Finset (Fin n × Index)) (q : ℝ)
    (P : Finset (Index × List (Fin 3 → ℤ))) (hP : P⊆terminalFamily D a stop E q ell)
    (tuple : Index → Fin ell → (Fin n × Index))
    (Hword : ∀p∈P,angularTuple D a f (List.ofFn (tuple (spatialLabel D (2^f) p.1)))=
      projectWord stop f p.2)
    (HC : ∀p t,p∈P→t∈P→spatialLabel D (2^m) p.1=spatialLabel D (2^m) t.1→
      projectWord stop m p.2=projectWord stop m t.2)
    (u v : Index) (hu : u∈nodes D f (P.image Prod.fst)) (hv : v∈nodes D f (P.image Prod.fst))
    (hancestor : spatialAncestor f m u=spatialAncestor f m v) :
    angularTuple D a m (List.ofFn (tuple u))=angularTuple D a m (List.ofFn (tuple v)) := by
  obtain ⟨p,hp,hpu⟩ := node_pair_witness D f P u hu
  obtain ⟨t,ht,htv⟩ := node_pair_witness D f P v hv
  have hcoarse : spatialLabel D (2^m) p.1=spatialLabel D (2^m) t.1 := by
    rw [←spatialAncestor_label D hmf p.1,←spatialAncestor_label D hmf t.1,hpu,htv]
    exact hancestor
  have hpuword := Hword p hp
  have htvword := Hword t ht
  rw [hpu] at hpuword
  rw [htv] at htvword
  have huword := installed_word_coarsens D a stop f m hfs hmf E q ell p (hP hp)
    (List.ofFn (tuple u)) hpuword
  have hvword := installed_word_coarsens D a stop f m hfs hmf E q ell t (hP ht)
    (List.ofFn (tuple v)) htvword
  exact huword.trans ((HC p t hp ht hcoarse).trans hvword.symm)

/-- A source-facing same-coarse-height endpoint. The height alignment and
terminal compatibility are the actual retained outputs; no metric implication
across dyadic boundaries, plane-gap bound or slope certificate is assumed. -/
theorem same_coarse_height_slope_variation {n ell f : ℕ} {D : FiniteScaleSource n} {eta a q : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (hq : 0 < q) (hell : 0 < ell) (hell4 : ell ≤ 4)
    (stop m : ℕ) (hfs : f ≤ stop) (hmf : m ≤ f)
    (E : Finset (Fin n × Index)) (P : Finset (Index × List (Fin 3 → ℤ)))
    (hP : P⊆terminalFamily D a stop E q ell)
    {point : Index → Index} {tuple : Index → Fin ell → (Fin n × Index)}
    {anchor : Index → Fin ell → Fin n}
    (H : IsNodeDirectionSystem D a f E (P.image Prod.fst) q ell point tuple anchor)
    (Hword : ∀p∈P,angularTuple D a f (List.ofFn (tuple (spatialLabel D (2^f) p.1)))=
      projectWord stop f p.2)
    (HC : ∀p t,p∈P→t∈P→spatialLabel D (2^m) p.1=spatialLabel D (2^m) t.1→
      projectWord stop m p.2=projectWord stop m t.2)
    (B : Finset Index) (hB : B⊆nodes D f (P.image Prod.fst))
    (Hfine : ∀u v,u∈B→v∈B→u (3:Fin 4)=v (3:Fin 4)→u=v)
    (Hcoarse : ∀u v,u∈B→v∈B→spatialAncestor f m u (3:Fin 4)=spatialAncestor f m v (3:Fin 4)→
      spatialAncestor f m u=spatialAncestor f m v)
    (P0 : Submodule ℝ E4) (hP0 : P0≤heightKernel) (hd0 : Module.finrank ℝ P0=ell-1)
    (u v : Index) (hu : u∈B) (hv : v∈B)
    (hcellu : cell P0=cell (horizontalPlane D tuple u)) (hcellv : cell P0=cell (horizontalPlane D tuple v))
    (hheight : spatialAncestor f m u (3:Fin 4)=spatialAncestor f m v (3:Fin 4)) :
    let plane := horizontalPlane D tuple
    let hplane : ∀u∈B,plane u≤heightKernel := fun u _ => horizontalPlane_le D tuple u
    let F := heightSlope B f P0 hP0 ell hell hell4 hd0 plane hplane
    ‖F (u (3:Fin 4))-F (v (3:Fin 4))‖ ≤ (72/((2^m:ℕ):ℝ))*coefficientCost 2 q ell := by
  have hword := same_ancestor_installed_word D a stop f m hfs hmf E q P hP tuple Hword HC
    u v (hB hu) (hB hv) (Hcoarse u v hu hv hheight)
  exact matching_height_slope_variation h hq hell hell4 H B hB Hfine P0 hP0 hd0 m u v hu hv
    hcellu hcellv hword

end NativeCoarseHeightSlopeVariation
