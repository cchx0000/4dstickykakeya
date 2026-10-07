import Theorems.Thm_StickyKakeya4_native_history_grain_cleanup
import Theorems.Thm_StickyKakeya4_native_dense_phase_parent_retention
import Theorems.Thm_StickyKakeya4_native_raw_shadow_pair_comparison

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 6500000

noncomputable section
namespace NativeParentGrainIncidenceCleanup
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeOriginalParentDensityCore NativeSpatialAngularGeometry NativeSquaredGrainQueries
open NativeActualProjectedGrainCount NativeQueriedVertexWeights NativeOriginalPacketReference
open RichDirectionalLayers WeightedRichDirectionalLayers NativeAutomaticWeightedGrainCore
open NativeHistoryGrainCleanup
open scoped BigOperators

/-- Cut literal original incidences by their original point membership. -/
def cutEdges {n : ℕ} (E : Finset (Fin n × Index)) (K : Finset Index) : Finset (Fin n × Index) :=
  E.filter (fun z => z.2∈K)

/-- Parent and grain use exactly the same raw spatial-node depth. -/
def mixedLabel {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m : ℕ)
    (P : Index → Submodule ℝ E4) (ell : ℕ) (z : Fin n × Index) : Parent × (Index × Index) :=
  (parentLabel D a (2^m) z.1,taggedLabel D m P ell z.2)

def mixedFiber {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m : ℕ)
    (P : Index → Submodule ℝ E4) (ell : ℕ) (E : Finset (Fin n × Index))
    (c : Parent × (Index × Index)) : Finset (Fin n × Index) :=
  classFiber E (mixedLabel D a m P ell) c

/-- These are raw physical vertices, not projected shadow cells. -/
def mixedVertices {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m f : ℕ)
    (P : Index → Submodule ℝ E4) (ell : ℕ) (E : Finset (Fin n × Index))
    (c : Parent × (Index × Index)) : Finset Index :=
  (mixedFiber D a m P ell E c).image (fun z => spatialLabel D (2^f) z.2)

lemma cutEdges_subset {n : ℕ} (E : Finset (Fin n × Index)) (K : Finset Index) :
    cutEdges E K⊆E := filter_subset _ _

lemma cutEdges_card {n : ℕ} (E : Finset (Fin n × Index)) (K : Finset Index) :
    (cutEdges E K).card=mass K (pointWeight E) := (mass_pointWeight E K).symm

lemma cutEdges_points {n : ℕ} (E : Finset (Fin n × Index)) (K : Finset Index)
    (hK : K⊆E.image Prod.snd) : (cutEdges E K).image Prod.snd=K := by
  ext k
  simp only [cutEdges,mem_image,mem_filter]
  constructor
  · rintro ⟨z,⟨_hz,hzk⟩,rfl⟩
    exact hzk
  · intro hk
    obtain ⟨z,hz,rfl⟩ := mem_image.mp (hK hk)
    exact ⟨z,⟨hz,hk⟩,rfl⟩

lemma cutEdges_grain_image {n : ℕ} (D : FiniteScaleSource n) (m : ℕ)
    (P : Index → Submodule ℝ E4) (ell : ℕ) (E : Finset (Fin n × Index))
    (K : Finset Index) (hK : K⊆E.image Prod.snd) :
    (cutEdges E K).image (fun z => taggedLabel D m P ell z.2)=K.image (taggedLabel D m P ell) := by
  calc
    _ = ((cutEdges E K).image Prod.snd).image (taggedLabel D m P ell) := by rw [image_image]; rfl
    _ = _ := by rw [cutEdges_points E K hK]

/-- Restricting to the chosen parent leaves each of its mixed fibers exactly intact. -/
lemma parent_mixed_fiber_eq {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m : ℕ)
    (P : Index → Submodule ℝ E4) (ell : ℕ) (E : Finset (Fin n × Index))
    (p : Parent) (c : Index × Index) :
    mixedFiber D a m P ell (parentEdges D a (2^m) E p) (p,c)=
      mixedFiber D a m P ell E (p,c) := by
  ext z
  simp only [mixedFiber,classFiber,parentEdges,mixedLabel,mem_filter,Prod.mk.injEq]
  tauto

lemma mixed_fiber_geometry {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m : ℕ)
    (P : Index → Submodule ℝ E4) (ell : ℕ) (E : Finset (Fin n × Index))
    (c : Parent × (Index × Index)) (x y : Fin n × Index)
    (hx : x∈mixedFiber D a m P ell E c) (hy : y∈mixedFiber D a m P ell E c) :
    x∈E ∧ y∈E ∧ parentLabel D a (2^m) x.1=parentLabel D a (2^m) y.1 ∧
      spatialLabel D (2^m) x.2=spatialLabel D (2^m) y.2 ∧
      Metric.infDist (rawVertex D (phaseDepth m) x.2-rawVertex D (phaseDepth m) y.2)
        (P (spatialLabel D (2^m) x.2):Set E4) ≤ 2*grainWidth m ell := by
  simp only [mixedFiber,classFiber,mem_filter] at hx hy
  obtain ⟨hxE,hxc⟩ := hx
  obtain ⟨hyE,hyc⟩ := hy
  have he := hxc.trans hyc.symm
  have hp := congrArg Prod.fst he
  have hg := tagged_same_label_near D m P ell x.2 y.2 (congrArg Prod.snd he)
  exact ⟨hxE,hyE,hp,hg⟩

/-- A bound on actual parents over each raw node controls the actual mixed image. -/
theorem mixed_label_count {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m : ℕ)
    (P : Index → Submodule ℝ E4) (ell : ℕ) (E : Finset (Fin n × Index))
    (K : Finset Index) (hK : K⊆E.image Prod.snd) (B : ℝ)
    (HB : ∀S⊆E,∀node : Index,(∀z∈S,spatialLabel D (2^m) z.2=node) →
      ((S.image (fun z => parentLabel D a (2^m) z.1)).card:ℝ) ≤ B) :
    (((cutEdges E K).image (mixedLabel D a m P ell)).card:ℝ) ≤
      B*(K.image (taggedLabel D m P ell)).card := by
  have Hfiber : ∀c∈(cutEdges E K).image (fun z => taggedLabel D m P ell z.2),
      ((((cutEdges E K).filter (fun z => taggedLabel D m P ell z.2=c)).image
        (mixedLabel D a m P ell)).card:ℝ) ≤ B := by
    intro c _hc
    let S := (cutEdges E K).filter (fun z => taggedLabel D m P ell z.2=c)
    have hSE : S⊆E := (filter_subset _ _).trans (cutEdges_subset E K)
    have hnode : ∀z∈S,spatialLabel D (2^m) z.2=c.1 := by
      intro z hz
      exact congrArg Prod.fst (mem_filter.mp hz).2
    have he : S.image (mixedLabel D a m P ell)=
        (S.image (fun z => parentLabel D a (2^m) z.1)).image (fun p => (p,c)) := by
      rw [image_image]
      apply image_congr
      intro z hz
      exact Prod.ext rfl (mem_filter.mp hz).2
    change ((S.image (mixedLabel D a m P ell)).card:ℝ) ≤ B
    rw [he,card_image_of_injective _ (fun _ _ hh => congrArg Prod.fst hh)]
    exact HB S hSE c.1 hnode
  have hh := NativeTangentGridCoarsening.image_card_le_real_mul_of_fiber_images
    (cutEdges E K) (mixedLabel D a m P ell) (fun z => taggedLabel D m P ell z.2) B Hfiber
  rwa [cutEdges_grain_image D m P ell E K hK] at hh

/-- The genuine parent/vertex cap bounds the original incidence cardinality
of each retained mixed fiber, on the literal raw spatial vertices. -/
theorem mixed_fiber_vertex_cap {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m f : ℕ)
    (P : Index → Submodule ℝ E4) (ell : ℕ) (E H : Finset (Fin n × Index)) (hHE : H⊆E)
    (c : Parent × (Index × Index)) (C : ℝ)
    (HC : ∀v : Index,((E.filter (fun z => parentLabel D a (2^m) z.1=c.1 ∧
      spatialLabel D (2^f) z.2=v)).card:ℝ) ≤ C) :
    ((mixedFiber D a m P ell H c).card:ℝ) ≤ C*(mixedVertices D a m f P ell H c).card := by
  have Hfiber : ∀v∈(mixedFiber D a m P ell H c).image (fun z => spatialLabel D (2^f) z.2),
      ((((mixedFiber D a m P ell H c).filter (fun z => spatialLabel D (2^f) z.2=v)).image id).card:ℝ) ≤ C := by
    intro v _hv
    rw [image_id]
    apply le_trans (Nat.cast_le.mpr (card_le_card (show
      (mixedFiber D a m P ell H c).filter (fun z => spatialLabel D (2^f) z.2=v) ⊆
        E.filter (fun z => parentLabel D a (2^m) z.1=c.1 ∧ spatialLabel D (2^f) z.2=v) from ?_))) (HC v)
    intro z hz
    obtain ⟨hzF,hzv⟩ := mem_filter.mp hz
    simp only [mixedFiber,classFiber,mem_filter] at hzF
    obtain ⟨hzH,hzc⟩ := hzF
    exact mem_filter.mpr ⟨hHE hzH,congrArg Prod.fst hzc,hzv⟩
  have hh := NativeTangentGridCoarsening.image_card_le_real_mul_of_fiber_images
    (mixedFiber D a m P ell H c) id (fun z => spatialLabel D (2^f) z.2) C Hfiber
  simpa only [image_id,mixedVertices] using hh

/-- Compute the actual mixed-label cleanup from unit original-edge weights.
No mixed-class count or final dense-core existence is assumed. -/
theorem exists_mixed_dense_core {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m : ℕ)
    (P : Index → Submodule ℝ E4) (ell : ℕ) (E : Finset (Fin n × Index))
    (K : Finset Index) (hK : K⊆E.image Prod.snd) (hKn : K.Nonempty) :
    ∃H⊆cutEdges E K,H.Nonempty ∧ (cutEdges E K).card ≤ 2*H.card ∧
      ∀x∈H,
        threshold (cutEdges E K).card 1 ((cutEdges E K).image (mixedLabel D a m P ell)).card ≤
          (mixedFiber D a m P ell H (mixedLabel D a m P ell x)).card ∧
        ((cutEdges E K).card:ℝ)/(2*((((cutEdges E K).image (mixedLabel D a m P ell)).card):ℝ)) <
          ((mixedFiber D a m P ell H (mixedLabel D a m P ell x)).card:ℝ) := by
  have hJ : (cutEdges E K).Nonempty := by
    have hh : ((cutEdges E K).image Prod.snd).Nonempty := by rwa [cutEdges_points E K hK]
    exact hh.of_image
  have hunit (S : Finset (Fin n × Index)) : mass S (fun _ => 1)=S.card := by simp [mass]
  have hpos : 0 < mass (cutEdges E K) (fun _ => 1) := by rw [hunit]; exact card_pos.mpr hJ
  obtain ⟨H,hHJ,hHn,hhalf,_hloss,hmin⟩ :=
    exists_automatic_simultaneous_dense_core (β:=fun _ : Fin 1 => Parent × (Index × Index))
      (by norm_num) (cutEdges E K) (fun _ => mixedLabel D a m P ell) (fun _ => 1) hpos
  refine ⟨H,hHJ,hHn,by simpa only [hunit] using hhalf,?_⟩
  intro x hx
  have hm := hmin (0:Fin 1) (mixedLabel D a m P ell x) (by
    simp only [mem_image]
    exact ⟨x,hx,rfl⟩)
  simpa only [hunit,classical_image_eq,Nat.cast_one,mul_one,mixedFiber] using hm

/-- Only after cleanup, choose a parent that retains its paid share. Its
mixed fibers are exactly the previously cleaned mixed fibers. -/
theorem exists_cleaned_parent {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m : ℕ)
    (P : Index → Submodule ℝ E4) (ell : ℕ) (E : Finset (Fin n × Index))
    (K : Finset Index) (hK : K⊆E.image Prod.snd) (hKn : K.Nonempty) :
    ∃H⊆cutEdges E K,H.Nonempty ∧ (cutEdges E K).card ≤ 2*H.card ∧
      ∃p : Parent,(parentEdges D a (2^m) H p).Nonempty ∧
        ((parentEdges D a (2^m) (cutEdges E K) p).card:ℝ) ≤ 2*(parentEdges D a (2^m) H p).card ∧
        ∀x∈parentEdges D a (2^m) H p,
          ((cutEdges E K).card:ℝ)/(2*((((cutEdges E K).image (mixedLabel D a m P ell)).card):ℝ)) <
            ((mixedFiber D a m P ell (parentEdges D a (2^m) H p)
              (mixedLabel D a m P ell x)).card:ℝ) := by
  obtain ⟨H,hHJ,hHn,hhalf,hmin⟩ := exists_mixed_dense_core D a m P ell E K hK hKn
  have hJn : (cutEdges E K).Nonempty := hHn.mono hHJ
  obtain ⟨p,_hp,_hJp,hHp,hret⟩ := NativeDensePhaseParentRetention.exists_retained_fiber
    (cutEdges E K) H hHJ hJn (fun z => parentLabel D a (2^m) z.1) 1 2 (by norm_num)
      (by simpa only [one_mul] using (show ((cutEdges E K).card:ℝ) ≤ 2*(H.card:ℝ) by exact_mod_cast hhalf))
  refine ⟨H,hHJ,hHn,hhalf,p,hHp,by simpa only [one_mul,parentEdges] using hret,?_⟩
  intro x hx
  have hxH := (mem_filter.mp hx).1
  have hxp := (mem_filter.mp hx).2
  have he : mixedLabel D a m P ell x=(p,taggedLabel D m P ell x.2) := Prod.ext hxp rfl
  rw [he,parent_mixed_fiber_eq]
  simpa only [he] using (hmin x hxH).2

end NativeParentGrainIncidenceCleanup
