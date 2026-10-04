import Theorems.Thm_StickyKakeya4_native_coarse_representative_geometry
import Theorems.Thm_StickyKakeya4_native_coarse_dyadic_shading
import Theorems.Thm_StickyKakeya4_native_coarse_direction_thinning
import Theorems.Thm_StickyKakeya4_native_padded_cell_source
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000
noncomputable section
namespace NativeCoarseCellSource
open Classical Finset MeasureTheory StickyKakeya4 NativeOriginalParentSelection NativeCommonCubicalMesh
open NativeUnitParentNormalization NativeCoarseShadingCapacity NativeCoarseRepresentativeGeometry
open NativeCoarseDyadicShading
open scoped BigOperators ENNReal

/-- Enumeration retains the selected ORIGINAL full-parameter cell labels. -/
def parentIndex (Q : Finset Parent) (i : Fin Q.card) : Parent := (Q.equivFin.symm i).val
lemma parentIndex_mem (Q : Finset Parent) (i : Fin Q.card) : parentIndex Q i∈Q :=
  (Q.equivFin.symm i).property
lemma parentIndex_injective (Q : Finset Parent) : Function.Injective (parentIndex Q) := by
  intro i j hij
  exact Q.equivFin.symm.injective (Subtype.ext hij)
lemma parentIndex_range (Q : Finset Parent) : Set.range (parentIndex Q)=(Q:Set Parent) := by
  ext p
  constructor
  · rintro ⟨i,rfl⟩
    exact parentIndex_mem Q i
  · intro hp
    exact ⟨Q.equivFin ⟨p,hp⟩,by simp [parentIndex]⟩

/-- A genuine coarse finite source on ACTUAL original representative lines
and their front-meeting cube images. Separation is supplied by the proved
residue/rank color, or inherited by any later retained subset of that color. -/
def source {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (a : ℝ) (level m : ℕ)
    (Q : Finset Parent) (rep : Parent → Fin n) (E : Finset (Fin n × Index))
    (hsep : ∀p∈Q,∀q∈Q,p≠q → 64/((2^m:ℕ):ℝ) ≤ dist (direction (D.line (rep p))) (direction (D.line (rep q)))) :
    FiniteScaleSource Q.card :=
  directionSeparatedWZCellSourceAtScales (64/((2^m:ℕ):ℝ)) (32/((2^m:ℕ):ℝ))
    (fun i => NativeContractedUnitParent.line D a (0,0) (rep (parentIndex Q i)))
    (fun i => rows D a (2^m) (block level m) rep E (parentIndex Q i))
    (by positivity)
    (by
      intro i j hij
      rw [direction_zero_parent h a,direction_zero_parent h a]
      exact hsep _ (parentIndex_mem Q i) _ (parentIndex_mem Q j)
        (fun he => hij (parentIndex_injective Q he)))

lemma source_thickness {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (a : ℝ) (level m : ℕ)
    (Q : Finset Parent) (rep : Parent → Fin n) (E : Finset (Fin n × Index))
    (hsep : ∀p∈Q,∀q∈Q,p≠q → 64/((2^m:ℕ):ℝ) ≤ dist (direction (D.line (rep p))) (direction (D.line (rep q)))) :
    (source h a level m Q rep E hsep).thickness=64/((2^m:ℕ):ℝ) := rfl

lemma source_line {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (a : ℝ) (level m : ℕ)
    (Q : Finset Parent) (rep : Parent → Fin n) (E : Finset (Fin n × Index))
    (hsep : ∀p∈Q,∀q∈Q,p≠q → 64/((2^m:ℕ):ℝ) ≤ dist (direction (D.line (rep p))) (direction (D.line (rep q))))
    (i : Fin Q.card) :
    (source h a level m Q rep E hsep).line i=NativeContractedUnitParent.line D a (0,0) (rep (parentIndex Q i)) := rfl

lemma source_shading {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (a : ℝ) (level m : ℕ)
    (Q : Finset Parent) (rep : Parent → Fin n) (E : Finset (Fin n × Index))
    (hsep : ∀p∈Q,∀q∈Q,p≠q → 64/((2^m:ℕ):ℝ) ≤ dist (direction (D.line (rep p))) (direction (D.line (rep q))))
    (i : Fin Q.card) :
    (source h a level m Q rep E hsep).shading i=
      wzCellShading (32/((2^m:ℕ):ℝ))
        (fun _ : Fin 1 => rows D a (2^m) (block level m) rep E (parentIndex Q i)) 0 := rfl

/-- Geometric native fields are all constructed on one literal coarse source.
AD, CW and the power density are separate consequences, not fields hidden in
this constructor. The input compact set and output compact set are the same K0. -/
theorem source_geometric_fields {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (hK : ∀i,D.line i∈fixedCompactClass)
    (original : Fin n → Finset Index) (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i) ∈ Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (level m : ℕ) (hdy : D.thickness=(2:ℝ)⁻¹^level) (hm : m ≤ level) (h6 : 6  ≤  m)
    (Q : Finset Parent) (rep : Parent → Fin n) (E : Finset (Fin n × Index))
    (hE : ∀e∈E,e.2∈original e.1)
    (hsep : ∀p∈Q,∀q∈Q,p≠q → 64/((2^m:ℕ):ℝ) ≤ dist (direction (D.line (rep p))) (direction (D.line (rep q)))) :
    let S := source h a level m Q rep E hsep
    0 < S.thickness ∧ S.thickness ≤ 1 ∧ IsWZDyadicScale S.thickness ∧
      (∀i,IsValidLine (S.line i)) ∧ (∀i,S.line i∈fixedCompactClass) ∧
      (∀i,S.weight i=1) ∧ (∀i,MeasurableSet (S.shading i)) ∧
      (∀i,IsWZComparableCubicalShading S.thickness (S.shading i)) ∧
      (∀i,S.shading i⊆markedUnitTube (S.line i) S.thickness) ∧
      (∀i j,i≠j → S.thickness ≤ dist (direction (S.line i)) (direction (S.line j))) ∧
      HasNormalizedWZGraphSlab S ∧ HasFixedWZGraphNormalization S := by
  let S := source h a level m Q rep E hsep
  have htd : IsWZDyadicScale S.thickness := by
    have hh := block_thickness_dyadic hdy hm h6
    rwa [block_thickness hdy hm] at hh
  have hmd : IsWZDyadicScale (32/((2^m:ℕ):ℝ)) := by
    have hh := NativePaddedCellSource.dyadic_div_power htd 1
    change IsWZDyadicScale ((64/((2^m:ℕ):ℝ))/(2:ℝ)^1) at hh
    convert hh using 1
    ring
  have hline (i : Fin Q.card) := zero_parent_valid_slab h a (rep (parentIndex Q i))
  have hvalid : ∀i,IsValidLine (S.line i) := fun i => (hline i).1
  have hslab : HasNormalizedWZGraphSlab S := by
    refine ⟨fun i => (hline i).2.1,-(1/4:ℝ),(1/4:ℝ),by norm_num,?_,fun i => (hline i).2.2⟩
    exact Set.nonempty_Icc.mpr (by norm_num)
  refine ⟨by change 0<64/((2^m:ℕ):ℝ); positivity,?_,htd,hvalid,?_,?_,?_,?_,?_,?_,hslab,
    hasFixedWZGraphNormalization_of_normalizedSlab S hvalid hslab⟩
  · change 64/((2^m:ℕ):ℝ) ≤ 1
    apply (div_le_iff₀ (by positivity : (0:ℝ)<((2^m:ℕ):ℝ))).mpr
    norm_num only [one_mul,Nat.cast_pow,Nat.cast_ofNat]
    exact (by norm_num : (64:ℝ)=(2:ℝ)^6) ▸ pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) h6
  · intro i
    exact zero_parent_mem_fixedCompactClass h hK ha (rep (parentIndex Q i))
  · intro i
    rfl
  · intro i
    exact measurableSet_wzCellShading _ (fun _ : Fin 1 => rows D a (2^m) (block level m) rep E (parentIndex Q i)) 0
  · intro i
    refine ⟨32/((2^m:ℕ):ℝ),by positivity,?_,?_,hmd,?_⟩
    · change 32/((2^m:ℕ):ℝ) ≤ 64/((2^m:ℕ):ℝ)
      gcongr
      norm_num
    · change 64/((2^m:ℕ):ℝ) ≤ 2*(32/((2^m:ℕ):ℝ))
      exact le_of_eq (by ring)
    · exact isWZCubicalShading_wzCellShading _
        (fun _ : Fin 1 => rows D a (2^m) (block level m) rep E (parentIndex Q i)) 0
  · intro i
    have hh := projected_shading_subset_tube h original horiginal ha (2^m) (block level m)
      (block_pos level m) rep E hE (parentIndex Q i)
    rwa [block_mesh hdy hm,block_thickness hdy hm] at hh
  · intro i j hij
    change 64/((2^m:ℕ):ℝ) ≤ dist (direction (NativeContractedUnitParent.line D a (0,0) (rep (parentIndex Q i))))
      (direction (NativeContractedUnitParent.line D a (0,0) (rep (parentIndex Q j))))
    rw [direction_zero_parent h a,direction_zero_parent h a]
    exact hsep _ (parentIndex_mem Q i) _ (parentIndex_mem Q j)
      (fun he => hij (parentIndex_injective Q he))

end NativeCoarseCellSource
