import Theorems.Thm_StickyKakeya4_native_coarse_carrier_geometry
import Theorems.Thm_StickyKakeya4_native_coarse_cw_transfer
import Theorems.Thm_StickyKakeya4_native_coarse_shading_pruning
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 3400000
noncomputable section
namespace NativeCoarseSourceProfiles
open Classical Finset MeasureTheory StickyKakeya4 NativeOriginalParentSelection NativeCommonCubicalMesh
open NativeUnitParentNormalization NativeCoarseCellSource NativeCoarseRepresentativeGeometry
open NativeCoarseCarrierGeometry NativeCoarseShadingPruning NativeOriginalSlopeCubePacking NativeUnitParentDirections
open scoped BigOperators ENNReal

lemma sum_parentIndex {M : Type*} [AddCommMonoid M] (Q : Finset Parent) (f : Parent → M) :
    (∑i : Fin Q.card,f (parentIndex Q i))=∑p∈Q,f p := by
  have hh := Q.equivFin.symm.sum_comp (fun p : Q => f p.val)
  simpa only [parentIndex,Finset.sum_coe_sort] using hh

lemma card_filter_parentIndex (Q : Finset Parent) (P : Parent → Prop) [DecidablePred P] :
    ((univ:Finset (Fin Q.card)).filter (fun i => P (parentIndex Q i))).card=(Q.filter P).card := by
  simpa only [Finset.card_filter] using sum_parentIndex (M:=ℕ) Q (fun p => if P p then 1 else 0)

variable {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
variable (h : IsWangZakharovNativeFiniteInput D eta) (level m : ℕ)
variable (Q : Finset Parent) (rep : Parent → Fin n) (E : Finset (Fin n × Index))
variable (hsep : ∀p∈Q,∀q∈Q,p≠q → 64/((2^m:ℕ):ℝ) ≤ dist (direction (D.line (rep p))) (direction (D.line (rep q))))

lemma source_carrier_count (i : Fin Q.card) (r : ℝ) :
    wzCarrierBallCount (source h a level m Q rep E hsep) i r=
      (Q.filter (fun p => dist (carrier D a (rep p)) (carrier D a (rep (parentIndex Q i))) ≤ r)).card := by
  exact card_filter_parentIndex Q (fun p => dist (carrier D a (rep p))
    (carrier D a (rep (parentIndex Q i))) ≤ r)

lemma source_contained_count (U : Set E4) :
    wzContainedTubeCount (source h a level m Q rep E hsep) U=
      (Q.filter (fun p => markedUnitTube (NativeContractedUnitParent.line D a (0,0) (rep p))
        (64/((2^m:ℕ):ℝ))⊆U)).card := by
  exact card_filter_parentIndex Q (fun p => markedUnitTube
    (NativeContractedUnitParent.line D a (0,0) (rep p)) (64/((2^m:ℕ):ℝ))⊆U)

lemma source_shading_sum :
    (∑i : Fin Q.card,(volume ((source h a level m Q rep E hsep).shading i)).toReal)=
      ∑p∈Q,weight D a level m rep E p := by
  exact sum_parentIndex Q (weight D a level m rep E)

/-- Literal direction packing gives the upper ball estimate for this actual
coarse source before any complete native input predicate has been asserted. -/
theorem source_carrier_upper (i : Fin Q.card) {r : ℝ}
    (hr : (source h a level m Q rep E hsep).thickness ≤ r) :
    (wzCarrierBallCount (source h a level m Q rep E hsep) i r:ℝ) ≤
      10077696*(r/(source h a level m Q rep E hsep).thickness)^3 := by
  let S := source h a level m Q rep E hsep
  let A := (univ:Finset (Fin Q.card)).filter (fun j => dist (wzCarrierPoint S j) (wzCarrierPoint S i) ≤ r)
  have hd : 0 < S.thickness := by change 0 < 64/((2^m:ℕ):ℝ); positivity
  have hrp := hd.trans_le hr
  have hg (j : Fin Q.card) : IsValidLine (S.line j) ∧ (1/2:ℝ) ≤ direction (S.line j) (3:Fin 4) := by
    have hh := zero_parent_valid_slab h a (rep (parentIndex Q j))
    exact ⟨hh.1,hh.2.1⟩
  have hs (j k : Fin Q.card) (hne : j≠k) : S.thickness ≤ dist (direction (S.line j)) (direction (S.line k)) := by
    change 64/((2^m:ℕ):ℝ) ≤ dist (direction (NativeContractedUnitParent.line D a (0,0) (rep (parentIndex Q j))))
      (direction (NativeContractedUnitParent.line D a (0,0) (rep (parentIndex Q k))))
    rw [direction_zero_parent h a,direction_zero_parent h a]
    exact hsep _ (parentIndex_mem Q j) _ (parentIndex_mem Q k) (fun he => hne (parentIndex_injective Q he))
  have hbox (j : Fin Q.card) (hj : j∈A) (k : Fin 3) :
      NativeOriginalCellChartGeometry.slope (S.line i) k-6*r ≤ NativeOriginalCellChartGeometry.slope (S.line j) k ∧
        NativeOriginalCellChartGeometry.slope (S.line j) k ≤ (NativeOriginalCellChartGeometry.slope (S.line i) k-6*r)+12*r := by
    have hdir : dist (direction (S.line j)) (direction (S.line i)) ≤ r :=
      (show dist (direction (S.line j)) (direction (S.line i)) ≤ dist (wzCarrierPoint S j) (wzCarrierPoint S i)
        from le_max_left _ _).trans (mem_filter.mp hj).2
    have hh := (slope_sub_le_direction_dist (S.line j) (S.line i) (hg i).1 (hg j).2 (hg i).2 k).trans
      (mul_le_mul_of_nonneg_left hdir (by norm_num : (0:ℝ) ≤ 6))
    obtain ⟨hlo,hhi⟩ := abs_le.mp hh
    constructor <;> linarith
  have hh := original_cube_card_le_ratio A S.line hd (show S.thickness ≤ 12*r by linarith)
    (fun j _hj => (hg j).1) (fun j _hj => (hg j).2) (fun j _hj k _hk hne => hs j k hne)
    (fun k => NativeOriginalCellChartGeometry.slope (S.line i) k-6*r) hbox
  change (A.card:ℝ) ≤ 10077696*(r/S.thickness)^3
  exact hh.trans_eq (by ring)

/-- The constructed source's native carrier count consumes the proved
pruned ancestor law on the same actual original representative labels. -/
theorem source_carrier_lower (hK : ∀i,D.line i∈fixedCompactClass)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i) ∈ Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (hrep : ∀p∈Q,parentLabel D a (2^m) (rep p)=p) {t : ℝ}
    (H : ∀ell : Fin (m+1),∀p : Parent,
      (Q.filter (fun q => NativeDyadicParentCells.ancestor m ell.val q=p)).Nonempty →
        D.thickness^t*(((2^m:ℕ):ℝ)/((2^ell.val:ℕ):ℝ))^3 ≤
          ((Q.filter (fun q => NativeDyadicParentCells.ancestor m ell.val q=p)).card:ℝ))
    (i : Fin Q.card) {r : ℝ} (hr : (source h a level m Q rep E hsep).thickness ≤ r) (hr1 : r ≤ 1) :
    D.thickness^t*(r/(source h a level m Q rep E hsep).thickness)^3 ≤
      (wzCarrierBallCount (source h a level m Q rep E hsep) i r:ℝ) := by
  rw [source_carrier_count]
  exact pruned_carrier_lower h hK ha m Q rep hrep H (parentIndex Q i) (parentIndex_mem Q i) hr hr1

end NativeCoarseSourceProfiles
