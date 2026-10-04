import Theorems.Thm_StickyKakeya4_native_coarse_pruning_budget
import Theorems.Thm_StickyKakeya4_native_coarse_representative_geometry
import Theorems.Thm_StickyKakeya4_native_coarse_dyadic_shading
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2800000
noncomputable section
namespace NativeCoarseShadingPruning
open Classical Finset MeasureTheory StickyKakeya4 NativeOriginalParentSelection NativeCommonCubicalMesh
open NativeUnitParentNormalization NativeCoarseShadingCapacity NativeCoarseRepresentativeGeometry
open NativeCoarseDyadicShading NativeCoarsePruningBudget NativeDyadicParentCells
open scoped BigOperators ENNReal

def weight {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (level m : ℕ)
    (rep : Parent → Fin n) (E : Finset (Fin n × Index)) (p : Parent) : ℝ :=
  (volume (wzCellShading (32/((2^m:ℕ):ℝ))
    (fun _ : Fin 1 => rows D a (2^m) (block level m) rep E p) 0)).toReal

lemma coarse_thickness_le_one (m : ℕ) (h6 : 6  ≤  m) : 64/((2^m:ℕ):ℝ) ≤ 1 := by
  apply (div_le_iff₀ (by positivity : (0:ℝ)<((2^m:ℕ):ℝ))).mpr
  norm_num only [one_mul,Nat.cast_pow,Nat.cast_ofNat]
  calc
    (64:ℝ) = (2:ℝ)^6 := by norm_num
    _  ≤  _ := pow_le_pow_right₀ (by norm_num) h6

/-- Actual per-coarse-tube shading upper mass follows from the constructed
front-meeting cubes and the genuine marked unit-tube volume formula. -/
theorem actual_weight_upper {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i) ∈ Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (level m : ℕ) (hdy : D.thickness=(2:ℝ)⁻¹^level) (hm : m ≤ level) (h6 : 6  ≤  m)
    (rep : Parent → Fin n) (E : Finset (Fin n × Index)) (hE : ∀e∈E,e.2∈original e.1)
    (p : Parent) :
    weight D a level m rep E p  ≤  NativeOriginalPrunedMass.volumeConstant*(64/((2^m:ℕ):ℝ))^3 := by
  have hs := projected_shading_subset_tube h original horiginal ha (2^m) (block level m)
    (block_pos level m) rep E hE p
  rw [block_mesh hdy hm,block_thickness hdy hm] at hs
  have hv := (zero_parent_valid_slab h a (rep p)).1
  have ht := volume_markedUnitTube_upper_bound hv
    (by positivity : 0 < 64/((2^m:ℕ):ℝ)) (coarse_thickness_le_one m h6)
  have hh := (measure_mono hs).trans ht
  have hf : 32*(ENNReal.ofReal (64/((2^m:ℕ):ℝ)))^3*ENNReal.ofReal (Real.pi^2/2)≠⊤ := by finiteness
  have hr := ENNReal.toReal_mono hf hh
  simp only [ENNReal.toReal_mul,ENNReal.toReal_pow,ENNReal.toReal_ofNat,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ 64/((2^m:ℕ):ℝ)),
    ENNReal.toReal_ofReal (by positivity : 0 ≤ Real.pi^2/2)] at hr
  exact hr.trans_eq (by dsimp [NativeOriginalPrunedMass.volumeConstant]; ring)

/-- The rho^3 tube-volume upper bound cancels the rho^-3 deletion count.
The only remaining deletion cost is a fixed constant, the number of dyadic
levels, and the chosen EXTRA ORIGINAL-delta power. -/
theorem actual_shading_pruning {n : ℕ} {D : FiniteScaleSource n} {eta zeta a t : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i) ∈ Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (R : Finset (Fin n)) (level m : ℕ) (hdy : D.thickness=(2:ℝ)⁻¹^level)
    (hm : m ≤ level) (h6 : 6  ≤  m)
    (H : ∀ell : Fin (m+1),∀p : Parent,
      (R.filter (fun i => parentLabel D a (2^ell.val) i=p)).Nonempty →
        D.thickness^zeta*((1/((2^ell.val:ℕ):ℝ))/D.thickness)^3  ≤
          ((R.filter (fun i => parentLabel D a (2^ell.val) i=p)).card:ℝ))
    (Q : Finset Parent) (hQ : Q⊆R.image (parentLabel D a (2^m)))
    (rep : Parent → Fin n) (E : Finset (Fin n × Index)) (hE : ∀e∈E,e.2∈original e.1) :
    ∃S⊆Q,
      (∑p∈Q,weight D a level m rep E p)  ≤  (∑p∈S,weight D a level m rep E p)+
        (746496*64^3*NativeOriginalPrunedMass.volumeConstant)*(m+1)*D.thickness^(t-zeta) ∧
      ∀ell : Fin (m+1),∀p : Parent,
        (S.filter (fun q => ancestor m ell.val q=p)).Nonempty →
          D.thickness^t*(((2^m:ℕ):ℝ)/((2^ell.val:ℕ):ℝ))^3  ≤
            ((S.filter (fun q => ancestor m ell.val q=p)).card:ℝ) := by
  let U := NativeOriginalPrunedMass.volumeConstant*(64/((2^m:ℕ):ℝ))^3
  have hU : 0 ≤ U := mul_nonneg NativeOriginalPrunedMass.volumeConstant_pos.le (by positivity)
  obtain ⟨S,hSQ,hshade,hterminal⟩ := weighted_pruning_power_budget h R m H Q hQ
    (weight D a level m rep E) hU
    (fun p _hp => actual_weight_upper h original horiginal ha level m hdy hm h6 rep E hE p)
  refine ⟨S,hSQ,?_,hterminal⟩
  convert hshade using 1
  dsimp [U]
  field_simp

end NativeCoarseShadingPruning
