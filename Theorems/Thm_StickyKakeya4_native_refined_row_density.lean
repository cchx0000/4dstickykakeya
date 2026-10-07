import Theorems.Thm_StickyKakeya4_native_refined_global_rows
import Theorems.Thm_StickyKakeya4_native_last_menu_shading_size

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 3600000

noncomputable section
namespace NativeRefinedRowDensity
open Classical Finset MeasureTheory StickyKakeya4 NativeCommonCubicalMesh
open NativeCubicalIncidenceCounts NativeOriginalParentSelection NativeOriginalParentDensityCore
open NativeLocalPairFibers NativeCoarseShadingCapacity NativeCoarseDyadicShading
open NativeCoarseShadingUniformity NativeGlobalCoarseRows NativeLastMenuShadingSize
open NativeRefinedGlobalRows NativeFixedSizeScaleMenu
open scoped ENNReal BigOperators

/-- The finest original depth is a valid single local-pair richness scale.
This is just the capacity scale condition, not a native-source admission. -/
lemma finest_pair_scale_valid {delta : ℝ} (level : ℕ)
    (hdy : delta=(2:ℝ)⁻¹^level) :
    0 < (2^level:ℕ) ∧ ((2^level:ℕ):ℝ)*delta/64 ≤ 1 := by
  constructor
  · positivity
  · rw [NativeDyadicParentCells.dyadic_fine_scale hdy]
    norm_num

/-- One finest-depth richness relation supplies all full-row and spatial
cover lower bounds without a lost endpoint-window power. -/
theorem finest_rich_row_bounds {n : ℕ} {D : FiniteScaleSource n}
    {eta a lambda gamma : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (E2 : Finset (Fin n × Index)) (hE2 : E2 ⊆ incidences original)
    (F1 G Q2 level : ℕ) (hF1 : 0 < F1) (hG : 0 < G) (hQ2 : 0 < Q2)
    (hlambda : 0 < lambda) (hdy : D.thickness=(2:ℝ)⁻¹^level)
    (hRich : ∀e,e∈E2 → D.thickness^eta*(2^level:ℕ)/
      (16384*(((F1:ℝ)/lambda)*(G:ℝ))*(Q2:ℝ)^2) ≤
        (pairFiber D a (2^level) E2 (localPair D a (2^level) e)).card)
    (hcost : (125*175616*16384:ℝ)*(F1:ℝ)*(G:ℝ)*(Q2:ℝ)^2*D.thickness^(-eta) ≤
      D.thickness^(-gamma))
    (m b : ℕ) (hbm : b ≤ m) (hml : m ≤ level) (hb6 : 6 ≤ b)
    (rep : Parent → Fin n) (p : Parent) (hp : (parentEdges D a (2^m) E2 p).Nonempty) :
    (125/64:ℝ)*lambda*D.thickness^gamma ≤
      (64/((2^b:ℕ):ℝ))*(rowCells D a level m b rep E2 p).card ∧
    (64/((2^b:ℕ):ℝ))*(rowCells D a level m b rep E2 p).card ≤
      16*NativeOriginalPrunedMass.volumeConstant := by
  have hd := h.1.2.1
  have hbl := hbm.trans hml
  have hB := block_pos level b
  have hrows := refined_projected_row_lower_absorbed h original horiginal ha E2 hE2 F1 G Q2
    hF1 hG hQ2 hlambda (fun _ : Fin 1 => 2^level) (fun _ e he => hRich e he) hcost
    0 (2^m) (block level b) hB rep p hp
  have hscaled := mul_le_mul_of_nonneg_left hrows
    (show 0 ≤ 64/((2^b:ℕ):ℝ) by positivity)
  have hc : (64/((2^b:ℕ):ℝ))*(125*lambda*D.thickness^gamma*
      ((2^level:ℕ):ℝ)/(block level b:ℝ)) =
      (125/64:ℝ)*lambda*D.thickness^gamma*(((2^level:ℕ):ℝ)*D.thickness) := by
    rw [block_scale hdy hbl]
    field_simp [hd.ne']
    ring
  rw [hc,NativeDyadicParentCells.dyadic_fine_scale hdy,mul_one] at hscaled
  constructor
  · simpa only [rowCells_eq_rows] using hscaled
  · have hu := projected_row_card_upper h original horiginal ha (2^m) (block level b) hB
      (by rw [block_thickness hdy hbl]; exact NativeCoarseShadingPruning.coarse_thickness_le_one b hb6)
      rep E2 hE2 p
    simpa only [block_thickness hdy hbl,rowCells_eq_rows] using hu

/-- Actual two-stage full-row density using the one finest richness scale.
The lower exponent is exactly rankLoss+c1+c2, with no endpoint-window loss. -/
theorem two_stage_finest_row_bounds {n : ℕ} {D : FiniteScaleSource n}
    {eta eta2 a lambda rankLoss c1 c2 : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (E2 : Finset (Fin n × Index)) (hE2 : E2 ⊆ incidences original)
    (F1 F2 G Q1 Q2 level : ℕ) (hF1 : 0 < F1) (hG : 0 < G) (hQ2 : 0 < Q2)
    (hQ1 : 1 ≤ Q1) (hGF : G ≤ F2) (heta2 : 0 ≤ eta2)
    (hdy : D.thickness=(2:ℝ)⁻¹^level) (hrank : D.thickness^rankLoss ≤ lambda)
    (hRich : ∀e,e∈E2 → D.thickness^eta*(2^level:ℕ)/
      (16384*(((F1:ℝ)/lambda)*(G:ℝ))*(Q2:ℝ)^2) ≤
        (pairFiber D a (2^level) E2 (localPair D a (2^level) e)).card)
    (hcost1 : (125*175616*16384:ℝ)*(F1:ℝ)*(Q1:ℝ)^2*D.thickness^(-eta) ≤ D.thickness^(-c1))
    (hcost2 : (125*175616*16384:ℝ)*(F2:ℝ)*(Q2:ℝ)^2*D.thickness^(-eta2) ≤ D.thickness^(-c2))
    (m b : ℕ) (hbm : b ≤ m) (hml : m ≤ level) (hb6 : 6 ≤ b)
    (rep : Parent → Fin n) (p : Parent) (hp : (parentEdges D a (2^m) E2 p).Nonempty) :
    D.thickness^(rankLoss+c1+c2) ≤
      (64/((2^b:ℕ):ℝ))*(rowCells D a level m b rep E2 p).card ∧
    (64/((2^b:ℕ):ℝ))*(rowCells D a level m b rep E2 p).card ≤
      16*NativeOriginalPrunedMass.volumeConstant := by
  have hd := h.1.2.1
  have hlambda := (Real.rpow_pos_of_pos hd rankLoss).trans_le hrank
  have hcost := nonrank_row_cost hd h.1.2.2.1 heta2 F1 F2 G Q1 Q2 hQ1 hGF hcost1 hcost2
  have hh := finest_rich_row_bounds h original horiginal ha E2 hE2 F1 G Q2 level
    hF1 hG hQ2 hlambda hdy hRich hcost m b hbm hml hb6 rep p hp
  refine ⟨?_,hh.2⟩
  calc
    _ = D.thickness^rankLoss*D.thickness^(c1+c2) := by
      rw [←Real.rpow_add hd]
      congr 1
      ring
    _ ≤ lambda*D.thickness^(c1+c2) :=
      mul_le_mul_of_nonneg_right hrank (Real.rpow_pos_of_pos hd _).le
    _ ≤ (125/64:ℝ)*(lambda*D.thickness^(c1+c2)) := by
      exact le_mul_of_one_le_left (by positivity) (by norm_num)
    _ = (125/64:ℝ)*lambda*D.thickness^(c1+c2) := by ring
    _ ≤ _ := hh.1

end NativeRefinedRowDensity
