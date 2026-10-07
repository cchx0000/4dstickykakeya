import Theorems.Thm_StickyKakeya4_native_refined_row_density
import Theorems.Thm_StickyKakeya4_native_refined_row_relations
import Theorems.Thm_StickyKakeya4_native_pair_scale_budget

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 4200000

noncomputable section
namespace NativeRefinedShortRowDensity
open Classical Finset MeasureTheory StickyKakeya4 NativeCommonCubicalMesh
open NativeCubicalIncidenceCounts NativeOriginalParentSelection NativeOriginalParentDensityCore
open NativeLocalPairFibers NativeCoarseShadingCapacity NativeCoarseDyadicShading
open NativeCoarseShadingUniformity NativeCoarseDirectionThinning NativeGlobalCoarseRows
open NativeLastMenuShadingSize NativeRefinedGlobalRows NativeRefinedRowDensity
open NativeRefinedRowRelations NativeJointUniformCoarseRelations
open scoped ENNReal BigOperators

/-- Only the two actual query relations are required; no surrounding
all-pairs schedule is assumed. The representative is identical in both maps. -/
theorem queried_rowChildren_comparable {n : ℕ} {D : FiniteScaleSource n} (a : ℝ)
    (level m b : ℕ) (hdy : D.thickness=(2:ℝ)⁻¹^level) (hbm : b ≤ m) (hml : m ≤ level)
    (rep : Parent → Fin n) (E : Finset (Fin n × Index)) (Q : ℕ)
    (HF : HasUniformFibers E Q (fixedPair D a level m m rep))
    (HC : HasUniformFibers E Q (fixedPair D a level m b rep))
    (p p' : Parent) (q q' : Index)
    (hq : q∈rowCells D a level m b rep E p) (hq' : q'∈rowCells D a level m b rep E p') :
    (rowChildren D a level m b rep E p q).card ≤ Q^4*(rowChildren D a level m b rep E p' q').card := by
  exact rowChildren_comparable (D := D) a level m b hdy hbm hml rep E Q
    (by
      intro x hx y hy
      convert HF x hx y hy using 1)
    (by
      intro x hx y hy
      convert HC x hx y hy using 1) p p' q q' hq hq'

/-- The installed finite row relations control every occupied short cell
at that installed pair. This is separate from any off-menu claim. -/
theorem installed_rowChildren_comparable {n g level : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n)) (a : ℝ)
    (schedule : Fin g → Fin (level+1)) (E : Finset (Fin n × Index)) (Q : ℕ)
    (HU : ∀i j,HasUniformFibers E Q (rowPair h R a schedule i j))
    (hdy : D.thickness=(2:ℝ)⁻¹^level) (i j : Fin g)
    (hji : (schedule j).val ≤ (schedule i).val) (p p' : Parent) (q q' : Index)
    (hq : q∈rowCells D a level (schedule i).val (schedule j).val
      (representative h R a (2^(schedule i).val)) E p)
    (hq' : q'∈rowCells D a level (schedule i).val (schedule j).val
      (representative h R a (2^(schedule i).val)) E p') :
    (rowChildren D a level (schedule i).val (schedule j).val
      (representative h R a (2^(schedule i).val)) E p q).card ≤ Q^4*
        (rowChildren D a level (schedule i).val (schedule j).val
          (representative h R a (2^(schedule i).val)) E p' q').card := by
  exact rowChildren_comparable (D := D) a level (schedule i).val (schedule j).val hdy hji
    (Nat.le_of_lt_succ (schedule i).isLt) (representative h R a (2^(schedule i).val)) E Q
    (by
      intro x hx y hy
      have hh := HU i i x hx y hy
      dsimp only [rowPair] at hh
      convert hh using 1
      all_goals congr)
    (by
      intro x hx y hy
      have hh := HU i j x hx y hy
      dsimp only [rowPair] at hh
      convert hh using 1
      all_goals congr) p p' q q' hq hq'


lemma rowChildren_card_sum {n : ℕ} {D : FiniteScaleSource n} (a : ℝ)
    (level m b : ℕ) (hdy : D.thickness=(2:ℝ)⁻¹^level) (hbm : b ≤ m) (hml : m ≤ level)
    (rep : Parent → Fin n) (E : Finset (Fin n × Index)) (p : Parent) :
    (rowCells D a level m m rep E p).card =
      ∑q∈rowCells D a level m b rep E p,(rowChildren D a level m b rep E p q).card := by
  rw [rowCells_eq_ancestor_image a level m b hdy hbm hml rep E p]
  exact card_eq_sum_card_image (cellAncestor m b) (rowCells D a level m m rep E p)

theorem row_card_le_children {n : ℕ} {D : FiniteScaleSource n} (a : ℝ)
    (level m b : ℕ) (hdy : D.thickness=(2:ℝ)⁻¹^level) (hbm : b ≤ m) (hml : m ≤ level)
    (rep : Parent → Fin n) (E : Finset (Fin n × Index)) (p : Parent) (q : Index) (K : ℕ)
    (H : ∀r∈rowCells D a level m b rep E p,
      (rowChildren D a level m b rep E p r).card ≤ K*(rowChildren D a level m b rep E p q).card) :
    (rowCells D a level m m rep E p).card ≤
      K*(rowCells D a level m b rep E p).card*(rowChildren D a level m b rep E p q).card := by
  rw [rowChildren_card_sum a level m b hdy hbm hml rep E p]
  calc
    _ ≤ ∑_r∈rowCells D a level m b rep E p,K*(rowChildren D a level m b rep E p q).card :=
      sum_le_sum H
    _ = _ := by simp only [sum_const,nsmul_eq_mul,Nat.cast_id]; ring

theorem queried_children_card_bound {n : ℕ} {D : FiniteScaleSource n} (a : ℝ)
    (level m b : ℕ) (hdy : D.thickness=(2:ℝ)⁻¹^level) (hbm : b ≤ m) (hml : m ≤ level)
    (rep : Parent → Fin n) (E : Finset (Fin n × Index)) (Q : ℕ)
    (HF : HasUniformFibers E Q (fixedPair D a level m m rep))
    (HC : HasUniformFibers E Q (fixedPair D a level m b rep))
    (p : Parent) (q : Index) (hq : q∈rowCells D a level m b rep E p) :
    (rowCells D a level m m rep E p).card ≤
      Q^4*(rowCells D a level m b rep E p).card*(rowChildren D a level m b rep E p q).card := by
  apply row_card_le_children a level m b hdy hbm hml rep E p q (Q^4)
  intro r hr
  exact queried_rowChildren_comparable a level m b hdy hbm hml rep E Q HF HC p p r q hr hq

/-- The installed relations yield the required upper on the full row in
terms of any one occupied short cell and the number of occupied coarse cells. -/
theorem installed_children_card_bound {n g level : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n)) (a : ℝ)
    (schedule : Fin g → Fin (level+1)) (E : Finset (Fin n × Index)) (Q : ℕ)
    (HU : ∀i j,HasUniformFibers E Q (rowPair h R a schedule i j))
    (hdy : D.thickness=(2:ℝ)⁻¹^level) (i j : Fin g)
    (hji : (schedule j).val ≤ (schedule i).val) (p : Parent) (q : Index)
    (hq : q∈rowCells D a level (schedule i).val (schedule j).val
      (representative h R a (2^(schedule i).val)) E p) :
    (rowCells D a level (schedule i).val (schedule i).val
      (representative h R a (2^(schedule i).val)) E p).card ≤
      Q^4*(rowCells D a level (schedule i).val (schedule j).val
        (representative h R a (2^(schedule i).val)) E p).card*
      (rowChildren D a level (schedule i).val (schedule j).val
        (representative h R a (2^(schedule i).val)) E p q).card := by
  apply row_card_le_children a level (schedule i).val (schedule j).val hdy hji
    (Nat.le_of_lt_succ (schedule i).isLt) (representative h R a (2^(schedule i).val)) E p q (Q^4)
  intro r hr
  exact installed_rowChildren_comparable h R a schedule E Q HU hdy i j hji p p r q hr hq

lemma count_lower_of_partition {delta rho beta U coefficient loss cost : ℝ}
    (hd : 0 < delta) (hrho : 0 ≤ rho) (hbeta : 0 ≤ beta) (K X Y Z : ℕ)
    (hcard : X ≤ K*Y*Z) (hFine : coefficient*delta^loss ≤ rho*X)
    (hCoarse : beta*Y ≤ U) (hCost : U*(K:ℝ) ≤ delta^(-cost)) :
    coefficient*delta^(loss+cost)*beta ≤ rho*Z := by
  have hc : (X:ℝ) ≤ (K:ℝ)*Y*Z := by exact_mod_cast hcard
  have hz : 0 ≤ rho*(Z:ℝ) := mul_nonneg hrho (Nat.cast_nonneg Z)
  have hcross : coefficient*delta^loss*beta ≤ delta^(-cost)*(rho*Z) := by
    calc
      _ ≤ (rho*(X:ℝ))*beta := mul_le_mul_of_nonneg_right hFine hbeta
      _ ≤ (rho*((K:ℝ)*Y*Z))*beta :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc hrho) hbeta
      _ = ((K:ℝ)*(beta*Y))*(rho*Z) := by ring
      _ ≤ ((K:ℝ)*U)*(rho*Z) := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hCoarse (Nat.cast_nonneg K)) hz
      _ = (U*(K:ℝ))*(rho*Z) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hCost hz
  calc
    _ = delta^cost*(coefficient*delta^loss*beta) := by rw [Real.rpow_add hd]; ring
    _ ≤ delta^cost*(delta^(-cost)*(rho*Z)) :=
      mul_le_mul_of_nonneg_left hcross (Real.rpow_pos_of_pos hd _).le
    _ = _ := by rw [←mul_assoc,←Real.rpow_add hd,add_neg_cancel,Real.rpow_zero,one_mul]

lemma volume_constant_bound : 16*NativeOriginalPrunedMass.volumeConstant ≤ (41472:ℝ) := by
  have hp := pow_le_pow_left₀ Real.pi_pos.le Real.pi_lt_four.le 2
  dsimp [NativeOriginalPrunedMass.volumeConstant]
  nlinarith

/-- The second raw source cost pays both Q2^4 and the geometric row-cover
constant. This introduces no additional source cutoff. -/
lemma short_cell_cost {delta eta2 c2 : ℝ} (hd : 0 < delta) (hd1 : delta ≤ 1)
    (heta2 : 0 ≤ eta2) (F2 Q2 : ℕ) (hF2 : 0 < F2)
    (H : (125*175616*16384:ℝ)*(F2:ℝ)*(Q2:ℝ)^2*delta^(-eta2) ≤ delta^(-c2)) :
    (16*NativeOriginalPrunedMass.volumeConstant)*(Q2:ℝ)^4 ≤ delta^(-(2*c2)) := by
  have hh := (NativePairScaleBudget.radix_four_cost hd hd1 heta2 F2 Q2 hF2 H).1
  exact (mul_le_mul_of_nonneg_right volume_constant_bound
    (pow_nonneg (Nat.cast_nonneg Q2) 4)).trans hh

/-- Actual occupied short-row lower density on E2 at any queried scale pair
with its two installed relations. The source costs and rank retention lambda are explicit, and the new radix is paid
at the full exponent c1+3c2. No off-menu occupancy lower is assumed. -/
theorem queried_short_row_lower {n level : ℕ} {D : FiniteScaleSource n}
    {eta eta2 a lambda c1 c2 : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (R : Finset (Fin n)) (E2 : Finset (Fin n × Index)) (hE2 : E2 ⊆ incidences original)
    (F1 F2 G Q1 Q2 : ℕ) (hF1 : 0 < F1) (hG : 0 < G) (hQ2 : 0 < Q2)
    (hQ1 : 1 ≤ Q1) (hGF : G ≤ F2) (heta2 : 0 ≤ eta2)
    (hdy : D.thickness=(2:ℝ)⁻¹^level) (hlambda : 0 < lambda)
    (hRich : ∀e,e∈E2 → D.thickness^eta*(2^level:ℕ)/
      (16384*(((F1:ℝ)/lambda)*(G:ℝ))*(Q2:ℝ)^2) ≤
        (pairFiber D a (2^level) E2 (localPair D a (2^level) e)).card)
    (hcost1 : (125*175616*16384:ℝ)*(F1:ℝ)*(Q1:ℝ)^2*D.thickness^(-eta) ≤ D.thickness^(-c1))
    (hcost2 : (125*175616*16384:ℝ)*(F2:ℝ)*(Q2:ℝ)^2*D.thickness^(-eta2) ≤ D.thickness^(-c2))
    (m b : ℕ) (hbm : b ≤ m) (hmL : m ≤ level) (hb6 : 6 ≤ b)
    (HF : HasUniformFibers E2 Q2 (fixedPair D a level m m (representative h R a (2^m))))
    (HC : HasUniformFibers E2 Q2 (fixedPair D a level m b (representative h R a (2^m))))
    (p : Parent) (q : Index)
    (hq : q∈rowCells D a level m b (representative h R a (2^m)) E2 p) :
    lambda*D.thickness^(c1+3*c2)*
      ((64/((2^b:ℕ):ℝ))/(64/((2^m:ℕ):ℝ))) ≤
      (rowChildren D a level m b (representative h R a (2^m)) E2 p q).card := by
  let rep := representative h R a (2^m)
  have hd := h.1.2.1
  have hbL : b ≤ level := hbm.trans hmL
  have hp : (parentEdges D a (2^m) E2 p).Nonempty := by
    obtain ⟨z,hz,hzq⟩ := mem_image.mp ((mem_rowCells D a level m b rep E2 p q).mp hq)
    have hpz := congrArg Prod.fst hzq
    exact ⟨z,mem_filter.mpr ⟨hz,hpz⟩⟩
  have hRowCost := nonrank_row_cost hd h.1.2.2.1 heta2 F1 F2 G Q1 Q2 hQ1 hGF hcost1 hcost2
  have hRow := (finest_rich_row_bounds h original horiginal ha E2 hE2 F1 G Q2 level
    hF1 hG hQ2 hlambda hdy hRich hRowCost m m le_rfl hmL (hb6.trans hbm) rep p hp).1
  have hFine : lambda*D.thickness^(c1+c2) ≤
      (64/((2^m:ℕ):ℝ))*(rowCells D a level m m rep E2 p).card := by
    calc
      _ ≤ (125/64:ℝ)*(lambda*D.thickness^(c1+c2)) :=
        le_mul_of_one_le_left (by positivity) (by norm_num)
      _ = (125/64:ℝ)*lambda*D.thickness^(c1+c2) := by ring
      _ ≤ _ := hRow
  have hCover := projected_row_card_upper h original horiginal ha (2^m) (block level b)
    (block_pos level b)
    (by rw [block_thickness hdy hbL]; exact NativeCoarseShadingPruning.coarse_thickness_le_one b hb6)
    rep E2 hE2 p
  have hCoarse : (64/((2^b:ℕ):ℝ))*(rowCells D a level m b rep E2 p).card ≤
      16*NativeOriginalPrunedMass.volumeConstant := by
    simpa only [block_thickness hdy hbL,rowCells_eq_rows] using hCover
  have hcard := queried_children_card_bound a level m b hdy hbm hmL rep E2 Q2 HF HC p q hq
  have hCost := short_cell_cost hd h.1.2.2.1 heta2 F2 Q2 (hG.trans_le hGF) hcost2
  have hLower := count_lower_of_partition (coefficient := lambda) (loss := c1+c2) (cost := 2*c2) hd
    (show 0 ≤ 64/((2^m:ℕ):ℝ) by positivity) (show 0 ≤ 64/((2^b:ℕ):ℝ) by positivity)
    (Q2^4) (rowCells D a level m m rep E2 p).card (rowCells D a level m b rep E2 p).card
    (rowChildren D a level m b rep E2 p q).card hcard hFine hCoarse
    (by simpa only [Nat.cast_pow] using hCost)
  have hLower' : lambda*D.thickness^(c1+3*c2)*(64/((2^b:ℕ):ℝ)) ≤
      (64/((2^m:ℕ):ℝ))*(rowChildren D a level m b rep E2 p q).card := by
    simpa only [show c1+c2+2*c2=c1+3*c2 by ring] using hLower
  have hh : lambda*D.thickness^(c1+3*c2)*(64/((2^b:ℕ):ℝ))/(64/((2^m:ℕ):ℝ)) ≤
      (rowChildren D a level m b rep E2 p q).card :=
    (div_le_iff₀ (show 0 < 64/((2^m:ℕ):ℝ) by positivity)).mpr
      (by simpa only [mul_comm] using hLower')
  simpa only [mul_div_assoc] using hh

end NativeRefinedShortRowDensity
