import Theorems.Thm_StickyKakeya4_native_global_coarse_rows
import Theorems.Thm_StickyKakeya4_native_two_stage_transversality_budget

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 3600000

noncomputable section
namespace NativeRefinedGlobalRows
open Classical Finset MeasureTheory StickyKakeya4 NativeCommonCubicalMesh
open NativeCubicalIncidenceCounts NativeOriginalParentSelection NativeOriginalParentDensityCore
open NativeLocalPairFibers NativeCoarseShadingCapacity NativeGlobalCoarseRows
open NativeTwoStageTransversalityBudget
open scoped ENNReal BigOperators

lemma first_cost_without_radix {delta eta cost : ℝ} (hd : 0 < delta)
    (F Q : ℕ) (hQ : 1 ≤ Q)
    (H : (125*175616*16384:ℝ)*(F:ℝ)*(Q:ℝ)^2*delta^(-eta) ≤ delta^(-cost)) :
    (125*175616*16384:ℝ)*(F:ℝ)*delta^(-eta) ≤ delta^(-cost) := by
  have hQr : (1:ℝ) ≤ Q := by exact_mod_cast hQ
  have hQ2 : (1:ℝ) ≤ (Q:ℝ)^2 := one_le_pow₀ hQr
  calc
    _ ≤ ((125*175616*16384:ℝ)*(F:ℝ)*delta^(-eta))*(Q:ℝ)^2 :=
      le_mul_of_one_le_right (by positivity) hQ2
    _ = (125*175616*16384:ℝ)*(F:ℝ)*(Q:ℝ)^2*delta^(-eta) := by ring
    _ ≤ _ := H

/-- The actual two source costs pay the full-row denominator. The rank
retention lambda is deliberately absent here and remains visible below. -/
theorem nonrank_row_cost {delta eta1 eta2 c1 c2 : ℝ}
    (hd : 0 < delta) (hd1 : delta ≤ 1) (heta2 : 0 ≤ eta2)
    (F1 F2 G Q1 Q2 : ℕ) (hQ1 : 1 ≤ Q1) (hGF : G ≤ F2)
    (hcost1 : (125*175616*16384:ℝ)*(F1:ℝ)*(Q1:ℝ)^2*delta^(-eta1) ≤ delta^(-c1))
    (hcost2 : (125*175616*16384:ℝ)*(F2:ℝ)*(Q2:ℝ)^2*delta^(-eta2) ≤ delta^(-c2)) :
    (125*175616*16384:ℝ)*(F1:ℝ)*(G:ℝ)*(Q2:ℝ)^2*delta^(-eta1) ≤
      delta^(-(c1+c2)) := by
  have hOld := first_cost_without_radix hd F1 Q1 hQ1 hcost1
  have hNew := retention_radix_le_of_transfer_cost hd hd1 heta2 F2 Q2 (G:ℝ)
    (by exact_mod_cast hGF) hcost2
  calc
    _ = ((125*175616*16384:ℝ)*(F1:ℝ)*delta^(-eta1))*((G:ℝ)*(Q2:ℝ)^2) := by ring
    _ ≤ delta^(-c1)*delta^(-c2) :=
      mul_le_mul hOld hNew (by positivity) (Real.rpow_pos_of_pos hd _).le
    _ = _ := by rw [←Real.rpow_add hd]; congr 1; ring

lemma retention_radix_six {delta cost : ℝ} (hd : 0 < delta)
    (G Q : ℕ) (hG : 0 < G) (H : (G:ℝ)*(Q:ℝ)^2 ≤ delta^(-cost)) :
    (G:ℝ)*(Q:ℝ)^6 ≤ delta^(-(3*cost)) := by
  have hG1 : (1:ℝ) ≤ G := by exact_mod_cast hG
  have hG2 : (1:ℝ) ≤ (G:ℝ)^2 := one_le_pow₀ hG1
  have hG3 : (G:ℝ) ≤ (G:ℝ)^3 := by
    have hh := mul_le_mul_of_nonneg_left hG2 (Nat.cast_nonneg (α := ℝ) G)
    nlinarith
  have hpow := pow_le_pow_left₀ (show 0 ≤ (G:ℝ)*(Q:ℝ)^2 by positivity) H 3
  calc
    _ ≤ (G:ℝ)^3*(Q:ℝ)^6 := mul_le_mul_of_nonneg_right hG3 (by positivity)
    _ = ((G:ℝ)*(Q:ℝ)^2)^3 := by ring
    _ ≤ (delta^(-cost))^3 := hpow
    _ = _ := by rw [←Real.rpow_mul_natCast hd.le]; congr 1; norm_num; ring

/-- Installing the short-row comparison costs four additional powers of
the NEW radix. The same second source budget pays these at cost 3c2. -/
theorem nonrank_short_row_cost {delta eta1 eta2 c1 c2 : ℝ}
    (hd : 0 < delta) (hd1 : delta ≤ 1) (heta2 : 0 ≤ eta2)
    (F1 F2 G Q1 Q2 : ℕ) (hG : 0 < G) (hQ1 : 1 ≤ Q1) (hGF : G ≤ F2)
    (hcost1 : (125*175616*16384:ℝ)*(F1:ℝ)*(Q1:ℝ)^2*delta^(-eta1) ≤ delta^(-c1))
    (hcost2 : (125*175616*16384:ℝ)*(F2:ℝ)*(Q2:ℝ)^2*delta^(-eta2) ≤ delta^(-c2)) :
    (125*175616*16384:ℝ)*(F1:ℝ)*(G:ℝ)*(Q2:ℝ)^6*delta^(-eta1) ≤
      delta^(-(c1+3*c2)) := by
  have hOld := first_cost_without_radix hd F1 Q1 hQ1 hcost1
  have hNew := retention_radix_six hd G Q2 hG
    (retention_radix_le_of_transfer_cost hd hd1 heta2 F2 Q2 (G:ℝ)
      (by exact_mod_cast hGF) hcost2)
  calc
    _ = ((125*175616*16384:ℝ)*(F1:ℝ)*delta^(-eta1))*((G:ℝ)*(Q2:ℝ)^6) := by ring
    _ ≤ delta^(-c1)*delta^(-(3*c2)) :=
      mul_le_mul hOld hNew (by positivity) (Real.rpow_pos_of_pos hd _).le
    _ = _ := by rw [←Real.rpow_add hd]; congr 1; ring

/-- The actual richness returned after rank selection and second refinement
controls each full projected row. No IsCore hypothesis is imposed on E2. -/
theorem refined_projected_row_lower {n g : ℕ} {D : FiniteScaleSource n}
    {eta a lambda : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (E2 : Finset (Fin n × Index)) (hE2 : E2 ⊆ incidences original)
    (F1 G Q2 : ℕ) (scales : Fin g → ℕ)
    (hRich : ∀j e,e∈E2 → D.thickness^eta*scales j/
      (16384*(((F1:ℝ)/lambda)*(G:ℝ))*(Q2:ℝ)^2) ≤
        (pairFiber D a (scales j) E2 (localPair D a (scales j) e)).card)
    (j : Fin g) (N B : ℕ) (hB : 0 < B) (rep : Parent → Fin n)
    (p : Parent) (hp : (parentEdges D a N E2 p).Nonempty) :
    D.thickness^eta*scales j/(16384*(((F1:ℝ)/lambda)*(G:ℝ))*(Q2:ℝ)^2) ≤
      175616*(B:ℝ)*(rows D a N B rep E2 p).card := by
  obtain ⟨e,he⟩ := hp
  obtain ⟨heE,hep⟩ := mem_filter.mp he
  have hh := hRich j e heE
  have hcap := pair_fiber_le_projected_rows h original horiginal ha E2 hE2
    (scales j) N B hB rep e
  rw [hep] at hcap
  exact hh.trans (by exact_mod_cast hcap)

lemma retained_richness_coefficient {delta eta gamma lambda : ℝ}
    (hd : 0 < delta) (hlambda : 0 < lambda) (F1 G Q2 : ℕ)
    (hF1 : 0 < F1) (hG : 0 < G) (hQ2 : 0 < Q2)
    (hcost : (125*175616*16384:ℝ)*(F1:ℝ)*(G:ℝ)*(Q2:ℝ)^2*delta^(-eta) ≤
      delta^(-gamma)) :
    125*175616*lambda*delta^gamma ≤
      delta^eta/(16384*(((F1:ℝ)/lambda)*(G:ℝ))*(Q2:ℝ)^2) := by
  have hF1r : (0:ℝ) < F1 := by exact_mod_cast hF1
  have hGr : (0:ℝ) < G := by exact_mod_cast hG
  have hQr : (0:ℝ) < Q2 := by exact_mod_cast hQ2
  have hden : 0 < 16384*(((F1:ℝ)/lambda)*(G:ℝ))*(Q2:ℝ)^2 := by positivity
  have hc := mul_le_mul_of_nonneg_right hcost
    (show 0 ≤ delta^gamma*delta^eta by positivity)
  have he1 : delta^(-eta)*(delta^gamma*delta^eta)=delta^gamma := by
    rw [←Real.rpow_add hd,←Real.rpow_add hd]
    congr 1
    ring
  have he2 : delta^(-gamma)*(delta^gamma*delta^eta)=delta^eta := by
    rw [←Real.rpow_add hd,←Real.rpow_add hd]
    congr 1
    ring
  rw [mul_assoc _ (delta^(-eta)),he1,he2] at hc
  apply (le_div_iff₀ hden).mpr
  have he : (125*175616*lambda*delta^gamma)*
      (16384*(((F1:ℝ)/lambda)*(G:ℝ))*(Q2:ℝ)^2) =
      (125*175616*16384:ℝ)*(F1:ℝ)*(G:ℝ)*(Q2:ℝ)^2*delta^gamma := by
    field_simp [hlambda.ne']
  rw [he]
  exact hc

/-- Global row richness with the exact rank-retention factor lambda. The
two-stage cost can be supplied by nonrank_row_cost above. -/
theorem refined_projected_row_lower_absorbed {n g : ℕ} {D : FiniteScaleSource n}
    {eta a lambda gamma : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (E2 : Finset (Fin n × Index)) (hE2 : E2 ⊆ incidences original)
    (F1 G Q2 : ℕ) (hF1 : 0 < F1) (hG : 0 < G) (hQ2 : 0 < Q2)
    (hlambda : 0 < lambda) (scales : Fin g → ℕ)
    (hRich : ∀j e,e∈E2 → D.thickness^eta*scales j/
      (16384*(((F1:ℝ)/lambda)*(G:ℝ))*(Q2:ℝ)^2) ≤
        (pairFiber D a (scales j) E2 (localPair D a (scales j) e)).card)
    (hcost : (125*175616*16384:ℝ)*(F1:ℝ)*(G:ℝ)*(Q2:ℝ)^2*D.thickness^(-eta) ≤
      D.thickness^(-gamma))
    (j : Fin g) (N B : ℕ) (hB : 0 < B) (rep : Parent → Fin n)
    (p : Parent) (hp : (parentEdges D a N E2 p).Nonempty) :
    125*lambda*D.thickness^gamma*(scales j:ℝ)/(B:ℝ) ≤ (rows D a N B rep E2 p).card := by
  have hbase := retained_richness_coefficient h.1.2.1 hlambda F1 G Q2 hF1 hG hQ2 hcost
  have hraw := refined_projected_row_lower h original horiginal ha E2 hE2 F1 G Q2
    scales hRich j N B hB rep p hp
  have hh := (mul_le_mul_of_nonneg_right hbase (Nat.cast_nonneg (scales j))).trans
    (by simpa only [div_mul_eq_mul_div,mul_comm (scales j:ℝ)] using hraw)
  apply (div_le_iff₀ (show (0:ℝ) < B by exact_mod_cast hB)).mpr
  nlinarith only [hh]

end NativeRefinedGlobalRows
