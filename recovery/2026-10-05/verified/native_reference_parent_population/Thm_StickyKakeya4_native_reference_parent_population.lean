import Theorems.Thm_StickyKakeya4_native_reference_relative_menu
import Theorems.Thm_StickyKakeya4_native_middle_grain_parent_budget
import Theorems.Thm_StickyKakeya4_native_normalized_cell_source_upper

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

noncomputable section
namespace NativeReferenceParentPopulation
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeOriginalParentDensityCore NativeLocalParentSource NativeMiddleWindowBalance
open NativeCubicalIncidenceCounts NativeMiddleGrainParentBudget

lemma candidate_middle_bounds (level stop : ℕ) (hlevel : 6 ≤ level) (hstop : stop ≤ level) :
    6 ≤ middleDepth stop ∧ middleDepth stop ≤ level := by unfold middleDepth; omega

/-- Every predetermined candidate middle depth is at a squared scale,
even before the stopping index is selected. -/
lemma candidate_middle_square {delta : ℝ} (level stop : ℕ)
    (hdy : delta=(2:ℝ)⁻¹^level) (hstop : stop ≤ level) :
    delta ≤ ((64:ℝ)/((2^(middleDepth stop):ℕ):ℝ))^2 := by
  have hexp : middleDepth stop*2 ≤ level+12 := by unfold middleDepth; omega
  have hpow : ((2^(middleDepth stop):ℕ))^2 ≤ (2^level:ℕ)*4096 := by
    calc
      _ = 2^(middleDepth stop*2) := by rw [pow_mul]
      _ ≤ 2^(level+12) := Nat.pow_le_pow_right (by norm_num) hexp
      _ = _ := by rw [pow_add]; norm_num
  have hpR : (((2^(middleDepth stop):ℕ):ℝ))^2 ≤ (2:ℝ)^level*4096 := by exact_mod_cast hpow
  rw [hdy,inv_pow,inv_eq_one_div,div_pow]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith only [hpR]

/-- The raw first-stage cost pays FQ² and cancels eta exactly. No rank
retention or history loss enters this reference-parent population. -/
lemma first_cost_density {delta eta zeta cost : ℝ} (hd : 0 < delta)
    (F Q parentCard edgeCard : ℕ)
    (Hpop : delta^(eta+2*zeta)*(parentCard:ℝ) ≤ delta*(F:ℝ)*(Q:ℝ)^2*edgeCard)
    (Hcost : (125*175616*16384:ℝ)*(F:ℝ)*(Q:ℝ)^2*delta^(-eta) ≤ delta^(-cost)) :
    delta^(cost+2*zeta)*(parentCard:ℝ) ≤ delta*edgeCard := by
  have hn : 0 ≤ (F:ℝ)*(Q:ℝ)^2*delta^(-eta) := by positivity
  have hraw : (F:ℝ)*(Q:ℝ)^2*delta^(-eta) ≤ delta^(-cost) :=
    (show (F:ℝ)*(Q:ℝ)^2*delta^(-eta) ≤
      (125*175616*16384:ℝ)*(F:ℝ)*(Q:ℝ)^2*delta^(-eta) by nlinarith only [hn]).trans Hcost
  have hunit : (F:ℝ)*(Q:ℝ)^2*delta^(cost-eta) ≤ 1 := by
    calc
      _ = ((F:ℝ)*(Q:ℝ)^2*delta^(-eta))*delta^cost := by
        rw [mul_assoc ((F:ℝ)*(Q:ℝ)^2),←Real.rpow_add hd]
        congr 2
        ring
      _ ≤ delta^(-cost)*delta^cost := mul_le_mul_of_nonneg_right hraw (by positivity)
      _ = _ := by rw [←Real.rpow_add hd]; norm_num
  have hh := mul_le_mul_of_nonneg_left Hpop (Real.rpow_nonneg hd.le (cost-eta))
  have he : delta^(cost-eta)*(delta^(eta+2*zeta)*(parentCard:ℝ))=
      delta^(cost+2*zeta)*(parentCard:ℝ) := by
    rw [←mul_assoc,←Real.rpow_add hd]
    congr 2
    ring
  rw [he] at hh
  calc
    _ ≤ delta^(cost-eta)*(delta*(F:ℝ)*(Q:ℝ)^2*edgeCard) := hh
    _ = ((F:ℝ)*(Q:ℝ)^2*delta^(cost-eta))*(delta*edgeCard) := by ring
    _ ≤ 1*(delta*edgeCard) := mul_le_mul_of_nonneg_right hunit (by positivity)
    _ = _ := one_mul _

/-- Same-R/E1 caller at any installed candidate parent. F is the ACTUAL
retention factor of the enlarged first-stage core. -/
theorem reference_parent_population {n : ℕ} {D : FiniteScaleSource n} {eta zeta a cost : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (R : Finset (Fin n)) (level : ℕ) (HB : HasOriginalBackbone D original R a level zeta)
    (hsmall : D.thickness ≤ 1/8) (E1 : Finset (Fin n × Index)) (hE : E1⊆retained original R)
    (F Q m : ℕ) (hm : m ≤ level) (hret : (incidences original).card ≤ F*E1.card)
    (Hparent : ∀x y,x∈E1 → y∈E1 →
      (parentEdges D a (2^m) E1 (parentLabel D a (2^m) x.1)).card ≤
        Q^2*(parentEdges D a (2^m) E1 (parentLabel D a (2^m) y.1)).card)
    (Hcost : (125*175616*16384:ℝ)*(F:ℝ)*(Q:ℝ)^2*D.thickness^(-eta) ≤ D.thickness^(-cost))
    (p : Parent) (hp : (parentEdges D a (2^m) E1 p).Nonempty) :
    D.thickness^(cost+2*zeta)*(parentLabels D R a (2^m) p).card ≤
      D.thickness*(parentEdges D a (2^m) E1 p).card := by
  have hpopulation := parent_average_density h original HB.1 hsmall R (2^m) Q F (by positivity) E1
    (fun z hz => (mem_filter.mp (hE hz)).2) hret Hparent
    (fun q hq => HB.2.2.2.2.2.2.2.2 ⟨m,by omega⟩ q hq) p hp
  exact first_cost_density h.1.2.1 F Q _ _ hpopulation Hcost

end NativeReferenceParentPopulation
