import Theorems.Thm_StickyKakeya4_original_weighted_line_color_selection
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2200000

open scoped BigOperators
noncomputable section
namespace OriginalDensestFiberRetention
open Classical OriginalPairStripGeometry OriginalPhysicalPairTube OriginalUnitLineGrid
open OriginalLineCellSourceMass OriginalWeightedLineColorSelection

/-- Every retained original cell fiber is paid by its two original endpoints.
A uniform original wide-tube population bound therefore converts weighted
cell retention to a representative count, without equating these weights. -/
theorem selected_original_fibers_le_population_square
    (P : Finset Point) (G S : Finset Pair) (rho B : ℝ)
    (hrho : 0<rho) (hS : S⊆G)
    (hinj : Set.InjOn (lineCell rho) (↑S : Set Pair))
    (hGP : G⊆P.product P) (hbox : ∀ p∈P, |p.1|≤1 ∧ |p.2|≤1)
    (hdistinct : ∀ z∈G, z.1≠z.2)
    (hpop : ∀ z∈S, ((physicalPairTube P (6*rho) z).card : ℝ)≤B) :
    ((originalCellGraph G S rho).card : ℝ)≤S.card*B^2 := by
  rw [original_selected_cell_graph_card G S rho hinj,Nat.cast_sum]
  calc
    _ ≤ ∑ z∈S, B^2 := by
      apply Finset.sum_le_sum
      intro z hz
      have hf := original_line_cell_fiber_mass P G rho z hrho (hdistinct z (hS hz)) hGP hbox
      have hfr : ((G.filter (fun v => lineCell rho v=lineCell rho z)).card : ℝ)≤
          ((physicalPairTube P (6*rho) z).card : ℝ)^2 := by exact_mod_cast hf
      have hp := hpop z hz
      have hp0 : (0:ℝ)≤((physicalPairTube P (6*rho) z).card : ℝ) := by positivity
      have hs : ((physicalPairTube P (6*rho) z).card : ℝ)^2≤B^2 := by
        nlinarith only [mul_nonneg (sub_nonneg.mpr hp) hp0,
          sq_nonneg (B-(physicalPairTube P (6*rho) z).card)]
      exact hfr.trans hs
    _ = _ := by simp

/-- Coarse shading selection is by tube count. Combining its cardinality
retention with the ORIGINAL cell-fiber bound pays for this step; no
unjustified claim that every selected tube carries the same edge mass is used. -/
theorem original_pair_mass_after_coarse_selection
    (P : Finset Point) (G T S : Finset Pair) (rho B : ℝ) (M L : ℕ)
    (hrho : 0<rho) (hT : T⊆G)
    (hinj : Set.InjOn (lineCell rho) (↑T : Set Pair))
    (hGP : G⊆P.product P) (hbox : ∀ p∈P, |p.1|≤1 ∧ |p.2|≤1)
    (hdistinct : ∀ z∈G, z.1≠z.2)
    (hpop : ∀ z∈T, ((physicalPairTube P (6*rho) z).card : ℝ)≤B)
    (hweight : G.card≤4*M^3*(originalCellGraph G T rho).card)
    (hcoarse : T.card≤L^2*S.card) :
    (G.card : ℝ)≤4*(M:ℝ)^3*(L:ℝ)^2*B^2*S.card := by
  have hfiber := selected_original_fibers_le_population_square P G T rho B
    hrho hT hinj hGP hbox hdistinct hpop
  have hweightR : (G.card : ℝ)≤4*(M:ℝ)^3*(originalCellGraph G T rho).card := by exact_mod_cast hweight
  have hcoarseR : (T.card : ℝ)≤(L:ℝ)^2*S.card := by exact_mod_cast hcoarse
  calc
    _ ≤ 4*(M:ℝ)^3*((T.card : ℝ)*B^2) :=
      hweightR.trans (mul_le_mul_of_nonneg_left hfiber (by positivity))
    _ ≤ 4*(M:ℝ)^3*(((L:ℝ)^2*S.card)*B^2) := by
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcoarseR (sq_nonneg B)) (by positivity)
    _ = _ := by ring

end OriginalDensestFiberRetention
