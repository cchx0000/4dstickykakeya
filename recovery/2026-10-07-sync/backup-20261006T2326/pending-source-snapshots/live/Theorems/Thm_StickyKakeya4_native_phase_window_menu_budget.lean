import Theorems.Thm_StickyKakeya4_native_phase_window_scale_budget

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
noncomputable section
namespace NativePhaseWindowMenuBudget
open Classical Finset NativePhaseWindowScaleBudget NativeMiddleGrainParentBudget

/-- All scales are in the final configured physical coordinates. The source
coherence width is exactly sixty-four times the displayed dyadic width. -/
def PreparedWindow (r b epsilon rhoBound : ℝ) (u d : ℕ) : Prop :=
  6 ≤ d ∧ d ≤ u+6 ∧
  0 < phaseRho r b ∧ phaseRho r b ≤ rhoBound ∧
  (2:ℝ)⁻¹^u/8 ≤ (phaseRho r b)^2 ∧
  tangentMesh r b ≤ 1/((2^d:ℕ):ℝ) ∧
  4*grainWidth r b epsilon+tangentMesh r b ≤ 1/((2^d:ℕ):ℝ) ∧
  1/((2^d:ℕ):ℝ) ≤ 2*target r b epsilon ∧
  (2:ℝ)⁻¹^u ≤ 64/((2^d:ℕ):ℝ) ∧
  1/((2^d:ℕ):ℝ) ≤ 21*offsetMesh r b epsilon ∧
  27*(2*(2064:ℝ)*(1/((2^d:ℕ):ℝ))/offsetMesh r b epsilon+2)^2 ≤
    27*(86690:ℝ)^2

/-- The finite exponent menu is fixed before the source. One positive cutoff
then works for every branch and every actual stopping radius and base. The
depths are chosen together from that same source before its coherence cuts;
the empty menu is allowed. No individual window budget is a premise. -/
theorem exists_source_menu_cutoff (K : ℕ) (amin rhoBound : ℝ) (b : Fin K → ℝ)
    (ha : 0 < amin) (hBound : 0 < rhoBound)
    (hb : ∀j, 0 < b j) (hb8 : ∀j, b j ≤ 1/8) :
    ∃delta0 : ℝ, 0 < delta0 ∧ delta0 ≤ 1 ∧
      ∀delta r power : ℝ, 0 < delta → delta ≤ delta0 → 0 < r →
      amin ≤ power → r ≤ delta^power →
      ∀epsilon : ℝ, 0 ≤ epsilon → (∀j, epsilon ≤ b j/2) →
      ∀stop u : ℕ, 6 ≤ stop → 48*((2^stop:ℕ):ℝ)*r=1 →
      (2:ℝ)⁻¹^u ≤ 2*max ((5/4:ℝ)*
        ((64:ℝ)/((2^(middleDepth stop):ℕ):ℝ))^(1-2*epsilon))
        ((64:ℝ)/((2^(middleDepth stop):ℕ):ℝ)) →
      ∃depths : Fin K → ℕ, ∀j, PreparedWindow r (b j) epsilon rhoBound u (depths j) := by
  choose cut hcut hcut1 H using
    fun j => exists_source_window_cutoff amin (b j) rhoBound ha (hb j) (hb8 j) hBound
  let delta0 : ℝ := ∏j, cut j
  have hd0 : 0 < delta0 := Finset.prod_pos (fun j _ => hcut j)
  have hd01 : delta0 ≤ 1 := Finset.prod_le_one
    (fun j _ => (hcut j).le) (fun j _ => hcut1 j)
  have hdcut : ∀j, delta0 ≤ cut j := by
    intro j
    simpa only [Finset.prod_singleton] using
      (Finset.prod_le_prod_of_subset_of_le_one
        (show ({j}:Finset (Fin K)) ⊆ univ by simp)
        (fun i _ => (hcut i).le) (fun i _ _ => hcut1 i))
  refine ⟨delta0,hd0,hd01,?_⟩
  intro delta r power hd hsmall hr hpower hrdelta epsilon he0 he stop u hs hid hbase
  have hr1 : r ≤ 1 := hrdelta.trans
    (Real.rpow_le_one hd.le (hsmall.trans hd01) (ha.le.trans hpower))
  have hlocal : ∀j, ∃d, PreparedWindow r (b j) epsilon rhoBound u d := by
    intro j
    obtain ⟨hRho,hRhoBound,hAnalytic,d,hd6,hdu,hTangent,hWidth,hTarget,hGuard⟩ :=
      H j delta r power hd (hsmall.trans (hdcut j)) hr hpower hrdelta
        epsilon he0 (he j) stop u hs hid hbase
    have hOffset := dyadic_width_le_offset_mesh hr hr1 he0 hTarget
    have hPopulation := offset_population_factor
      (show (0:ℝ) ≤ 1/((2^d:ℕ):ℝ) by positivity)
      (show 0 < offsetMesh r (b j) epsilon by
        unfold offsetMesh physicalLip phaseRho
        positivity) hOffset
    exact ⟨d,hd6,hdu,hRho,hRhoBound,hAnalytic,hTangent,hWidth,hTarget,hGuard,
      hOffset,hPopulation⟩
  choose depths hdepths using hlocal
  exact ⟨depths,hdepths⟩

end NativePhaseWindowMenuBudget
