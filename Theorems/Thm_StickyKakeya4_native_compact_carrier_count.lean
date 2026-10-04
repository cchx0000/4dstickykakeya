import Theorems.Thm_StickyKakeya4_native_compact_chart_reach
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
noncomputable section
namespace NativeCompactCarrierCount
open Classical Finset StickyKakeya4 NativeOriginalParentSelection NativeOriginalParentCount
open scoped ENNReal BigOperators

/-- A fixed compact original marked family gives a fixed finite carrier cover
before choosing the scale or the retained family. Native AD supplies the
cubic source count inside each occupied cover element. -/
theorem compact_carrier_card_bound (K : Set MarkedLine) (hK : IsCompact K) :
    ∃ C : ℕ, 0<C ∧ ∀ (n : ℕ) (D : FiniteScaleSource n) (eta : ℝ),
      IsWangZakharovNativeFiniteInput D eta → (∀ i,D.line i∈K) →
      (n:ℝ≥0∞)≤C*(ENNReal.ofReal D.thickness).rpow (-eta)*
        (ENNReal.ofReal (1/D.thickness))^3 := by
  have hcompact : IsCompact (lineCarrier K) := hK.image continuous_fst
  obtain ⟨cover,_hcoverK,hfinite,hcover⟩ := hcompact.finite_cover_balls
    (show (0:ℝ)<1/2 by norm_num)
  let centers := hfinite.toFinset
  refine ⟨centers.card+1,by omega,?_⟩
  intro n D eta h hDK
  let cells := fun c : E4×E4 => univ.filter fun i : Fin n => dist (wzCarrierPoint D i) c<1/2
  have hcoverI : (univ:Finset (Fin n))⊆centers.biUnion cells := by
    intro i _hi
    have hq : wzCarrierPoint D i∈lineCarrier K := ⟨D.line i,hDK i,rfl⟩
    obtain ⟨c,hc⟩ := Set.mem_iUnion.mp (hcover hq)
    obtain ⟨hcK,hnear⟩ := Set.mem_iUnion.mp hc
    exact mem_biUnion.mpr ⟨c,(by simpa [centers] using hcK),mem_filter.mpr ⟨mem_univ _,hnear⟩⟩
  let U := (ENNReal.ofReal D.thickness).rpow (-eta)*(ENNReal.ofReal (1/D.thickness))^3
  have hcell (c : E4×E4) : ((cells c).card:ℝ≥0∞)≤U := by
    by_cases hne : (cells c).Nonempty
    · obtain ⟨i,hi⟩ := hne
      have hsub : cells c⊆univ.filter fun j=>dist (wzCarrierPoint D j) (wzCarrierPoint D i)≤1 := by
        intro j hj
        apply mem_filter.mpr
        refine ⟨mem_univ _,?_⟩
        have hi' := (mem_filter.mp hi).2
        have hj' := (mem_filter.mp hj).2
        have ht := dist_triangle (wzCarrierPoint D j) c (wzCarrierPoint D i)
        rw [dist_comm c] at ht
        linarith
      have hc : (cells c).card≤wzCarrierBallCount D i 1 := card_le_card hsub
      exact (show ((cells c).card:ℝ≥0∞)≤wzCarrierBallCount D i 1 by exact_mod_cast hc).trans
        (h.1.2.2.2.2.2.2.2.2.2.2.1 i 1 h.1.2.2.1 le_rfl).2
    · rw [not_nonempty_iff_eq_empty.mp hne,card_empty,Nat.cast_zero]
      exact bot_le
  calc
    (n:ℝ≥0∞)≤∑c∈centers,((cells c).card:ℝ≥0∞) := by
      have hh : n≤∑c∈centers,(cells c).card := by
        simpa only [card_univ,Fintype.card_fin] using (card_le_card hcoverI).trans card_biUnion_le
      exact_mod_cast hh
    _ ≤ ∑_c∈centers,U := sum_le_sum (fun c _=>hcell c)
    _ = (centers.card:ℝ≥0∞)*U := by simp
    _ ≤ (centers.card+1:ℕ)*U := mul_le_mul' (by exact_mod_cast Nat.le_add_right centers.card 1) le_rfl
    _ = _ := by dsimp [U]; ring

end NativeCompactCarrierCount
