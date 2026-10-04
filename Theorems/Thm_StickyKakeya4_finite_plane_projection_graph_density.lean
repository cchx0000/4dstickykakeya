import Theorems.Thm_StickyKakeya4_finite_plane_projection_graph_core
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
open Finset
noncomputable section
open Classical
namespace FinitePlaneProjectionGraph

lemma original_density_le_one {X Y Z : Type*}
    (P : Finset X) (B : Finset Y) (C : Finset Z) (G : Finset (X × (Y × Z))) {beta : ℝ}
    (hP : P.Nonempty) (hB : B.Nonempty) (hC : C.Nonempty)
    (hG : G ⊆ P ×ˢ (B ×ˢ C))
    (hdense : beta * P.card * B.card * C.card ≤ (G.card : ℝ)) : beta ≤ 1 := by
  have hNp : 0 < (P.card : ℝ) := by exact_mod_cast hP.card_pos
  have hNb : 0 < (B.card : ℝ) := by exact_mod_cast hB.card_pos
  have hNc : 0 < (C.card : ℝ) := by exact_mod_cast hC.card_pos
  have hcap : (G.card : ℝ) ≤ (P.card : ℝ) * B.card * C.card := by
    have hh : (G.card : ℝ) ≤ ((P ×ˢ (B ×ˢ C)).card : ℝ) := Nat.cast_le.mpr (Finset.card_le_card hG)
    simpa only [Finset.card_product, Nat.cast_mul, mul_assoc] using hh
  have hprod : 0 < (P.card : ℝ) * B.card * C.card := by positivity
  apply (mul_le_mul_iff_left₀ hprod).mp
  calc
    _ = beta * P.card * B.card * C.card := by ring
    _ ≤ G.card := hdense
    _ ≤ (P.card : ℝ) * B.card * C.card := hcap
    _ = _ := by ring

theorem original_vertex_retention_from_graph_mass {X Y Z : Type*}
    (P S : Finset X) (B T : Finset Y) (C : Finset Z)
    (G E : Finset (X × (Y × Z))) {beta L : ℝ}
    (hP : P.Nonempty) (hB : B.Nonempty) (hC : C.Nonempty)
    (hb : 0 ≤ beta) (hL : 0 ≤ L) (hSP : S ⊆ P) (hTB : T ⊆ B)
    (hE : E ⊆ S ×ˢ (T ×ˢ C))
    (hdense : beta * P.card * B.card * C.card ≤ (G.card : ℝ))
    (hmass : (G.card : ℝ) ≤ L * E.card) :
    beta * P.card ≤ L * S.card ∧ beta * B.card ≤ L * T.card ∧
      beta * S.card * T.card * C.card ≤ L * E.card := by
  have hNp : 0 < (P.card : ℝ) := by exact_mod_cast hP.card_pos
  have hNb : 0 < (B.card : ℝ) := by exact_mod_cast hB.card_pos
  have hNc : 0 < (C.card : ℝ) := by exact_mod_cast hC.card_pos
  have hSr : (S.card : ℝ) ≤ P.card := Nat.cast_le.mpr (Finset.card_le_card hSP)
  have hTr : (T.card : ℝ) ≤ B.card := Nat.cast_le.mpr (Finset.card_le_card hTB)
  have hcap : (E.card : ℝ) ≤ (S.card : ℝ) * T.card * C.card := by
    have hh : (E.card : ℝ) ≤ ((S ×ˢ (T ×ˢ C)).card : ℝ) := Nat.cast_le.mpr (Finset.card_le_card hE)
    simpa only [Finset.card_product, Nat.cast_mul, mul_assoc] using hh
  have htotal := hdense.trans hmass
  have hcapL := mul_le_mul_of_nonneg_left hcap hL
  have hleft : L * E.card ≤ (L * S.card) * ((B.card : ℝ) * C.card) := by
    have hh := mul_le_mul_of_nonneg_right hTr (show 0 ≤ L * (S.card : ℝ) * C.card by positivity)
    nlinarith
  have hright : L * E.card ≤ (L * T.card) * ((P.card : ℝ) * C.card) := by
    have hh := mul_le_mul_of_nonneg_right hSr (show 0 ≤ L * (T.card : ℝ) * C.card by positivity)
    nlinarith
  refine ⟨?_, ?_, ?_⟩
  · apply (mul_le_mul_iff_left₀ (show 0 < (B.card : ℝ) * C.card by positivity)).mp
    calc
      _ = beta * P.card * B.card * C.card := by ring
      _ ≤ L * E.card := htotal
      _ ≤ _ := hleft
  · apply (mul_le_mul_iff_left₀ (show 0 < (P.card : ℝ) * C.card by positivity)).mp
    calc
      _ = beta * P.card * B.card * C.card := by ring
      _ ≤ L * E.card := htotal
      _ ≤ _ := hright
  · have hST : (S.card : ℝ) * T.card ≤ (P.card : ℝ) * B.card :=
      mul_le_mul hSr hTr (by positivity) (by positivity)
    have hh := mul_le_mul_of_nonneg_right hST (show 0 ≤ beta * C.card by positivity)
    nlinarith

lemma reciprocal_population_bound (N M beta L : ℝ) (hb : 0 < beta)
    (hmass : beta * N ≤ L * M) : N ≤ (L / beta) * M := by
  calc
    N ≤ L * M / beta := (le_div_iff₀ hb).mpr (by nlinarith)
    _ = _ := by ring
end FinitePlaneProjectionGraph
