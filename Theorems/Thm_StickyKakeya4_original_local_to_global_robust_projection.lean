import Theorems.Thm_StickyKakeya4_original_weighted_direction_gluing
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000
noncomputable section
open Classical

namespace OriginalLocalToGlobalRobustProjection
open OriginalRobustProjectionExhaustion OriginalWeightedDirectionGluing
variable {X Y : Type*} [DecidableEq X] [DecidableEq Y]

/-- A local robust conclusion on every sufficiently large ORIGINAL
residual yields a global robust conclusion. Actual disjoint pieces are
constructed, and bad directions are averaged with original piece weights.
The loss is beta/tau, independent of the number of pieces. -/
theorem exists_original_global_robust_projection (P : Finset X) (C : Finset Y)
    (cover : Y → Finset X → ℝ) {q r tau s beta T : ℝ}
    (hP : P.Nonempty) (hbeta : 0≤beta) (htau : 0<tau) (hs : 0≤s)
    (hslack : r+tau+s<q)
    (hmono : ∀ c : Y, ∀ Q Q' : Finset X, Q⊆Q' → cover c Q≤cover c Q')
    (hlocal : ∀ R : Finset X, R⊆P → r*(P.card:ℝ)≤R.card →
      ∃ F : Finset X, F⊆R ∧ F.Nonempty ∧
        ∃ Good : Finset Y, Good⊆C ∧ (1-beta)*(C.card:ℝ)≤Good.card ∧
          ∀ c∈Good, ∀ Q : Finset X, Q⊆F → s*(F.card:ℝ)≤Q.card → T<cover c Q) :
    ∃ Good : Finset Y, Good⊆C ∧ (1-beta/tau)*(C.card:ℝ)≤Good.card ∧
      ∀ c∈Good, ∀ Q : Finset X, Q⊆P → q*(P.card:ℝ)≤Q.card → T<cover c Q := by
  let Valid : Finset X → Prop := fun F => ∃ Good : Finset Y,
    Good⊆C ∧ (1-beta)*(C.card:ℝ)≤Good.card ∧
      ∀ c∈Good, ∀ Q : Finset X, Q⊆F → s*(F.card:ℝ)≤Q.card → T<cover c Q
  have hextract : ∀ R : Finset X, R⊆P → r*(P.card:ℝ)≤R.card →
      ∃ F : Finset X,F⊆R ∧ F.Nonempty ∧ Valid F := hlocal
  obtain ⟨Pieces,hdis,hpieces,hres⟩ := exists_original_local_exhaustion P (r*P.card) Valid hextract
  let GoodPiece (F : Finset X) : Finset Y := if hv : Valid F then Classical.choose hv else ∅
  have hgood (F : Finset X) (hF : F∈Pieces) :
      GoodPiece F⊆C ∧ (1-beta)*(C.card:ℝ)≤(GoodPiece F).card ∧
        ∀ c∈GoodPiece F, ∀ Q : Finset X,Q⊆F → s*(F.card:ℝ)≤Q.card → T<cover c Q := by
    have hv := (hpieces F hF).2.2
    dsimp [GoodPiece]
    rw [dif_pos hv]
    exact Classical.choose_spec hv
  let Bad : Finset X → Finset Y := fun F => C \ GoodPiece F
  have hBad : ∀ F∈Pieces,Bad F⊆C := fun _ _ => Finset.sdiff_subset
  have hcount : ∀ F∈Pieces,((Bad F).card:ℝ)≤beta*C.card := by
    intro F hF
    have hc : ((Bad F).card:ℝ)+(GoodPiece F).card=C.card := by
      exact_mod_cast Finset.card_sdiff_add_card_eq_card (hgood F hF).1
    have hg := (hgood F hF).2.1
    nlinarith only [hc,hg]
  have hmass := original_disjoint_piece_mass P Pieces hdis (fun F hF => (hpieces F hF).1)
  obtain ⟨Good,hGC,hGmass,hGbad⟩ := exists_original_weighted_good_directions Pieces C Bad hbeta htau
    (Nat.cast_pos.mpr hP.card_pos) hBad hcount hmass
  refine ⟨Good,hGC,hGmass,?_⟩
  intro c hc Q hQP hQmass
  obtain ⟨F,hF,hcnot,hquery⟩ := exists_original_good_query_piece P Q Pieces Bad c hP hQP hs
    hslack hQmass hdis (fun F hF => (hpieces F hF).1) hres.le (hGbad c hc)
  have hcGood : c∈GoodPiece F := by
    by_contra h
    exact hcnot (Finset.mem_sdiff.mpr ⟨hGC hc,h⟩)
  exact ((hgood F hF).2.2 c hcGood (Q∩F) Finset.inter_subset_right hquery).trans_le
    (hmono c (Q∩F) Q Finset.inter_subset_left)

end OriginalLocalToGlobalRobustProjection
