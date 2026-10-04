import Theorems.Thm_StickyKakeya4_original_robust_projection_exhaustion
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3500000
noncomputable section
open Classical
open scoped BigOperators

namespace OriginalWeightedDirectionGluing
open OriginalRobustProjectionExhaustion
variable {X Y : Type*} [DecidableEq Y]

def badMass (Pieces : Finset (Finset X)) (Bad : Finset X → Finset Y) (c : Y) : ℝ :=
  ∑ F∈Pieces, if c∈Bad F then (F.card:ℝ) else 0

lemma original_bad_mass_nonneg (Pieces : Finset (Finset X)) (Bad : Finset X → Finset Y) (c : Y) :
    0≤badMass Pieces Bad c := Finset.sum_nonneg (fun _ _ => by split_ifs <;> positivity)

/-- Fubini charges each bad direction by the ORIGINAL size of its piece.
The total has no factor depending on the number of pieces. -/
theorem original_total_bad_mass (Pieces : Finset (Finset X)) (C : Finset Y)
    (Bad : Finset X → Finset Y) {beta N : ℝ} (hbeta : 0≤beta)
    (hBad : ∀ F∈Pieces,Bad F⊆C)
    (hcount : ∀ F∈Pieces,((Bad F).card:ℝ)≤beta*C.card)
    (hmass : (∑ F∈Pieces,(F.card:ℝ))≤N) :
    (∑ c∈C,badMass Pieces Bad c)≤beta*C.card*N := by
  have hrow (F : Finset X) (hF : F∈Pieces) :
      (∑ c∈C,if c∈Bad F then (F.card:ℝ) else 0)=((Bad F).card:ℝ)*F.card := by
    have he : C.filter (fun c => c∈Bad F)=Bad F := by
      ext c
      simp only [Finset.mem_filter]
      exact ⟨fun hc => hc.2,fun hc => ⟨hBad F hF hc,hc⟩⟩
    rw [← Finset.sum_filter,he]
    simp only [Finset.sum_const,nsmul_eq_mul]
  unfold badMass
  rw [Finset.sum_comm]
  calc
    _ = ∑ F∈Pieces,((Bad F).card:ℝ)*F.card := Finset.sum_congr rfl hrow
    _ ≤ ∑ F∈Pieces,(beta*C.card)*(F.card:ℝ) := Finset.sum_le_sum
      (fun F hF => mul_le_mul_of_nonneg_right (hcount F hF) (Nat.cast_nonneg _))
    _ = beta*C.card*(∑ F∈Pieces,(F.card:ℝ)) := (Finset.mul_sum _ _ _).symm
    _ ≤ beta*C.card*N := mul_le_mul_of_nonneg_left hmass (by positivity)

/-- Most ORIGINAL directions lose at most a chosen original point mass
to all their bad pieces combined. -/
theorem exists_original_weighted_good_directions (Pieces : Finset (Finset X)) (C : Finset Y)
    (Bad : Finset X → Finset Y) {beta tau N : ℝ}
    (hbeta : 0≤beta) (htau : 0<tau) (hN : 0<N)
    (hBad : ∀ F∈Pieces,Bad F⊆C)
    (hcount : ∀ F∈Pieces,((Bad F).card:ℝ)≤beta*C.card)
    (hmass : (∑ F∈Pieces,(F.card:ℝ))≤N) :
    ∃ Good : Finset Y, Good⊆C ∧ (1-beta/tau)*(C.card:ℝ)≤Good.card ∧
      ∀ c∈Good,badMass Pieces Bad c≤tau*N := by
  let B := C.filter (fun c => tau*N<badMass Pieces Bad c)
  let Good := C \ B
  have hBC : B⊆C := Finset.filter_subset _ _
  have htotal := original_total_bad_mass Pieces C Bad hbeta hBad hcount hmass
  have hlow : (tau*N)*(B.card:ℝ)≤∑ c∈B,badMass Pieces Bad c := by
    calc
      _ = ∑ _c∈B,tau*N := by simp only [Finset.sum_const,nsmul_eq_mul]; ring
      _ ≤ _ := Finset.sum_le_sum (fun c hc => (Finset.mem_filter.mp hc).2.le)
  have hsum : (∑ c∈B,badMass Pieces Bad c)≤∑ c∈C,badMass Pieces Bad c :=
    Finset.sum_le_sum_of_subset_of_nonneg hBC (fun c _hc _ => original_bad_mass_nonneg Pieces Bad c)
  have hmult : tau*(B.card:ℝ)≤beta*C.card := by
    apply (mul_le_mul_iff_of_pos_right hN).mp
    nlinarith only [hlow,hsum,htotal]
  have hBcard : (B.card:ℝ)≤(beta/tau)*C.card := by
    apply (mul_le_mul_iff_of_pos_right htau).mp
    have he : ((beta/tau)*(C.card:ℝ))*tau=beta*C.card := by field_simp
    rw [he]
    nlinarith only [hmult]
  have hid : (Good.card:ℝ)+B.card=C.card := by
    exact_mod_cast Finset.card_sdiff_add_card_eq_card hBC
  refine ⟨Good,Finset.sdiff_subset,?_,?_⟩
  · nlinarith only [hBcard,hid]
  · intro c hc
    have hcC := (Finset.mem_sdiff.mp hc).1
    have hnot := (Finset.mem_sdiff.mp hc).2
    exact le_of_not_gt (fun h => hnot (Finset.mem_filter.mpr ⟨hcC,h⟩))

variable [DecidableEq X]

/-- A large original query must be dense in one of its good original
pieces. Only uncovered point mass and weighted bad mass are charged. -/
theorem exists_original_good_query_piece (P Q : Finset X) (Pieces : Finset (Finset X))
    (Bad : Finset X → Finset Y) (c : Y) {q r tau s : ℝ}
    (hP : P.Nonempty) (hQP : Q⊆P) (hs : 0≤s)
    (hslack : r+tau+s<q) (hQmass : q*(P.card:ℝ)≤Q.card)
    (hdis : (Pieces:Set (Finset X)).PairwiseDisjoint id)
    (hsub : ∀ F∈Pieces,F⊆P)
    (hres : (((P \ Pieces.biUnion id).card):ℝ)≤r*P.card)
    (hbad : badMass Pieces Bad c≤tau*P.card) :
    ∃ F∈Pieces,c∉Bad F ∧ s*(F.card:ℝ)≤(Q∩F).card := by
  by_contra h
  push Not at h
  have hbound (F : Finset X) (hF : F∈Pieces) :
      ((Q∩F).card:ℝ)≤s*F.card+(if c∈Bad F then (F.card:ℝ) else 0) := by
    by_cases hc : c∈Bad F
    · rw [if_pos hc]
      have hi : ((Q∩F).card:ℝ)≤F.card := Nat.cast_le.mpr (Finset.card_le_card Finset.inter_subset_right)
      have hp := mul_nonneg hs (Nat.cast_nonneg F.card)
      linarith only [hi,hp]
    · rw [if_neg hc,add_zero]
      exact (h F hF hc).le
  have hsum := Finset.sum_le_sum hbound
  rw [Finset.sum_add_distrib,← Finset.mul_sum] at hsum
  have hpieces := original_disjoint_piece_mass P Pieces hdis hsub
  have hpieces' := mul_le_mul_of_nonneg_left hpieces hs
  have hquery := original_query_piece_mass P Q Pieces hQP
  have hN : (0:ℝ)<P.card := Nat.cast_pos.mpr hP.card_pos
  have hstrict := mul_lt_mul_of_pos_right hslack hN
  change (∑ F∈Pieces,((Q∩F).card:ℝ))≤s*(∑ F∈Pieces,(F.card:ℝ))+badMass Pieces Bad c at hsum
  nlinarith only [hquery,hsum,hpieces',hbad,hres,hQmass,hstrict]

end OriginalWeightedDirectionGluing
