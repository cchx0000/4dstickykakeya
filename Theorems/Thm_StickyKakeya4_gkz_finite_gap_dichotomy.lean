import Theorems.Thm_StickyKakeya4_gkz_finite_halving_net
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000
noncomputable section
open Classical

namespace GKZFiniteGapDichotomy
open GKZFiniteHalvingNet ActualRoundedAdditiveEnergy

/-- Counting original dyadic witnesses gives an explicit occupied-cell lower
bound. Each output cell receives at most eight dyadic labels. -/
theorem original_net_floor_count (S : Finset ℝ) (m : ℕ)
    (hnet : ∀ k : ℕ, k < 2^m →
      ∃ b ∈ S, |gridPoint m k-b| ≤ 2*((2:ℝ)^m)⁻¹) :
    1 ≤ 8*((2:ℝ)^m)⁻¹ * (S.image (rounded (((2:ℝ)^m)⁻¹))).card := by
  let s : ℝ := ((2:ℝ)^m)⁻¹
  have hs : 0 < s := by dsimp [s]; positivity
  have hw : ∀ i : Fin (2^m), ∃ b ∈ S, |gridPoint m i.val-b| ≤ 2*s :=
    fun i => hnet i.val i.isLt
  choose b hb hnear using hw
  let P : Finset (Fin (2^m)) := Finset.univ
  let f : Fin (2^m) → ℤ := fun i => rounded s (b i)
  have hgrid (i : Fin (2^m)) : ⌊gridPoint m i.val/s⌋ = (i.val : ℤ) := by
    have heq : gridPoint m i.val/s = (i.val : ℝ) := by
      dsimp [gridPoint, s]
      field_simp
    rw [heq]
    simp
  have hfiber : ∀ z ∈ P.image f,
      ((P.filter (fun i => f i=z)).card : ℝ) ≤ 8 := by
    intro z _
    apply (NativeTangentGridCoarsening.scalar_injective_grid_centered_card
      (P.filter (fun i => f i=z)) (fun i => gridPoint m i.val)
      (r := s) (R := 3) (c := s*(z:ℝ)) hs (by norm_num) ?_ ?_).trans (by norm_num)
    · intro i _ j _ hij
      simp only [hgrid] at hij
      exact Fin.ext (by exact_mod_cast hij)
    · intro i hi
      have hcell := (Finset.mem_filter.mp hi).2
      have herr := round_error hs (b i)
      change rounded s (b i) = z at hcell
      rw [hcell] at herr
      have hround : |b i-s*(z:ℝ)| ≤ s :=
        (abs_of_nonneg herr.1).le.trans herr.2.le
      exact (abs_sub_le (gridPoint m i.val) (b i) (s*(z:ℝ))).trans (by
        have hn := hnear i
        linarith)
  have hmass := OriginalSeparatedPacking.card_le_real_mul_image P f hfiber
  have himage : P.image f ⊆ S.image (rounded s) := by
    intro z hz
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hz
    exact Finset.mem_image.mpr ⟨b i, hb i, rfl⟩
  have hcard : ((2^m : ℕ) : ℝ) ≤ 8*(S.image (rounded s)).card := by
    have hc : ((P.image f).card : ℝ) ≤ (S.image (rounded s)).card :=
      Nat.cast_le.mpr (Finset.card_le_card himage)
    simpa only [P, Finset.card_univ, Fintype.card_fin] using
      hmass.trans (mul_le_mul_of_nonneg_left hc (by norm_num))
  have hmass' := mul_le_mul_of_nonneg_left hcard hs.le
  have hid : s*((2^m:ℕ):ℝ)=1 := by simp [s]
  rw [hid] at hmass'
  change 1 ≤ 8*s*(S.image (rounded s)).card
  nlinarith

/-- A finite version of GKZ Lemma 4.1 with actual original gap witnesses and
an explicit dyadic occupied-cell lower bound in the dense alternative. -/
theorem original_gap_or_dense (B : Finset ℝ) (m : ℕ)
    (hzero : 0 ∈ B) (hone : 1 ∈ B) :
    (∃ b ∈ B, 0 ≤ b ∧ b ≤ 1 ∧
      ((∀ z ∈ B, ((2:ℝ)^m)⁻¹ ≤ |b/2-z|) ∨
       (∀ z ∈ B, ((2:ℝ)^m)⁻¹ ≤ |(b+1)/2-z|))) ∨
    1 ≤ 8*((2:ℝ)^m)⁻¹ *
      ((B.filter (fun b => 0 ≤ b ∧ b ≤ 1)).image
        (rounded (((2:ℝ)^m)⁻¹))).card := by
  let s : ℝ := ((2:ℝ)^m)⁻¹
  let S := B.filter (fun b => 0 ≤ b ∧ b ≤ 1)
  by_cases hgap : ∃ b ∈ B, 0 ≤ b ∧ b ≤ 1 ∧
      ((∀ z ∈ B, s ≤ |b/2-z|) ∨ (∀ z ∈ B, s ≤ |(b+1)/2-z|))
  · exact Or.inl hgap
  right
  have hchild : ∀ b ∈ S, (∃ z ∈ S, |b/2-z| ≤ s) ∧
      (∃ z ∈ S, |(b+1)/2-z| ≤ s) := by
    intro b hb
    obtain ⟨hbB, hb0, hb1⟩ := Finset.mem_filter.mp hb
    have hleft : ¬ ∀ z ∈ B, s ≤ |b/2-z| := by
      intro hh
      exact hgap ⟨b, hbB, hb0, hb1, Or.inl hh⟩
    have hright : ¬ ∀ z ∈ B, s ≤ |(b+1)/2-z| := by
      intro hh
      exact hgap ⟨b, hbB, hb0, hb1, Or.inr hh⟩
    push Not at hleft hright
    obtain ⟨z, hz, hnear⟩ := hleft
    obtain ⟨z', hz', hz0, hz1, hnear'⟩ := original_unit_interval_approximation
      B hzero hone (x := b/2) ⟨by linarith, by linarith⟩ hz
    obtain ⟨w, hw, hnearw⟩ := hright
    obtain ⟨w', hw', hw0, hw1, hnearw'⟩ := original_unit_interval_approximation
      B hzero hone (x := (b+1)/2) ⟨by linarith, by linarith⟩ hw
    exact ⟨⟨z', Finset.mem_filter.mpr ⟨hz', hz0, hz1⟩, hnear'.trans hnear.le⟩,
      ⟨w', Finset.mem_filter.mpr ⟨hw', hw0, hw1⟩, hnearw'.trans hnearw.le⟩⟩
  apply original_net_floor_count S m
  apply original_dyadic_net S (by positivity)
    (Finset.mem_filter.mpr ⟨hzero, le_rfl, by norm_num⟩)
  · exact fun b hb => (hchild b hb).1
  · exact fun b hb => (hchild b hb).2

end GKZFiniteGapDichotomy
