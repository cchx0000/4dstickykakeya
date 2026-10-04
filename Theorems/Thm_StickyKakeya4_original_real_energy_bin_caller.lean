import Theorems.Thm_StickyKakeya4_integer_bin_real_near_energy

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

noncomputable section
namespace OriginalRealEnergyBinCaller
open ActualRoundedAdditiveEnergy ShiftedLabelEnergy DyadicOriginalFiberSelection
open IntegerBinRealNearEnergy

/-- The exact source-level (89) adapter for the native singleton-C case.
It starts with original real A and original pair labels, constructs a literal
real grid bin X, retains original pair mass, and supplies the actual real
near-difference energy required by the asymmetric BSG endpoint. -/
theorem exists_original_real_bsg_bin
    {P : Type*} [DecidableEq P] (A : Finset ℝ) (W : Finset P) (v : P → ℝ)
    (hA : A.Nonempty) (hW : W.Nonempty) {delta nu : ℝ}
    (hdelta : 0<delta) (hnu : 0<nu)
    (hsep : ∀ a∈A, ∀ b∈A, a≠b → delta≤|a-b|)
    (he : nu*(A.card : ℝ)*(W.card : ℝ)^2 ≤
      ((nearPairs (A.product W) (fun p => p.1+v p.2) delta).card : ℝ)) :
    ∃ j<levelCount W,
      let f := fun p => rounded delta (v p)
      let X := realGrid delta ((bin W f j).image f)
      (bin W f j).Nonempty ∧ X.Nonempty ∧
      (∀ x∈X, ∀ y∈X, x≠y → delta≤|x-y|) ∧
      nu*(W.card : ℝ)≤10*(levelCount W : ℝ)*(bin W f j).card ∧
      nu*(A.card : ℝ)*(X.card : ℝ)^2 ≤
        40*(levelCount W : ℝ)^2*(nearDifferenceEnergy X A delta : ℝ) := by
  classical
  obtain ⟨j,hj,hbin,hm,henergy⟩ := LabelledRealEnergyBin.exists_real_energy_preserving_bin
    A W v hA hW hdelta hnu hsep he
  let f := fun p => rounded delta (v p)
  let S := (bin W f j).image f
  have hS : S.Nonempty := hbin.image f
  have hX : (realGrid delta S).Nonempty := hS.image _
  have htransfer : (Finset.addEnergy (A.image (rounded delta)) S : ℝ) ≤
      (nearDifferenceEnergy (realGrid delta S) A delta : ℝ) := by
    exact_mod_cast integer_energy_le_original_near A S hdelta hsep
  have hfinal := henergy.trans (mul_le_mul_of_nonneg_left htransfer
    (by positivity : 0≤40*(levelCount W : ℝ)^2))
  refine ⟨j,hj,hbin,hX,real_grid_separated hdelta S,hm,?_⟩
  simpa only [real_grid_card hdelta] using hfinal

end OriginalRealEnergyBinCaller
