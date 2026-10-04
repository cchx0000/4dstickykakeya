import Theorems.Thm_StickyKakeya4_energy_preserving_original_fiber_bin
import Theorems.Thm_StickyKakeya4_actual_rounded_additive_energy

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

open scoped BigOperators
noncomputable section

namespace LabelledRealEnergyBin
open TwoTubePathCollisionCount ShiftedLabelEnergy ActualRoundedAdditiveEnergy
open DyadicOriginalFiberSelection

/-- Rounding keeps EVERY original pair label, even when many labels have the
same real value. Separation is required only on the actual A source. -/
theorem labelled_near_energy_le_five
    {P : Type*} [DecidableEq P] (A : Finset ℝ) (W : Finset P) (v : P → ℝ)
    {delta : ℝ} (hdelta : 0<delta)
    (hsep : ∀ a∈A, ∀ b∈A, a≠b → delta≤|a-b|) :
    (nearPairs (A.product W) (fun p => p.1+v p.2) delta).card ≤
      5*(collisions ((A.image (rounded delta)).product W)
        (fun p => p.1+rounded delta (v p.2))).card := by
  classical
  have hnear := near_pairs_le_five_energy (A.product W)
    (fun p => rounded delta p.1+rounded delta (v p.2)) (fun p => p.1+v p.2) hdelta
    (by
      intro p _
      have ha := round_error hdelta p.1
      have hv := round_error hdelta (v p.2)
      push_cast
      constructor <;> nlinarith)
  let g : ℝ × P → ℤ × P := fun p => (rounded delta p.1,p.2)
  have hinj : Set.InjOn g (A.product W) := by
    intro p hp q hq heq
    have hs : p.2=q.2 := by
      simpa only [g] using congrArg (fun r : ℤ × P => r.2) heq
    have hf : rounded delta p.1=rounded delta q.1 := by
      simpa only [g] using congrArg (fun r : ℤ × P => r.1) heq
    exact Prod.ext ((rounding_injOn A hdelta hsep) (Finset.mem_product.mp hp).1
      (Finset.mem_product.mp hq).1 hf) hs
  have him : (A.product W).image g=(A.image (rounded delta)).product W := by
    ext q
    constructor
    · intro hq
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hq
      obtain ⟨ha,hw⟩ := Finset.mem_product.mp hp
      exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ ha,hw⟩
    · intro hq
      obtain ⟨ha,hw⟩ := Finset.mem_product.mp hq
      obtain ⟨a,ha,heq⟩ := Finset.mem_image.mp ha
      exact Finset.mem_image.mpr ⟨(a,q.2),Finset.mem_product.mpr ⟨ha,hw⟩,Prod.ext heq rfl⟩
  have hcoll := collisions_image_card (A.product W) g
    (fun p : ℤ × P => p.1+rounded delta (v p.2)) hinj
  rw [him] at hcoll
  change (collisions (A.product W) (fun p => rounded delta p.1+rounded delta (v p.2))).card = _ at hcoll
  rwa [hcoll] at hnear

/-- The real per-pair energy cap is derived from original separation through
actual rounding and the translation injection, with a fixed factor five. -/
theorem labelled_near_energy_cap
    {P : Type*} [DecidableEq P] (A : Finset ℝ) (W : Finset P) (v : P → ℝ)
    {delta : ℝ} (hdelta : 0<delta)
    (hsep : ∀ a∈A, ∀ b∈A, a≠b → delta≤|a-b|) :
    (nearPairs (A.product W) (fun p => p.1+v p.2) delta).card ≤ 5*A.card*W.card^2 := by
  have h := (labelled_near_energy_le_five A W v hdelta hsep).trans
    (Nat.mul_le_mul_left 5 (PartitionedCollisionEnergy.translated_pair_energy_cap
      (A.image (rounded delta)) W (fun p => rounded delta (v p))))
  simpa only [rounded_card A hdelta hsep,Nat.mul_assoc] using h

/-- Closed real (89) caller for singleton C: one original fiber bin keeps
original pair mass and supplies unweighted integer energy simultaneously. -/
theorem exists_real_energy_preserving_bin
    {P : Type*} [DecidableEq P] (A : Finset ℝ) (W : Finset P) (v : P → ℝ)
    (hA : A.Nonempty) (hW : W.Nonempty) {delta nu : ℝ}
    (hdelta : 0<delta) (hnu : 0<nu)
    (hsep : ∀ a∈A, ∀ b∈A, a≠b → delta≤|a-b|)
    (he : nu*(A.card : ℝ)*(W.card : ℝ)^2 ≤
      ((nearPairs (A.product W) (fun p => p.1+v p.2) delta).card : ℝ)) :
    ∃ j<levelCount W,
      let f := fun p => rounded delta (v p)
      let S := (bin W f j).image f
      (bin W f j).Nonempty ∧
      nu*(W.card : ℝ)≤10*(levelCount W : ℝ)*(bin W f j).card ∧
      nu*(A.card : ℝ)*(S.card : ℝ)^2 ≤
        40*(levelCount W : ℝ)^2*(Finset.addEnergy (A.image (rounded delta)) S : ℝ) := by
  classical
  let f := fun p => rounded delta (v p)
  have hround : ((nearPairs (A.product W) (fun p => p.1+v p.2) delta).card : ℝ) ≤
      5*((collisions ((A.image (rounded delta)).product W) (fun p => p.1+f p.2)).card : ℝ) := by
    exact_mod_cast labelled_near_energy_le_five A W v hdelta hsep
  have he' : (nu/5)*((A.image (rounded delta)).card : ℝ)*(W.card : ℝ)^2 ≤
      ((collisions ((A.image (rounded delta)).product W) (fun p => p.1+f p.2)).card : ℝ) := by
    rw [rounded_card A hdelta hsep]
    nlinarith only [he.trans hround]
  obtain ⟨j,hj,hbin,hm,henergy⟩ := EnergyPreservingOriginalFiberBin.exists_energy_preserving_bin
    (A.image (rounded delta)) W f (hA.image _) hW (div_pos hnu (by norm_num)) he'
  rw [rounded_card A hdelta hsep] at henergy
  refine ⟨j,hj,hbin,?_,?_⟩
  · nlinarith only [hm]
  · nlinarith only [henergy]

end LabelledRealEnergyBin
