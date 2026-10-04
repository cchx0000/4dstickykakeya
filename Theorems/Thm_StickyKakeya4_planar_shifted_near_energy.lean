import Theorems.Thm_StickyKakeya4_abelian_shifted_label_energy
import Theorems.Thm_StickyKakeya4_actual_rounded_additive_energy

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

namespace PlanarShiftedNearEnergy
open TwoTubePathCollisionCount
noncomputable section
variable {P : Type*} [DecidableEq P]

lemma seven_discrepancies {x y eta : ℝ} {i j : ℤ} (heta : 0 < eta)
    (hx : 0 ≤ x-eta*(i:ℝ) ∧ x-eta*(i:ℝ) < 2*eta)
    (hy : 0 ≤ y-eta*(j:ℝ) ∧ y-eta*(j:ℝ) < 2*eta)
    (hxy : |x-y| ≤ 2*eta) : -3 ≤ i-j ∧ i-j ≤ 3 := by
  obtain ⟨hl,hu⟩ := abs_le.mp hxy
  have hlo : (-4:ℝ) < (i:ℝ)-(j:ℝ) := by nlinarith
  have hup : (i:ℝ)-(j:ℝ) < 4 := by nlinarith
  have hlo' : (-4:ℤ) < i-j := by exact_mod_cast hlo
  have hup' : i-j < (4:ℤ) := by exact_mod_cast hup
  omega

def coordinateNearPairs (A : Finset P) (v : P → ℝ×ℝ) (delta : ℝ) : Finset (P×P) :=
  (A.product A).filter (fun p => |(v p.1).1-(v p.2).1| ≤ delta ∧
    |(v p.1).2-(v p.2).2| ≤ delta)

/-- The actual planar near pairs occupy49 fixed discrepancy classes. This
is the labelled energy adapter needed for the vector-valued Section21 sum. -/
theorem near_pairs_le_fortynine_energy (A : Finset P) (f : P → ℤ×ℤ)
    (v : P → ℝ×ℝ) {eta : ℝ} (heta : 0 < eta)
    (h1 : ∀ p∈A, 0 ≤ (v p).1-eta*((f p).1:ℝ) ∧
      (v p).1-eta*((f p).1:ℝ) < 2*eta)
    (h2 : ∀ p∈A, 0 ≤ (v p).2-eta*((f p).2:ℝ) ∧
      (v p).2-eta*((f p).2:ℝ) < 2*eta) :
    (coordinateNearPairs A v (2*eta)).card ≤ 49*(collisions A f).card := by
  classical
  let D := (Finset.Icc (-3:ℤ) 3).product (Finset.Icc (-3:ℤ) 3)
  have hd : D.card = 49 := by decide
  have h := AbelianShiftedLabelEnergy.pair_set_le_menu_energy A f
    (coordinateNearPairs A v (2*eta)) D (Finset.filter_subset _ _) (by
      intro p hp
      obtain ⟨hm,hx,hy⟩ := Finset.mem_filter.mp hp
      obtain ⟨hp1,hp2⟩ := Finset.mem_product.mp hm
      have hx' := seven_discrepancies heta (h1 p.1 hp1) (h1 p.2 hp2) hx
      have hy' := seven_discrepancies heta (h2 p.1 hp1) (h2 p.2 hp2) hy
      exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr hx',Finset.mem_Icc.mpr hy'⟩)
  simpa only [hd] using h

def roundPoint (eta : ℝ) (x : ℝ×ℝ) : ℤ×ℤ :=
  (ActualRoundedAdditiveEnergy.rounded eta x.1,ActualRoundedAdditiveEnergy.rounded eta x.2)

/-- Preserve every original point/pair label before any fiber binning. -/
theorem original_labelled_planar_rounding (A : Finset P) (x y : P → ℝ×ℝ)
    {delta : ℝ} (hdelta : 0 < delta) :
    (coordinateNearPairs A (fun p => x p+y p) delta).card ≤
      49*(collisions A (fun p => roundPoint (delta/2) (x p)+roundPoint (delta/2) (y p))).card := by
  have heta : 0 < delta/2 := by positivity
  have hx (p : P) := ActualRoundedAdditiveEnergy.round_error heta (x p).1
  have hy (p : P) := ActualRoundedAdditiveEnergy.round_error heta (y p).1
  have hx2 (p : P) := ActualRoundedAdditiveEnergy.round_error heta (x p).2
  have hy2 (p : P) := ActualRoundedAdditiveEnergy.round_error heta (y p).2
  have h := near_pairs_le_fortynine_energy A
    (fun p => roundPoint (delta/2) (x p)+roundPoint (delta/2) (y p))
    (fun p => x p+y p) heta (by
      intro p _
      dsimp [roundPoint]
      push_cast
      constructor <;> nlinarith [hx p,hy p]) (by
      intro p _
      dsimp [roundPoint]
      push_cast
      constructor <;> nlinarith [hx2 p,hy2 p])
  simpa only [show 2*(delta/2)=delta by ring] using h
end
end PlanarShiftedNearEnergy
