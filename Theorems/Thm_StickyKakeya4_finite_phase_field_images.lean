import Theorems.Thm_StickyKakeya4_native_tangent_grid_coarsening

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000

noncomputable section
namespace FinitePhaseFieldImages
open Classical

variable {P K : Type*} [DecidableEq K]

/-- Literal reflected original xi grid, with its own anisotropic mesh tau. -/
def normalPhaseCell (tau : ℝ) (xi₀ : ℝ × ℝ) (offset : P → ℝ × ℝ) (p : P) : ℤ × ℤ :=
  (⌊(xi₀-offset p).1/tau⌋,⌊(xi₀-offset p).2/tau⌋)

def normalPhaseCells (E : Finset P) (tau : ℝ) (xi₀ : ℝ × ℝ)
    (offset : P → ℝ × ℝ) : Finset (ℤ × ℤ) := E.image (normalPhaseCell tau xi₀ offset)

def phaseCells (E : Finset P) (tangentCell : P → ℤ) (tau : ℝ) (xi₀ : ℝ × ℝ)
    (offset : P → ℝ × ℝ) : Finset (ℤ × (ℤ × ℤ)) :=
  E.image (fun p => (tangentCell p,normalPhaseCell tau xi₀ offset p))

/-- Original coarse-field consistency bounds the NORMAL phase image in one
 actual physical cell. The Delta/tau loss is explicit; macro-only control is
 not silently treated as a microscopic phase-population bound. -/
theorem original_field_cell_phase_image
    (E : Finset P) (physicalCell : P → K) (offset : P → ℝ × ℝ) (field : K → ℝ × ℝ)
    (xi₀ : ℝ × ℝ) {tau Delta Cxi : ℝ}
    (htau : 0 < tau) (hDelta : 0 ≤ Delta) (hCxi : 0 ≤ Cxi)
    (hfield : ∀ p ∈ E, ‖offset p-field (physicalCell p)‖ ≤ Cxi*Delta) (k : K) :
    ((normalPhaseCells (E.filter (fun p => physicalCell p=k)) tau xi₀ offset).card : ℝ) ≤
      (2*Cxi*Delta/tau+2)^2 := by
  let S := E.filter (fun p => physicalCell p=k)
  let c := xi₀-field k
  have hnorm : ∀ p ∈ S, ‖(xi₀-offset p)-c‖ ≤ Cxi*Delta := by
    intro p hp
    obtain ⟨hpE,hpk⟩ := Finset.mem_filter.mp hp
    calc
      _ = ‖-(offset p-field k)‖ := by congr 1; dsimp [c]; abel
      _ = ‖offset p-field k‖ := norm_neg _
      _ ≤ Cxi*Delta := by simpa only [hpk] using hfield p hpE
  have hnear : ∀ p ∈ S,
      |(xi₀-offset p).1-c.1| ≤ (Cxi*Delta/tau)*tau ∧
      |(xi₀-offset p).2-c.2| ≤ (Cxi*Delta/tau)*tau := by
    intro p hp
    rw [div_mul_cancel₀ _ htau.ne']
    exact max_le_iff.mp (hnorm p hp)
  have hc := NativeTangentGridCoarsening.planar_centered_grid_card S (fun p => xi₀-offset p) c
    htau (show 0 ≤ Cxi*Delta/tau by positivity) hnear
  change ((NativeTangentGridCoarsening.planarCells S (fun p => xi₀-offset p) tau).card : ℝ) ≤ _
  convert hc using 1; ring

/-- A finite union of the actual physical-cell phase images covers the whole
 phase image. No single-valued phase-to-physical-cell map is assumed. -/
theorem original_field_phase_image
    (E : Finset P) (physicalCell : P → K) (offset : P → ℝ × ℝ) (field : K → ℝ × ℝ)
    (xi₀ : ℝ × ℝ) {tau Delta Cxi : ℝ}
    (htau : 0 < tau) (hDelta : 0 ≤ Delta) (hCxi : 0 ≤ Cxi)
    (hfield : ∀ p ∈ E, ‖offset p-field (physicalCell p)‖ ≤ Cxi*Delta) :
    ((normalPhaseCells E tau xi₀ offset).card : ℝ) ≤
      (2*Cxi*Delta/tau+2)^2*((E.image physicalCell).card : ℝ) := by
  apply NativeTangentGridCoarsening.image_card_le_real_mul_of_fiber_images E
    (normalPhaseCell tau xi₀ offset) physicalCell ((2*Cxi*Delta/tau+2)^2)
  intro k _hk
  exact original_field_cell_phase_image E physicalCell offset field xi₀ htau hDelta hCxi hfield k

/-- In a fixed actual tangent cell the full phase image has precisely the
 cardinality of its normal phase image, independent of original point fibers. -/
theorem phase_card_of_fixed_tangent_cell
    (E : Finset P) (tangentCell : P → ℤ) (tau : ℝ) (xi₀ : ℝ × ℝ)
    (offset : P → ℝ × ℝ) (k : ℤ) (hcell : ∀ p ∈ E, tangentCell p=k) :
    (phaseCells E tangentCell tau xi₀ offset).card=(normalPhaseCells E tau xi₀ offset).card := by
  have heq : phaseCells E tangentCell tau xi₀ offset=
      (normalPhaseCells E tau xi₀ offset).image (fun n => (k,n)) := by
    rw [phaseCells,normalPhaseCells,Finset.image_image]
    apply Finset.image_congr
    intro p hp
    simp only [Function.comp_def,hcell p hp]
  rw [heq]
  exact Finset.card_image_of_injOn (fun a _ b _ hab => congrArg Prod.snd hab)

end FinitePhaseFieldImages
