import Theorems.Thm_StickyKakeya4_original_window_physical_cells
import Theorems.Thm_StickyKakeya4_euclidean_alignment_patches
import Theorems.Thm_StickyKakeya4_original_w_physical_displacement

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2600000

noncomputable section
namespace OriginalTubeSliceOccupancy
open Classical OriginalPhaseCellPopulation OriginalWWitnessCounts

variable {P T : Type*}

/-- The actual four original point coordinates, in height-first order. -/
def coordinates (height x : P → ℝ) (y : P → ℝ × ℝ) (p : P) : Fin 4 → ℝ :=
  ![height p, x p, (y p).1, (y p).2]

/-- The original point's Euclidean embedding, using the canonical conversion. -/
def embedding (height x : P → ℝ) (y : P → ℝ × ℝ) (p : P) :
    EuclideanSpace ℝ (Fin 4) :=
  EuclideanAlignmentPatches.euclidean (coordinates height x y p)

/-- Equal literal physical cells give the original Euclidean distance bound. -/
theorem same_physical_cell_distance
    (height x : P → ℝ) (y : P → ℝ × ℝ) {b : ℝ} (hb : 0 < b) {p q : P}
    (hcell : physicalCell b height x y p = physicalCell b height x y q) :
    dist (embedding height x y p) (embedding height x y q) ≤ 4*b := by
  have hh := congrArg Prod.fst hcell
  have hx := congrArg (fun a : ℤ × (ℤ × (ℤ × ℤ)) => a.2.1) hcell
  have hy1 := congrArg (fun a : ℤ × (ℤ × (ℤ × ℤ)) => a.2.2.1) hcell
  have hy2 := congrArg (fun a : ℤ × (ℤ × (ℤ × ℤ)) => a.2.2.2) hcell
  have hc : SeparatedAlignmentPatches.cell b (coordinates height x y p) =
      SeparatedAlignmentPatches.cell b (coordinates height x y q) := by
    funext i
    fin_cases i
    · exact hh
    · exact hx
    · exact hy1
    · exact hy2
  simpa only [embedding, Nat.cast_ofNat] using
    EuclideanAlignmentPatches.same_cell_euclidean_dist_le b hb
      (coordinates height x y p) (coordinates height x y q) hc

/-- Separation of original labels forces injectivity of the actual delta/8
physical-cell map. This is derived, not an input multiplicity condition. -/
theorem physical_cell_injective
    (E : Finset P) (height x : P → ℝ) (y : P → ℝ × ℝ)
    {delta : ℝ} (hdelta : 0 < delta)
    (hsep : ∀ p ∈ E, ∀ q ∈ E, p ≠ q →
      delta ≤ dist (embedding height x y p) (embedding height x y q)) :
    Set.InjOn (physicalCell (delta/8) height x y) (E : Set P) := by
  intro p hp q hq hc
  by_contra hne
  have hsmall := same_physical_cell_distance height x y (by positivity : 0 < delta/8) hc
  have hlarge := hsep p hp q hq hne
  linarith

/-- The rectangle count bounds ORIGINAL LABELS, because the physical-cell map
has just been proved injective on the original separated point set. -/
theorem separated_rectangle_card
    (E S : Finset P) (hSE : S ⊆ E)
    (height x : P → ℝ) (y : P → ℝ × ℝ) (z cX : ℝ) (cY : ℝ × ℝ)
    {delta C0 : ℝ} (hdelta : 0 < delta) (hC0 : 0 ≤ C0)
    (hsep : ∀ p ∈ E, ∀ q ∈ E, p ≠ q →
      delta ≤ dist (embedding height x y p) (embedding height x y q))
    (hheight : ∀ p ∈ S, height p=z)
    (hx : ∀ p ∈ S, cX ≤ x p ∧ x p ≤ cX+2*C0*delta)
    (hy : ∀ p ∈ S,
      (cY.1 ≤ (y p).1 ∧ (y p).1 ≤ cY.1+2*C0*delta) ∧
      (cY.2 ≤ (y p).2 ∧ (y p).2 ≤ cY.2+2*C0*delta)) :
    (S.card : ℝ) ≤ (16*C0+2)^3 := by
  have hinj := physical_cell_injective E height x y hdelta hsep
  have hcard : (physicalCells S (delta/8) height x y).card = S.card := by
    apply Finset.card_image_iff.mpr
    intro p hp q hq hc
    exact hinj (hSE hp) (hSE hq) hc
  have hrect := OriginalWindowPhysicalCells.physical_cells_rectangle S height x y z cX cY
    (by positivity : 0 < delta/8) (by positivity : 0 ≤ 2*C0*delta)
    (by positivity : 0 ≤ 2*C0*delta) hheight hx hy
  rw [hcard] at hrect
  have hratio : 2*C0*delta/(delta/8) = 16*C0 := by field_simp; ring
  rw [hratio] at hrect
  convert hrect using 1; ring

/-- A fixed original tube and actual height have the claimed occupancy bound,
from original incidence residuals and original Euclidean separation alone. -/
theorem pointsAt_card_le
    (E : Finset P) (I : Finset (P × T)) (height x : P → ℝ) (y : P → ℝ × ℝ)
    (baseU u : T → ℝ) (baseV v : T → ℝ × ℝ)
    {delta C0 : ℝ} (hdelta : 0 < delta) (hC0 : 0 ≤ C0)
    (hI : ∀ p t, (p,t) ∈ I → p ∈ E)
    (hsep : ∀ p ∈ E, ∀ q ∈ E, p ≠ q →
      delta ≤ dist (embedding height x y p) (embedding height x y q))
    (hx : ∀ p t, (p,t) ∈ I → |x p-baseU t-height p*u t| ≤ C0*delta)
    (hy : ∀ p t, (p,t) ∈ I → ‖y p-baseV t-height p • v t‖ ≤ C0*delta)
    (t : T) (z : ℝ) :
    ((pointsAt I height t z).card : ℝ) ≤ (16*C0+2)^3 := by
  apply separated_rectangle_card E (pointsAt I height t z) (by
    intro p hp
    exact hI p t ((mem_pointsAt I height t z p).mp hp).1)
    height x y z (baseU t+z*u t-C0*delta)
      ((baseV t).1+z*(v t).1-C0*delta, (baseV t).2+z*(v t).2-C0*delta)
      hdelta hC0 hsep
  · intro p hp
    exact ((mem_pointsAt I height t z p).mp hp).2
  · intro p hp
    obtain ⟨hpt,hpz⟩ := (mem_pointsAt I height t z p).mp hp
    have h := abs_le.mp (hx p t hpt)
    rw [hpz] at h
    constructor <;> linarith [h.1,h.2]
  · intro p hp
    obtain ⟨hpt,hpz⟩ := (mem_pointsAt I height t z p).mp hp
    have h := hy p t hpt
    rw [hpz] at h
    have h1 := abs_le.mp (max_le_iff.mp h).1
    have h2 := abs_le.mp (max_le_iff.mp h).2
    change -(C0*delta) ≤ (y p).1-(baseV t).1-z*(v t).1 ∧
      (y p).1-(baseV t).1-z*(v t).1 ≤ C0*delta at h1
    change -(C0*delta) ≤ (y p).2-(baseV t).2-z*(v t).2 ∧
      (y p).2-(baseV t).2-z*(v t).2 ≤ C0*delta at h2
    dsimp only
    exact ⟨⟨by linarith [h1.1,h1.2], by linarith [h1.1,h1.2]⟩,
      ⟨by linarith [h2.1,h2.2], by linarith [h2.1,h2.2]⟩⟩

/-- The same original occupancy cap accepts the canonical incidenceResidual
formulation directly, with the native transverse product norm. -/
theorem pointsAt_card_le_of_incidenceResidual
    (E : Finset P) (I : Finset (P × T)) (height x : P → ℝ) (y : P → ℝ × ℝ)
    (baseU u : T → ℝ) (baseV v : T → ℝ × ℝ)
    {delta C0 : ℝ} (hdelta : 0 < delta) (hC0 : 0 ≤ C0)
    (hI : ∀ p t, (p,t) ∈ I → p ∈ E)
    (hsep : ∀ p ∈ E, ∀ q ∈ E, p ≠ q →
      delta ≤ dist (embedding height x y p) (embedding height x y q))
    (hx : ∀ p t, (p,t) ∈ I →
      ‖OriginalWPhysicalDisplacement.incidenceResidual height x baseU u p t‖ ≤ C0*delta)
    (hy : ∀ p t, (p,t) ∈ I →
      ‖OriginalWPhysicalDisplacement.incidenceResidual height y baseV v p t‖ ≤ C0*delta)
    (t : T) (z : ℝ) :
    ((pointsAt I height t z).card : ℝ) ≤ (16*C0+2)^3 := by
  apply pointsAt_card_le E I height x y baseU u baseV v hdelta hC0 hI hsep
  · intro p s hp
    simpa only [OriginalWPhysicalDisplacement.incidenceResidual, smul_eq_mul,
      Real.norm_eq_abs] using hx p s hp
  · exact hy

/-- The dimension-only constant is explicit: 18 cubed equals 5832. -/
theorem occupancy_constant_bound {C0 : ℝ} (hC0 : 1 ≤ C0) :
    (16*C0+2)^3 ≤ 5832*C0^3 := by
  have h := pow_le_pow_left₀ (by positivity : 0 ≤ 16*C0+2)
    (by linarith : 16*C0+2 ≤ 18*C0) 3
  nlinarith only [h]

/-- Explicit constant bound for a literal original tube-height point fiber. -/
theorem pointsAt_card_le_constant
    (E : Finset P) (I : Finset (P × T)) (height x : P → ℝ) (y : P → ℝ × ℝ)
    (baseU u : T → ℝ) (baseV v : T → ℝ × ℝ)
    {delta C0 : ℝ} (hdelta : 0 < delta) (hC0 : 1 ≤ C0)
    (hI : ∀ p t, (p,t) ∈ I → p ∈ E)
    (hsep : ∀ p ∈ E, ∀ q ∈ E, p ≠ q →
      delta ≤ dist (embedding height x y p) (embedding height x y q))
    (hx : ∀ p t, (p,t) ∈ I → |x p-baseU t-height p*u t| ≤ C0*delta)
    (hy : ∀ p t, (p,t) ∈ I → ‖y p-baseV t-height p • v t‖ ≤ C0*delta)
    (t : T) (z : ℝ) :
    ((pointsAt I height t z).card : ℝ) ≤ 5832*C0^3 :=
  (pointsAt_card_le E I height x y baseU u baseV v hdelta (by linarith) hI hsep hx hy t z).trans
    (occupancy_constant_bound hC0)

/-- Absorb the fixed geometric constant into one additional delta^(-eta). -/
theorem occupancy_rpow_bound {delta eta C0 : ℝ} (hdelta : 0 < delta)
    (hC0 : 1 ≤ C0) (hCM : C0 ≤ delta^(-eta)) (hM : 5832 ≤ delta^(-eta)) :
    (16*C0+2)^3 ≤ delta^(-4*eta) := by
  have hp : C0^3 ≤ (delta^(-eta))^3 := pow_le_pow_left₀ (by linarith) hCM 3
  calc
    _ ≤ 5832*C0^3 := occupancy_constant_bound hC0
    _ ≤ delta^(-eta)*(delta^(-eta))^3 := mul_le_mul hM hp (by positivity) (by positivity)
    _ = (delta^(-eta))^4 := by ring
    _ = delta^(-4*eta) := by
      rw [← Real.rpow_mul_natCast hdelta.le (-eta) 4]
      congr 1
      ring

/-- The scalar-terminal collision caller's C is derived on literal P labels. -/
theorem pointsAt_card_le_rpow
    (E : Finset P) (I : Finset (P × T)) (height x : P → ℝ) (y : P → ℝ × ℝ)
    (baseU u : T → ℝ) (baseV v : T → ℝ × ℝ)
    {delta eta C0 : ℝ} (hdelta : 0 < delta) (hC0 : 1 ≤ C0)
    (hCM : C0 ≤ delta^(-eta)) (hM : 5832 ≤ delta^(-eta))
    (hI : ∀ p t, (p,t) ∈ I → p ∈ E)
    (hsep : ∀ p ∈ E, ∀ q ∈ E, p ≠ q →
      delta ≤ dist (embedding height x y p) (embedding height x y q))
    (hx : ∀ p t, (p,t) ∈ I → |x p-baseU t-height p*u t| ≤ C0*delta)
    (hy : ∀ p t, (p,t) ∈ I → ‖y p-baseV t-height p • v t‖ ≤ C0*delta)
    (t : T) (z : ℝ) :
    ((pointsAt I height t z).card : ℝ) ≤ delta^(-4*eta) :=
  (pointsAt_card_le E I height x y baseU u baseV v hdelta (by linarith) hI hsep hx hy t z).trans
    (occupancy_rpow_bound hdelta hC0 hCM hM)

end OriginalTubeSliceOccupancy
