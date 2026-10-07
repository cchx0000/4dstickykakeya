import Theorems.Thm_StickyKakeya4_native_single_height_recoding

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
noncomputable section
namespace NativeExactHeightFields
open Classical Finset NativeMatrixHeightWholePoint NativeFrozenTimeField NativeSingleHeightRecoding

/-- The physical fine-height midpoint, with its actual supplied step. -/
def physicalHeight (mu : ℝ) (z : ℤ) : ℝ := mu*((z:ℝ)+1/2)

/-- A frozen representative has the same old height as every surviving
point in its base bin. Thus its field value is EXACT, not merely close. -/
theorem frozen_eq_on_selected {P V : Type*} [Zero V] (S : Finset P)
    (height : P → ℤ) (F : ℤ → V) (mu : ℝ) (hmu : 0<mu) (N : ℕ)
    (hsame : ∀p∈S,∀q∈S,height p/(N:ℤ)=height q/(N:ℤ) → height p=height q)
    {p : P} (hp : p∈S) :
    field S (fun p => physicalHeight mu (height p)) (fun p => F (height p)) (mu*(N:ℝ))
      ⌊physicalHeight mu (height p)/(mu*(N:ℝ))⌋=F (height p) := by
  obtain ⟨q,hq,he,hread⟩ := field_realization S
    (fun p => physicalHeight mu (height p)) (fun p => F (height p)) (mu*(N:ℝ)) ⟨p,hp,rfl⟩
  rw [hread]
  apply congrArg F
  apply hsame q hq p hp
  simpa only [physicalHeight,coarse_height_readback mu hmu N] using he

/-- Both original fields are frozen on the same selected old-height source.
No continuity, norm bound, or constant-field premise is required of G. -/
theorem select_two_exact_fields {P U V : Type*} [Zero U] [Zero V]
    (S : Finset P) (w : P → ℕ) (height : P → ℤ) (F : ℤ → U) (G : ℤ → V)
    (mu : ℝ) (hmu : 0<mu) (N : ℕ) (hN : 0<N) :
    ∃T⊆S,mass S w≤N*mass T w ∧
      ∀p∈T,
        field T (fun p => physicalHeight mu (height p)) (fun p => F (height p)) (mu*(N:ℝ))
          ⌊physicalHeight mu (height p)/(mu*(N:ℝ))⌋=F (height p) ∧
        field T (fun p => physicalHeight mu (height p)) (fun p => G (height p)) (mu*(N:ℝ))
          ⌊physicalHeight mu (height p)/(mu*(N:ℝ))⌋=G (height p) := by
  obtain ⟨T,hTS,hret,hsame⟩ := select_one_old_height S w height N hN
  exact ⟨T,hTS,hret,fun p hp =>
    ⟨frozen_eq_on_selected T height F mu hmu N hsame hp,
      frozen_eq_on_selected T height G mu hmu N hsame hp⟩⟩

end NativeExactHeightFields
