import Theorems.Thm_StickyKakeya4_grid_quotient_ad
import Theorems.Thm_StickyKakeya4_native_finite_slice_union_ad

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 5000000

noncomputable section
namespace NativeLiteralGridOverlap
open Finset FiniteVoronoiPopulation

def center {l : ℕ} (rho : ℝ) (k : Fin l → ℤ) : Fin l → ℝ :=
  fun i => rho*((k i:ℝ)+1/2)

lemma floor_center {l : ℕ} {rho : ℝ} (hrho : 0 < rho) (k : Fin l → ℤ) :
    (fun i => ⌊center rho k i/rho⌋) = k := by
  funext i
  have heq : center rho k i/rho = (k i:ℝ)+1/2 := by
    dsimp [center]
    field_simp
  rw [heq]
  apply Int.floor_eq_iff.mpr
  constructor <;> linarith

lemma center_injective {l : ℕ} {rho : ℝ} (hrho : 0 < rho) :
    Function.Injective (center (l:=l) rho) := by
  intro k q h
  funext i
  have hi := congrFun h i
  dsimp [center] at hi
  have he := mul_left_cancel₀ hrho.ne' hi
  have hcast : (k i:ℝ) = q i := by linarith only [he]
  exact_mod_cast hcast

lemma close_centers_mem_box {l : ℕ} {rho : ℝ} (hrho : 0 < rho)
    (k q : Fin l → ℤ) (N : ℕ) (hclose : dist (center rho k) (center rho q) ≤ (N:ℝ)*rho) :
    k∈GridQuotientAD.box q N := by
  apply (GridQuotientAD.mem_box_iff q k N).mpr
  intro i
  have hi : |center rho k i-center rho q i| ≤ (N:ℝ)*rho := by
    simpa only [Real.dist_eq] using (dist_le_pi_dist (center rho k) (center rho q) i).trans hclose
  have heq : |center rho k i-center rho q i| = rho*|((k i-q i:ℤ):ℝ)| := by
    have hd : center rho k i-center rho q i = rho*((k i-q i:ℤ):ℝ) := by
      dsimp [center]
      push_cast
      ring
    rw [hd,abs_mul,abs_of_pos hrho]
  rw [heq] at hi
  have hir : |((k i-q i:ℤ):ℝ)| ≤ (N:ℝ) :=
    (mul_le_mul_iff_right₀ hrho).mp (by simpa only [mul_comm] using hi)
  exact_mod_cast hir

/-- Literal grid packing around an arbitrary real center. The proof uses
only integer labels and the exact cubical-center displacement. -/
theorem grid_ball_card_le {l : ℕ} (B : Finset (Fin l → ℤ)) {rho : ℝ}
    (hrho : 0 < rho) (x : Fin l → ℝ) (N : ℕ) :
    (B.filter (fun k => dist (center rho k) x ≤ (N:ℝ)*rho)).card ≤ (4*N+1)^l := by
  classical
  let S := B.filter (fun k => dist (center rho k) x ≤ (N:ℝ)*rho)
  change S.card ≤ (4*N+1)^l
  by_cases hS : S.Nonempty
  · obtain ⟨q,hq⟩ := hS
    have hqx := (Finset.mem_filter.mp hq).2
    have hxq : dist x (center rho q) ≤ (N:ℝ)*rho := by simpa only [dist_comm] using hqx
    have hsub : S ⊆ GridQuotientAD.box q (2*N) := by
      intro k hk
      have hkx := (Finset.mem_filter.mp hk).2
      apply close_centers_mem_box hrho k q (2*N)
      have ht := dist_triangle (center rho k) x (center rho q)
      push_cast
      linarith only [ht,hkx,hxq]
    calc
      S.card ≤ (GridQuotientAD.box q (2*N)).card := Finset.card_le_card hsub
      _ = (4*N+1)^l := by rw [GridQuotientAD.box_card]; congr 1; omega
  · have he : S=∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    rw [he,Finset.card_empty]
    exact Nat.zero_le _

lemma realized_ball_card {l : ℕ} (B : Finset (Fin l → ℤ)) {rho : ℝ}
    (hrho : 0 < rho) (x : Fin l → ℝ) (r : ℝ) :
    (carrierBall (B.image (center rho)) x r).card =
      (B.filter (fun k => dist (center rho k) x ≤ r)).card := by
  classical
  have heq : (B.filter (fun k => dist (center rho k) x ≤ r)).image (center rho) =
      carrierBall (B.image (center rho)) x r := by
    ext y
    simp only [Finset.mem_image,Finset.mem_filter,mem_carrierBall]
    constructor
    · rintro ⟨k,⟨hk,hd⟩,rfl⟩
      exact ⟨⟨k,hk,rfl⟩,hd⟩
    · rintro ⟨⟨k,hk,rfl⟩,hd⟩
      exact ⟨k,⟨hk,hd⟩,rfl⟩
  rw [←heq,Finset.card_image_of_injective _ (center_injective hrho)]

end NativeLiteralGridOverlap
