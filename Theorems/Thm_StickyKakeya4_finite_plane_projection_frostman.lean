import Theorems.Thm_StickyKakeya4_finite_plane_projection_representatives
import Theorems.Thm_StickyKakeya4_projection_heavy_cells

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2500000

open Finset
open scoped BigOperators
noncomputable section
open Classical

namespace FinitePlaneProjectionGrid

/-- Collision energy at a larger geometric scale, from the original spatial cap. -/
theorem actual_KT1_collision_energy_at_scale {X : Type*} (P : Finset X) (p : X → Point3)
    (n J : ℕ) {rho K r : ℝ} (hmesh : mesh n ≤ rho) (hK : 0 ≤ K)
    (hr : rho ≤ r) (hJ : 2 ≤ 2 ^ (J + 1) * rho)
    (htop : ∀ i ∈ P, ∀ k ∈ P, dist3 (p i) (p k) ≤ 2)
    (hKT1 : ∀ i ∈ P, ∀ R : ℝ, rho ≤ R →
      ((P.filter (fun k => dist3 (p i) (p k) ≤ R)).card : ℝ) ≤ K * R / rho) :
    (∑ uv ∈ parameters n, ((labelCollisions P p uv r).card : ℝ)) ≤
      257 * K * r / rho * P.card * (parameters n).card := by
  have hrho := (mesh_pos n).trans_le hmesh
  have hrpos := hrho.trans_le hr
  have htopr : 2 ≤ 2 ^ (J + 1) * r :=
    hJ.trans (mul_le_mul_of_nonneg_left hr (by positivity))
  have hball : ∀ i ∈ P, ∀ R : ℝ, r ≤ R →
      ((P.filter (fun k => dist3 (p i) (p k) ≤ R)).card : ℝ) ≤
        (K * r / rho) * R / r := by
    intro i hi R hR
    have he : (K * r / rho) * R / r = K * R / rho := by field_simp
    rw [he]
    exact hKT1 i hi R (hr.trans hR)
  have hh := actual_KT1_collision_energy P p n J (hmesh.trans hr)
    (show 0 ≤ K * r / rho by positivity) htopr htop hball
  convert hh using 1
  ring

/-- A finite-scale energy that tests the actual projected original labels. -/
def scaleEnergy {X : Type*} (P : Finset X) (p : X → Point3)
    (scales : Finset ℝ) (uv : ℝ × ℝ) (rho : ℝ) : ℝ :=
  ∑ r ∈ scales, (rho / r) * (labelCollisions P p uv r).card

lemma scaleEnergy_nonneg {X : Type*} (P : Finset X) (p : X → Point3)
    (scales : Finset ℝ) (uv : ℝ × ℝ) {rho : ℝ} (hrho : 0 ≤ rho)
    (hscales : ∀ r ∈ scales, 0 ≤ r) : 0 ≤ scaleEnergy P p scales uv rho := by
  unfold scaleEnergy
  exact Finset.sum_nonneg (fun r hr => mul_nonneg (div_nonneg hrho (hscales r hr)) (by positivity))

/-- The energy budget is derived from spatial KT1 caps at every selected scale. -/
theorem scaleEnergy_budget {X : Type*} (P : Finset X) (p : X → Point3)
    (scales : Finset ℝ) (n J : ℕ) {rho K : ℝ} (hmesh : mesh n ≤ rho) (hK : 0 ≤ K)
    (hscales : ∀ r ∈ scales, rho ≤ r) (hJ : 2 ≤ 2 ^ (J + 1) * rho)
    (htop : ∀ i ∈ P, ∀ k ∈ P, dist3 (p i) (p k) ≤ 2)
    (hKT1 : ∀ i ∈ P, ∀ R : ℝ, rho ≤ R →
      ((P.filter (fun k => dist3 (p i) (p k) ≤ R)).card : ℝ) ≤ K * R / rho) :
    (∑ uv ∈ parameters n, scaleEnergy P p scales uv rho) ≤
      257 * K * scales.card * P.card * (parameters n).card := by
  have hrho := (mesh_pos n).trans_le hmesh
  unfold scaleEnergy
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ _r ∈ scales, 257 * K * P.card * (parameters n).card := by
      apply Finset.sum_le_sum
      intro r hr
      have hrpos := hrho.trans_le (hscales r hr)
      rw [← Finset.mul_sum]
      have hh := mul_le_mul_of_nonneg_left
        (actual_KT1_collision_energy_at_scale P p n J hmesh hK (hscales r hr) hJ htop hKT1)
        (show 0 ≤ rho / r by positivity)
      convert hh using 1
      field_simp
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring

/-- Labels lying in a projected cell whose original population exceeds the cap. -/
def heavyScale {X : Type*} (P : Finset X) (p : X → Point3)
    (uv : ℝ × ℝ) (rho D r : ℝ) : Finset X :=
  ProjectionHeavyCells.heavy P (fun i => projectedCell uv r (p i)) (D * r / rho)

def badScales {X : Type*} (P : Finset X) (p : X → Point3)
    (scales : Finset ℝ) (uv : ℝ × ℝ) (rho D : ℝ) : Finset X :=
  scales.biUnion (fun r => heavyScale P p uv rho D r)

def retainedScales {X : Type*} (P : Finset X) (p : X → Point3)
    (scales : Finset ℝ) (uv : ℝ × ℝ) (rho D : ℝ) : Finset X :=
  P \ badScales P p scales uv rho D

lemma heavyScale_subset {X : Type*} (P : Finset X) (p : X → Point3)
    (uv : ℝ × ℝ) (rho D r : ℝ) : heavyScale P p uv rho D r ⊆ P :=
  Finset.filter_subset _ _

lemma badScales_subset {X : Type*} (P : Finset X) (p : X → Point3)
    (scales : Finset ℝ) (uv : ℝ × ℝ) (rho D : ℝ) : badScales P p scales uv rho D ⊆ P := by
  intro i hi
  obtain ⟨r, _hr, hir⟩ := Finset.mem_biUnion.mp hi
  exact heavyScale_subset P p uv rho D r hir

lemma retainedScales_subset {X : Type*} (P : Finset X) (p : X → Point3)
    (scales : Finset ℝ) (uv : ℝ × ℝ) (rho D : ℝ) : retainedScales P p scales uv rho D ⊆ P :=
  Finset.sdiff_subset

lemma heavyScale_mass {X : Type*} (P : Finset X) (p : X → Point3)
    (uv : ℝ × ℝ) {rho D r : ℝ} (hrho : 0 < rho) (hr : 0 < r) :
    D * ((heavyScale P p uv rho D r).card : ℝ) ≤
      (rho / r) * (labelCollisions P p uv r).card := by
  let f := fun i => projectedCell uv r (p i)
  have hpoint : ∀ i ∈ heavyScale P p uv rho D r,
      D * r / rho ≤ ((P.filter (fun k =>
        |(project uv (p i)).1 - (project uv (p k)).1| ≤ r ∧
        |(project uv (p i)).2 - (project uv (p k)).2| ≤ r)).card : ℝ) := by
    intro i hi
    have hlarge := (Finset.mem_filter.mp hi).2
    have hsub : ProjectionHeavyCells.cell P f i ⊆ P.filter (fun k =>
        |(project uv (p i)).1 - (project uv (p k)).1| ≤ r ∧
        |(project uv (p i)).2 - (project uv (p k)).2| ≤ r) := by
      intro k hk
      obtain ⟨hkP, hcell⟩ := Finset.mem_filter.mp hk
      exact Finset.mem_filter.mpr ⟨hkP, same_projected_cell_close uv hr hcell.symm⟩
    exact hlarge.le.trans (Nat.cast_le.mpr (Finset.card_le_card hsub))
  have hmass : (D * r / rho) * ((heavyScale P p uv rho D r).card : ℝ) ≤
      (labelCollisions P p uv r).card := by
    calc
      _ = ∑ _i ∈ heavyScale P p uv rho D r, D * r / rho := by simp [mul_comm]
      _ ≤ ∑ i ∈ heavyScale P p uv rho D r,
          ((P.filter (fun k =>
            |(project uv (p i)).1 - (project uv (p k)).1| ≤ r ∧
            |(project uv (p i)).2 - (project uv (p k)).2| ≤ r)).card : ℝ) :=
        Finset.sum_le_sum hpoint
      _ ≤ ∑ i ∈ P, ((P.filter (fun k =>
            |(project uv (p i)).1 - (project uv (p k)).1| ≤ r ∧
            |(project uv (p i)).2 - (project uv (p k)).2| ≤ r)).card : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg (heavyScale_subset P p uv rho D r)
          (fun _ _ _ => Nat.cast_nonneg _)
      _ = _ := (ProjectionHeavyCells.card_far_pairs_eq_sum P _).symm
  have hh := mul_le_mul_of_nonneg_left hmass (show 0 ≤ rho / r by positivity)
  have he : rho / r * (D * r / rho * ((heavyScale P p uv rho D r).card : ℝ)) =
      D * (heavyScale P p uv rho D r).card := by
    field_simp
  rwa [he] at hh

lemma badScales_mass {X : Type*} (P : Finset X) (p : X → Point3)
    (scales : Finset ℝ) (uv : ℝ × ℝ) {rho D : ℝ} (hrho : 0 < rho) (hD : 0 ≤ D)
    (hscales : ∀ r ∈ scales, 0 < r) :
    D * ((badScales P p scales uv rho D).card : ℝ) ≤ scaleEnergy P p scales uv rho := by
  have hcard : ((badScales P p scales uv rho D).card : ℝ) ≤
      ∑ r ∈ scales, ((heavyScale P p uv rho D r).card : ℝ) := by
    exact_mod_cast Finset.card_biUnion_le (s := scales) (t := fun r => heavyScale P p uv rho D r)
  calc
    _ ≤ D * ∑ r ∈ scales, ((heavyScale P p uv rho D r).card : ℝ) :=
      mul_le_mul_of_nonneg_left hcard hD
    _ = ∑ r ∈ scales, D * ((heavyScale P p uv rho D r).card : ℝ) := Finset.mul_sum ..
    _ ≤ _ := Finset.sum_le_sum (fun r hr => heavyScale_mass P p uv hrho (hscales r hr))

lemma retainedScales_cell_bound {X : Type*} (P : Finset X) (p : X → Point3)
    (scales : Finset ℝ) (uv : ℝ × ℝ) (rho D : ℝ) {r : ℝ} (hr : r ∈ scales)
    {i : X} (hi : i ∈ retainedScales P p scales uv rho D) :
    ((P.filter (fun k => projectedCell uv r (p k) = projectedCell uv r (p i))).card : ℝ) ≤
      D * r / rho := by
  obtain ⟨hiP, hinot⟩ := Finset.mem_sdiff.mp hi
  by_contra h
  have hh : i ∈ heavyScale P p uv rho D r := Finset.mem_filter.mpr ⟨hiP, lt_of_not_ge h⟩
  exact hinot (Finset.mem_biUnion.mpr ⟨r, hr, hh⟩)

lemma retainedScales_half {X : Type*} (P : Finset X) (p : X → Point3)
    (scales : Finset ℝ) (uv : ℝ × ℝ) {rho D : ℝ} (hrho : 0 < rho) (hD : 0 < D)
    (hscales : ∀ r ∈ scales, 0 < r)
    (henergy : scaleEnergy P p scales uv rho ≤ D / 2 * P.card) :
    (P.card : ℝ) / 2 ≤ (retainedScales P p scales uv rho D).card := by
  have hbad := (badScales_mass P p scales uv hrho hD.le hscales).trans henergy
  have hcard : ((retainedScales P p scales uv rho D).card : ℝ) +
      (badScales P p scales uv rho D).card = P.card := by
    exact_mod_cast Finset.card_sdiff_add_card_eq_card (badScales_subset P p scales uv rho D)
  nlinarith

end FinitePlaneProjectionGrid
