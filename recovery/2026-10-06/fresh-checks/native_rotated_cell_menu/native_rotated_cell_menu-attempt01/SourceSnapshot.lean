import Theorems.Thm_StickyKakeya4_native_rotated_cell_selection
import Theorems.Thm_StickyKakeya4_native_matrix_height_budget

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
noncomputable section

namespace NativeRotatedCellMenu
open Classical Finset StickyKakeya4 NativeMatrixHeightWholePoint
open NativeRotatedCellSelection NativeMatrixHeightBudget NativeQuarterScaleParameters
open scoped BigOperators

/-- Every later selection preserves all earlier literal chart-cell
implications. The original natural weights are unchanged at every stage. -/
theorem select_finite_menu {A I : Type*} [DecidableEq I]
    (menu : Finset I) (S : Finset A) (w : A → ℕ) (point : A → E4)
    (O : I → E4 ≃ₗᵢ[ℝ] E4) (c : I → E4) (rho : I → ℝ)
    (hrho : ∀i,0 < rho i) :
    ∃T⊆S,mass S w ≤ 625^menu.card*mass T w ∧
      ∀i∈menu,∀x∈T,∀y∈T,
        rotatedCell (O i) (c i) (rho i) (point x)=rotatedCell (O i) (c i) (rho i) (point y) →
        wzDyadicCellIndex (rho i) (point x)=wzDyadicCellIndex (rho i) (point y) := by
  induction menu using Finset.induction_on generalizing S with
  | empty =>
      refine ⟨S,Subset.refl _,?_,?_⟩
      · simp
      · intro i hi
        simp at hi
  | @insert i menu hi ih =>
      obtain ⟨S1,hS1,hret1,hcell1⟩ := select_one_rotated_grid S w point (O i) (c i) (hrho i)
      obtain ⟨T,hT,hret,hcell⟩ := ih S1
      refine ⟨T,hT.trans hS1,?_,?_⟩
      · calc
          mass S w ≤ 625*mass S1 w := hret1
          _ ≤ 625*(625^menu.card*mass T w) := Nat.mul_le_mul_left _ hret
          _ = 625^(insert i menu).card*mass T w := by
            rw [card_insert_of_notMem hi,pow_succ]
            ring
      · intro j hj x hx y hy heq
        rcases mem_insert.mp hj with rfl | hj
        · exact hcell1 x (hT hx) y (hT hy) heq
        · exact hcell j hj x hx y hy heq

/-- K is fixed before the literal chart/mesh values. Each old and new cell
uses exactly the same uniform physical mesh rho_i in the supplied E4 frame. -/
theorem select_point_menu {A : Type*} (K : ℕ)
    (S : Finset A) (w : A → ℕ) (point : A → E4)
    (O : Fin K → E4 ≃ₗᵢ[ℝ] E4) (c : Fin K → E4) (rho : Fin K → ℝ)
    (hrho : ∀i,0 < rho i) :
    ∃T⊆S,mass S w ≤ 625^K*mass T w ∧
      ∀i,∀x∈T,∀y∈T,
        rotatedCell (O i) (c i) (rho i) (point x)=rotatedCell (O i) (c i) (rho i) (point y) →
        wzDyadicCellIndex (rho i) (point x)=wzDyadicCellIndex (rho i) (point y) := by
  obtain ⟨T,hT,hret,hcell⟩ := select_finite_menu univ S w point O c rho hrho
  exact ⟨T,hT,by simpa using hret,fun i => hcell i (mem_univ i)⟩

/-- Original-point fiber weights are computed from the actual old edges.
The final lift retains every original edge at each surviving point. -/
theorem select_original_edge_menu {E P : Type*} [DecidableEq P]
    (K : ℕ) (A : Finset E) (point : E → P) (position : P → E4)
    (O : Fin K → E4 ≃ₗᵢ[ℝ] E4) (c : Fin K → E4) (rho : Fin K → ℝ)
    (hrho : ∀i,0 < rho i) :
    ∃B⊆A.image point,let T := edgeLift A point B
      T⊆A ∧ A.card ≤ 625^K*T.card ∧
      (∀p∈B,T.filter (fun x => point x=p)=A.filter (fun x => point x=p)) ∧
      ∀i,∀x∈T,∀y∈T,
        rotatedCell (O i) (c i) (rho i) (position (point x))=
          rotatedCell (O i) (c i) (rho i) (position (point y)) →
        wzDyadicCellIndex (rho i) (position (point x))=
          wzDyadicCellIndex (rho i) (position (point y)) := by
  let w := fun p => (A.filter (fun x => point x=p)).card
  have hmass : mass (A.image point) w=A.card := (card_eq_sum_card_image point A).symm
  obtain ⟨B,hB,hret,hcell⟩ := select_point_menu K (A.image point) w position O c rho hrho
  rw [hmass,←edgeLift_card A point B] at hret
  refine ⟨B,hB,filter_subset _ _,hret,fun p hp => edgeLift_fiber A point B p hp,?_⟩
  intro i x hx y hy heq
  exact hcell i (point x) (mem_filter.mp hx).2 (point y) (mem_filter.mp hy).2 heq

/-- Any existing old-cell pair conclusion transfers to the SAME selected
new cells. No old coherence is inferred from proximity or from a grid alias. -/
theorem select_edges_inheriting_predicate {E P : Type*} [DecidableEq P]
    (K : ℕ) (A : Finset E) (point : E → P) (position : P → E4)
    (O : Fin K → E4 ≃ₗᵢ[ℝ] E4) (c : Fin K → E4) (rho : Fin K → ℝ)
    (hrho : ∀i,0 < rho i) (Pred : Fin K → E → E → Prop)
    (hOld : ∀i,∀x∈A,∀y∈A,
      wzDyadicCellIndex (rho i) (position (point x))=
        wzDyadicCellIndex (rho i) (position (point y)) → Pred i x y) :
    ∃B⊆A.image point,let T := edgeLift A point B
      T⊆A ∧ A.card ≤ 625^K*T.card ∧
      (∀p∈B,T.filter (fun x => point x=p)=A.filter (fun x => point x=p)) ∧
      ∀i,∀x∈T,∀y∈T,
        rotatedCell (O i) (c i) (rho i) (position (point x))=
          rotatedCell (O i) (c i) (rho i) (position (point y)) →
        wzDyadicCellIndex (rho i) (position (point x))=
          wzDyadicCellIndex (rho i) (position (point y)) ∧ Pred i x y := by
  obtain ⟨B,hB,hTA,hret,hfiber,hcell⟩ := select_original_edge_menu K A point position O c rho hrho
  refine ⟨B,hB,hTA,hret,hfiber,?_⟩
  intro i x hx y hy heq
  have hh := hcell i x hx y hy heq
  exact ⟨hh,hOld i x (hTA hx) y (hTA hy) hh⟩

/-- Both finite menu counts and the requested charge are fixed first.
The actual source radius, Lipschitz bound, and smaller epsilon come later.
This pays the product of the rotated-grid and matrix palette charges. -/
theorem exists_combined_palette_cutoff (Kmatrix Krot : ℕ) (e : ℝ) (he : 0 < e) :
    ∃epsilon0 r0 : ℝ,0 < epsilon0 ∧ epsilon0 ≤ e/(32*((Kmatrix:ℝ)+1)) ∧
      0 < r0 ∧ r0 ≤ 1 ∧
      ∀r L epsilon : ℝ,0 < r → r ≤ r0 → 0 ≤ L →
        0 ≤ epsilon → epsilon ≤ epsilon0 → L ≤ 3*r^(-2*epsilon) →
          (625:ℝ)^Krot*(9*(1+L)^2)^Kmatrix ≤ r^(-e) ∧
          ((625^Krot*(modulus L)^(2*Kmatrix):ℕ):ℝ) ≤ r^(-e) := by
  obtain ⟨epsilon0,rMatrix,hepsilon0,hepsilonBound,hrMatrix,hrMatrix1,Hmatrix⟩ :=
    exists_uniform_palette_cutoff Kmatrix (e/2) (by linarith only [he])
  have hC : (0:ℝ) < (625:ℝ)^Krot := by positivity
  obtain ⟨rRot,hrRot,hrRot1,Hrot⟩ := exists_small_power_cutoff
    (show 0 < e/2 by linarith only [he]) (show 0 < 1/(625:ℝ)^Krot by positivity)
  refine ⟨epsilon0,min rMatrix rRot,hepsilon0,?_,lt_min hrMatrix hrRot,
    (min_le_left _ _).trans hrMatrix1,?_⟩
  · convert hepsilonBound using 1 <;> ring
  · intro r L epsilon hr hsmall hL heps hepsBound hLip
    have hM := Hmatrix r L epsilon hr (hsmall.trans (min_le_left _ _)) hL heps hepsBound hLip
    have hsmallPower := Hrot r hr (hsmall.trans (min_le_right _ _))
    have hprod : (625:ℝ)^Krot*r^(e/2) ≤ 1 := by
      have hh := (le_div_iff₀ hC).mp hsmallPower
      simpa only [mul_comm] using hh
    have hR : (625:ℝ)^Krot ≤ r^(-(e/2)) := by
      rw [Real.rpow_neg hr.le,←one_div]
      exact (le_div_iff₀ (Real.rpow_pos_of_pos hr (e/2))).mpr hprod
    have hsplit : r^(-(e/2))*r^(-(e/2))=r^(-e) := by
      rw [←Real.rpow_add hr]
      congr 1
      ring
    have hpaid : (625:ℝ)^Krot*(9*(1+L)^2)^Kmatrix ≤ r^(-e) := by
      calc
        _ ≤ r^(-(e/2))*r^(-(e/2)) := mul_le_mul hR hM.1 (by positivity)
          (Real.rpow_nonneg hr.le _)
        _ = _ := hsplit
    refine ⟨hpaid,?_⟩
    calc
      ((625^Krot*(modulus L)^(2*Kmatrix):ℕ):ℝ) =
          (625:ℝ)^Krot*((modulus L)^(2*Kmatrix):ℝ) := by push_cast
      _ ≤ (625:ℝ)^Krot*(9*(1+L)^2)^Kmatrix :=
        mul_le_mul_of_nonneg_left (modulus_cost L hL Kmatrix) (by positivity)
      _ ≤ _ := hpaid

end NativeRotatedCellMenu
