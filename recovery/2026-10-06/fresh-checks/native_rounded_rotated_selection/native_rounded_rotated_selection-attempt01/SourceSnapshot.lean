import Theorems.Thm_StickyKakeya4_native_rotated_cell_selection

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
noncomputable section

namespace NativeRoundedRotatedSelection
open Classical Finset StickyKakeya4 NativeMatrixHeightWholePoint
open NativeRotatedCellSelection
open scoped BigOperators

/-- The modulus is derived from the actual rounding-error constant.
It is not the exact-isometry modulus 5 unless that case is proved. -/
def roundingModulus (C : ℝ) : ℕ := 2*⌈2+2*C⌉₊+1

lemma roundingModulus_pos (C : ℝ) : 0 < roundingModulus C := by
  unfold roundingModulus
  omega

/-- This theorem REQUIRES the displayed physical rounding estimates.
It does not derive them from a symbolic label or from a grid alias. -/
theorem same_configured_cell_dist_le (O : E4 ≃ₗᵢ[ℝ] E4) (c : E4)
    {C delta rho : ℝ} (hC : 0 ≤ C) (hrho : 0 < rho) (hscale : delta ≤ rho)
    {x y u v : E4}
    (hx : dist u (O (x-c)) ≤ C*delta) (hy : dist v (O (y-c)) ≤ C*delta)
    (hcell : wzDyadicCellIndex rho u=wzDyadicCellIndex rho v) :
    dist x y ≤ (2+2*C)*rho := by
  have hcellDist := same_grid_dist_le hrho hcell
  have htri := dist_triangle4 (O (x-c)) u v (O (y-c))
  have herror : C*delta ≤ C*rho := mul_le_mul_of_nonneg_left hscale hC
  rw [LinearIsometryEquiv.dist_map,dist_sub_right] at htri
  rw [dist_comm (O (x-c)) u] at htri
  nlinarith only [htri,hx,hy,hcellDist,herror]

/-- Equal derived residue colors inside a configured rho-cell force exact
equality of the ORIGINAL rho-grid labels, despite bounded rounding error. -/
theorem same_color_same_original_cell (O : E4 ≃ₗᵢ[ℝ] E4) (c : E4)
    {C delta rho : ℝ} (hC : 0 ≤ C) (hrho : 0 < rho) (hscale : delta ≤ rho)
    {x y u v : E4}
    (hx : dist u (O (x-c)) ≤ C*delta) (hy : dist v (O (y-c)) ≤ C*delta)
    (hcell : wzDyadicCellIndex rho u=wzDyadicCellIndex rho v)
    (hcolor : SeparatedAlignmentPatches.color (roundingModulus C) (roundingModulus_pos C)
        (wzDyadicCellIndex rho x)=
      SeparatedAlignmentPatches.color (roundingModulus C) (roundingModulus_pos C)
        (wzDyadicCellIndex rho y)) :
    wzDyadicCellIndex rho x=wzDyadicCellIndex rho y := by
  have hd := same_configured_cell_dist_le O c hC hrho hscale hx hy hcell
  have hsup : dist (fun j : Fin 4 => x j) (fun j : Fin 4 => y j) ≤ (2+2*C)*rho := by
    apply (dist_pi_le_iff (by positivity)).mpr
    intro j
    exact (PiLp.dist_apply_le x y j).trans hd
  have hclose : dist (fun j : Fin 4 => x j) (fun j : Fin 4 => y j) < (3+2*C)*rho := by
    nlinarith only [hsup,hrho]
  have hgap : (3+2*C)*rho ≤ ((roundingModulus C:ℝ)-1)*rho := by
    apply mul_le_mul_of_nonneg_right _ hrho.le
    have hceil := Nat.le_ceil (2+2*C)
    dsimp only [roundingModulus]
    push_cast
    nlinarith only [hceil,hC]
  have hh := SeparatedAlignmentPatches.close_same_color_cell_eq rho ((3+2*C)*rho)
    hrho (roundingModulus C) (roundingModulus_pos C) hgap
    (fun j : Fin 4 => x j) (fun j : Fin 4 => y j) hcolor hclose
  exact hh

/-- Select by unchanged original label weights inside the ACTUAL configured
cells. The rounding estimate is the explicit geometric input of this module. -/
theorem select_one_configured_grid {A : Type*}
    (S : Finset A) (w : A → ℕ) (point configured : A → E4)
    (O : E4 ≃ₗᵢ[ℝ] E4) (c : E4) (C delta rho : ℝ)
    (hC : 0 ≤ C) (hdelta : 0 < delta) (hscale : delta ≤ rho)
    (hround : ∀x∈S,dist (configured x) (O (point x-c)) ≤ C*delta) :
    ∃T⊆S,mass S w ≤ (roundingModulus C)^4*mass T w ∧
      ∀x∈T,∀y∈T,wzDyadicCellIndex rho (configured x)=wzDyadicCellIndex rho (configured y) →
        wzDyadicCellIndex rho (point x)=wzDyadicCellIndex rho (point y) := by
  let M := roundingModulus C
  have hM : 0 < M := roundingModulus_pos C
  let : Nonempty (Fin 4 → Fin M) := ⟨fun _ => ⟨0,hM⟩⟩
  let paint := fun x => SeparatedAlignmentPatches.color M hM (wzDyadicCellIndex rho (point x))
  let label := fun x => wzDyadicCellIndex rho (configured x)
  obtain ⟨chi,hsub,_hlocal,hret,hcolor⟩ := select_color_per_cell S w label paint
  refine ⟨S.filter (fun x => paint x=chi (label x)),hsub,?_,?_⟩
  · simpa only [Fintype.card_fun,Fintype.card_fin] using hret
  · intro x hx y hy heq
    exact same_color_same_original_cell O c hC (hdelta.trans_le hscale) hscale
      (hround x (hsub hx)) (hround y (hsub hy)) heq (hcolor x hx y hy heq)

/-- Iteration on unchanged original weights. Every earlier configured-cell
implication survives later point subsets; no points or charts are moved. -/
theorem select_finite_menu {A I : Type*} [DecidableEq I]
    (menu : Finset I) (S : Finset A) (w : A → ℕ) (point : A → E4)
    (configured : I → A → E4) (O : I → E4 ≃ₗᵢ[ℝ] E4) (c : I → E4)
    (C delta : ℝ) (rho : I → ℝ) (hC : 0 ≤ C) (hdelta : 0 < delta)
    (hscale : ∀i,delta ≤ rho i)
    (hround : ∀i,∀x∈S,dist (configured i x) (O i (point x-c i)) ≤ C*delta) :
    ∃T⊆S,mass S w ≤ (roundingModulus C)^(4*menu.card)*mass T w ∧
      ∀i∈menu,∀x∈T,∀y∈T,
        wzDyadicCellIndex (rho i) (configured i x)=wzDyadicCellIndex (rho i) (configured i y) →
        wzDyadicCellIndex (rho i) (point x)=wzDyadicCellIndex (rho i) (point y) := by
  induction menu using Finset.induction_on generalizing S with
  | empty =>
      refine ⟨S,Subset.refl _,?_,?_⟩
      · simp
      · intro i hi
        simp at hi
  | @insert i menu hi ih =>
      obtain ⟨S1,hS1,hret1,hcell1⟩ := select_one_configured_grid S w point (configured i)
        (O i) (c i) C delta (rho i) hC hdelta (hscale i) (hround i)
      obtain ⟨T,hT,hret,hcell⟩ := ih S1 (fun j x hx => hround j x (hS1 hx))
      refine ⟨T,hT.trans hS1,?_,?_⟩
      · calc
          mass S w ≤ (roundingModulus C)^4*mass S1 w := hret1
          _ ≤ (roundingModulus C)^4*((roundingModulus C)^(4*menu.card)*mass T w) :=
            Nat.mul_le_mul_left _ hret
          _ = (roundingModulus C)^(4*(insert i menu).card)*mass T w := by
            rw [card_insert_of_notMem hi,←mul_assoc,←pow_add]
            congr 2
            omega
      · intro j hj x hx y hy heq
        rcases mem_insert.mp hj with rfl | hj
        · exact hcell1 x (hT hx) y (hT hy) heq
        · exact hcell j hj x hx y hy heq

/-- Whole original-edge lift. The actual recoded position is a map of the
original point label, so every surviving point retains its entire old fiber. -/
theorem select_original_edges {E P : Type*} [DecidableEq P]
    (K : ℕ) (A : Finset E) (point : E → P) (position : P → E4)
    (configured : Fin K → P → E4) (O : Fin K → E4 ≃ₗᵢ[ℝ] E4) (c : Fin K → E4)
    (C delta : ℝ) (rho : Fin K → ℝ) (hC : 0 ≤ C) (hdelta : 0 < delta)
    (hscale : ∀i,delta ≤ rho i)
    (hround : ∀i,∀p∈A.image point,dist (configured i p) (O i (position p-c i)) ≤ C*delta) :
    ∃B⊆A.image point,let T := edgeLift A point B
      T⊆A ∧ A.card ≤ (roundingModulus C)^(4*K)*T.card ∧
      (∀p∈B,T.filter (fun x => point x=p)=A.filter (fun x => point x=p)) ∧
      ∀i,∀x∈T,∀y∈T,
        wzDyadicCellIndex (rho i) (configured i (point x))=
          wzDyadicCellIndex (rho i) (configured i (point y)) →
        wzDyadicCellIndex (rho i) (position (point x))=
          wzDyadicCellIndex (rho i) (position (point y)) := by
  let w := fun p => (A.filter (fun x => point x=p)).card
  have hmass : mass (A.image point) w=A.card := (card_eq_sum_card_image point A).symm
  obtain ⟨B,hB,hret,hcell⟩ := select_finite_menu univ (A.image point) w position configured O c
    C delta rho hC hdelta hscale hround
  rw [hmass,←edgeLift_card A point B] at hret
  refine ⟨B,hB,filter_subset _ _,by simpa using hret,
    fun p hp => edgeLift_fiber A point B p hp,?_⟩
  intro i x hx y hy heq
  exact hcell i (mem_univ i) (point x) (mem_filter.mp hx).2 (point y) (mem_filter.mp hy).2 heq

/-- Transfer a proved old-cell pair predicate through bounded-error
configured cells on the same retained edge family. -/
theorem select_edges_inheriting_predicate {E P : Type*} [DecidableEq P]
    (K : ℕ) (A : Finset E) (point : E → P) (position : P → E4)
    (configured : Fin K → P → E4) (O : Fin K → E4 ≃ₗᵢ[ℝ] E4) (c : Fin K → E4)
    (C delta : ℝ) (rho : Fin K → ℝ) (hC : 0 ≤ C) (hdelta : 0 < delta)
    (hscale : ∀i,delta ≤ rho i)
    (hround : ∀i,∀p∈A.image point,dist (configured i p) (O i (position p-c i)) ≤ C*delta)
    (Pred : Fin K → E → E → Prop)
    (hOld : ∀i,∀x∈A,∀y∈A,
      wzDyadicCellIndex (rho i) (position (point x))=
        wzDyadicCellIndex (rho i) (position (point y)) → Pred i x y) :
    ∃B⊆A.image point,let T := edgeLift A point B
      T⊆A ∧ A.card ≤ (roundingModulus C)^(4*K)*T.card ∧
      (∀p∈B,T.filter (fun x => point x=p)=A.filter (fun x => point x=p)) ∧
      ∀i,∀x∈T,∀y∈T,
        wzDyadicCellIndex (rho i) (configured i (point x))=
          wzDyadicCellIndex (rho i) (configured i (point y)) →
        wzDyadicCellIndex (rho i) (position (point x))=
          wzDyadicCellIndex (rho i) (position (point y)) ∧ Pred i x y := by
  obtain ⟨B,hB,hTA,hret,hfiber,hcell⟩ := select_original_edges K A point position configured O c
    C delta rho hC hdelta hscale hround
  refine ⟨B,hB,hTA,hret,hfiber,?_⟩
  intro i x hx y hy heq
  have hh := hcell i x hx y hy heq
  exact ⟨hh,hOld i x (hTA hx) y (hTA hy) hh⟩

end NativeRoundedRotatedSelection
